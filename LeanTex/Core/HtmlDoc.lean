import LeanTex.Core.Html
import LeanTex.Core.HtmlResource
import LeanTex.Core.MathMl
import LeanTex.Core.Ir
import LeanTex.Core.Dim
import LeanTex.Core.Contrast
import LeanTex.Core.Font
import Std.Http.Data.URI.Encoding

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
  /-- The document's resolved main locale, set from the document at
  `emitTree`'s entry: what the backend's generated furniture (the
  abstract heading, caption prefixes) is worded in. -/
  locale : Locale := Locale.en
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
  /-- The palette in force at this point of the block walk — the epoch
  state a body `\palette` snapshot is diffed against. Epoch 0 is the
  document's preamble+theme palette (`emitTree` seeds it); each
  `.setPalette` replaces it as the walk passes the block. -/
  pal : Ir.Palette := {}
  /-- A listing's local frame colours. Its code panel states the same ground
  that PDF paints, so default syntax inks have one contrast contract on
  screen and paper, including standout and title-page frames. -/
  listingGround : Option Ir.Color := none
  listingFg : Option Ir.Color := none
  /-- The token state in force, same door (`.setTokens`). -/
  tokens : Ir.Tokens := {}
  /-- Whether the emitted page is the paged deck (the slides class's frame
  model): the frame arm then realizes its declared vertical distribution
  with flex spacers, which every other class's flow has no use for. -/
  deck : Bool := false
  /-- The frame's numbered extent, used to project union selectors into
  finite HTML attribute tokens. It is read from the IR, never the surface. -/
  overlaySteps : Nat := 1
  /-- The document's page geometry, from the document at `emitTree`'s
  entry: the deck's image sizing reads the stage and its margins to state
  every dimension as a share of the stage (`deckStageMilli`), never a
  print length on a screen. -/
  page : Ir.PageSpec := {}
  /-- The resolved local measurement context. A box replaces the horizontal
  measures while retaining the page's text height; outside a box, `none`
  reads the document's text area. Providers share the native vocabulary. -/
  measures : Option MeasureValues := none
  /-- The accumulated custom-property redefinitions the siblings from here
  on carry on their own style attribute. Properties on an element inherit
  into it, so styling each following sibling realizes "from here on"
  without a wrapper element — a wrapper would break the `* + *` sibling
  adjacency the rhythm gap rules key on. -/
  epochStyle : String := ""
  /-- Whether that accumulated palette diff changes the rendered page ground.
  Kept as data: no CSS substring is used to infer a semantic epoch. -/
  epochGround : Bool := false
  /-- The document's resolved faces, from the driver — the same `FontSet`
  the PDF embeds from — when the artifact ships them: one `@font-face` per
  face, carrying its captured font program as a data URL. `none` (a document that declared
  its `css =` story owns fonts itself, and so does a caller with no font
  environment) keeps the name-only stacks. -/
  fonts : Option Font.FontSet := none
  /-- Compatibility field for callers staging older directory-based pages.
  Embedded font URLs do not read it. -/
  fontsDir : String := "fonts"
  /-- Compatibility field for older staging callers. Embedded image URLs
  do not read it. -/
  assetsDir : String := "assets"
  /-- Exact declared stylesheet spelling and captured text. A missing or
  mismatched capture remains a link, which checked publication refuses. -/
  stylesheet : Option (String × String) := none
  /-- Captured icon bytes, keyed by the document's exact favicon spelling. -/
  favicon : Option (String × HtmlResource.Embedded) := none
  /-- Inside a declared title slot: the slot's font template already wraps
  what it sets, so the title heading there takes no `titlepage` template
  of its own — the PDF's `slotTitle` reading, the same one value. -/
  slotTitle : Bool := false
  /-- How a picture label's content measures, from the driver: the same
  function layout places labels with (`Layout.labelMetric` over the one
  `FontSet`), so a picture's `viewBox` is the box the PDF reserves
  (`Pdf.picture_box_agree`). The default answers nothing — a caller with no
  font environment sizes a picture by its declared box and node borders. -/
  labelMetric : Ir.Pic.LabelMetric := fun _ _ => {}
  /-- Measured cancellation in the resolved surrounding text style, supplied
  by the same font environment and assembly as the native backend. -/
  cancelMetric : MeasureValues → Array Ir.Style → Math.MathStyle → Math.CancelSpec →
    Math.MList → Math.MList → Option Math.CancelMetric := fun _ _ _ _ _ _ => none
  /-- The same run's font unit for explicitly sized math lengths. -/
  mathEm : MeasureValues → Array Ir.Style → Math.MathStyle → Option Int := fun _ _ _ => none
  /-- Text-sourced math alphabets keep the ambient text em, before the math
  face's x-height matching. Read only at a styled math leaf. -/
  mathTextEm : MeasureValues → Array Ir.Style → Math.MathStyle → Option Int := fun _ _ _ => none
  /-- The native resolver folds this ordered history; the HTML walk carries
  declarations without implementing another font or size interpreter. -/
  mathStyles : Array Ir.Style := #[]
  /-- Inside a fill row's group (`fillRow`): a fraction of the text width is
  a fraction of the row, the line the fill spans, as in TeX — never of the
  group, whose width that same fraction decides. The image emission states
  it in `cqi` against the row, which then declares itself the container. -/
  inFillRow : Bool := false

/-- The current physical text area, before relative lengths resolve.
An explicit local context wins over the page's ordinary text area. -/
def Config.measureValues (cfg : Config) : MeasureValues :=
  cfg.measures.getD (MeasureValues.horizontal
    (cfg.page.width - 2 * cfg.page.hmargin) (cfg.page.height - 2 * cfg.page.vmargin))

/-- Enter a box with the same horizontal-measure convention as native
paragraphs. Descendant widths resolve against it; siblings keep their own
context because only the child's configuration changes. -/
def Config.atMeasure (cfg : Config) (width : Sp) : Config :=
  { cfg with measures := some (MeasureValues.horizontal width cfg.measureValues.textHeight) }

def cssColor (c : Color) : String := c.css

/-- What a formula's cancel marks read from the math face, in thousandths
of an em — its overbar rule and clearance, the two quantities the PDF lays
the marks with — when the page ships its faces; TeX's own stand-ins
(`MathMl.Marks`' defaults) where it does not. -/
def mathMarks (cfg : Config) : MathMl.Marks :=
  let marks : MathMl.Marks := {
    metric := cfg.cancelMetric cfg.measureValues cfg.mathStyles
    em := cfg.mathEm cfg.measureValues cfg.mathStyles
    textEm := cfg.mathTextEm cfg.measureValues cfg.mathStyles }
  match cfg.fonts.bind fun fs => fs.math.bind (fs.fonts[·]?) with
  | some f =>
    match f.math with
    | some mc =>
      let per (v : Int) : Nat := (v * 1000 / (max 1 f.unitsPerEm : Int)).toNat
      { marks with rule := per mc.overbarRuleThickness, gap := per mc.overbarVerticalGap
                   scales := mc.scales }
    | none => marks
  | none => marks

/-- The class an authored role wears in the artifact: verbatim after a
fixed prefix, so the mapping is injective (`roleClass_inj`) and lands in a
namespace no engine class enters (`roleClass_engine_disjoint`) and no
framework convention plausibly claims (Bulma's `.title` vs `u-title`). A
class, not a custom element: WHATWG HTML §3.2.6 places no constraint on
class values and encourages nature-of-content names, while a custom
element (§4.13.1) exists to define behaviour and would swap the `<span>`
for an unknown element — the wrong tool for a styling hook. -/
def roleClass (n : String) : String := "u-" ++ n

theorem roleClass_toList (n : String) :
    (roleClass n).toList = 'u' :: '-' :: n.toList := by
  have h : "u-".toList = ['u', '-'] := by decide
  simp [roleClass, String.toList_append, h]

/-- Two authored names never share a class, so no collision diagnostic can
fire and none is warranted — the theorem replaces it. -/
theorem roleClass_inj (a b : String) (h : roleClass a = roleClass b) : a = b := by
  have hl := congrArg String.toList h
  rw [roleClass_toList, roleClass_toList] at hl
  simp only [List.cons.injEq, true_and] at hl
  exact String.ext hl

/-- The class a ragged scope carries, one per declared side. Two names
rather than one class plus an inline style, because the side is a
*declaration* and belongs where a reader's own sheet can address it; the
rule text is built from `Ir.FlushSide.align` at the one site below
(`raggedRule`), so the class and the alignment it declares cannot drift. -/
def raggedClass : Ir.FlushSide → String
  | .left => "ragged"
  | .right => "ragged-right"

/-- The margins a block-level box — a table — takes on its scope's side:
`auto` exactly where the page leaves the box slack
(`box_margins_agree`), so HTML sets a tabular or a lone minipage where the
PDF does (`Ir.HAlign.boxOffset`). -/
def boxMargins : Ir.HAlign → String × String
  | .left => ("0", "auto")
  | .center => ("auto", "auto")
  | .right => ("auto", "0")

/-- The track placement a lone box's grid row takes on its scope's side. -/
def boxJustify : Ir.HAlign → String
  | .left => "start"
  | .center => "center"
  | .right => "end"

/-- The two readings of a scope's side agree: the stylesheet leaves slack
before a box exactly when the page's offset takes some, and after it
exactly when the offset leaves some. -/
theorem box_margins_agree (h : Ir.HAlign) :
    ((boxMargins h).1 = "auto" ↔ 0 < h.slackHalves) ∧
      ((boxMargins h).2 = "auto" ↔ h.slackHalves < 2) := by
  cases h <;> decide

/-- An alignment scope's rule: its class, the side's `text-align`, and the
side's box placement as inherited properties — inherited exactly as
`text-align` is, so a table or a lone minipage anywhere in the scope stands
on its side, as TeX sets a box in a line wherever the scope's skips are in
force. -/
def alignScopeRule (cls : String) (h : Ir.HAlign) : String :=
  "." ++ cls ++ " { text-align: " ++ h.align ++ "; --ltx-box-left: " ++ (boxMargins h).1 ++
    "; --ltx-box-right: " ++ (boxMargins h).2 ++ "; --ltx-box-justify: " ++ boxJustify h ++
    "; }\n"

/-- One ragged side's stylesheet rule: its class, and the alignment the IR
declares for it. Both halves come from the IR, so the sheet cannot declare
an edge the page does not set (`ragged_sides_agree` ties the alignment this
prints to the origin the page's walk reads). -/
def raggedRule (s : Ir.FlushSide) : String := alignScopeRule (raggedClass s) s.halign

/-- The rule is the class and the IR's own alignment, nothing invented
between them: the projection corollary of `ragged_sides_agree` on this
backend's side. -/
theorem raggedRule_projects (s : Ir.FlushSide) :
    raggedRule s = alignScopeRule (raggedClass s) s.halign ∧ s.halign.align = s.align := by
  cases s <;> exact ⟨rfl, rfl⟩

/-- Every class value the engine itself puts on an element, as tokens (a
multi-class value like `"slide standout"` is listed split). Maintained by
grep over this file — `("class", "…")` literals, the `rowClass`/`cls`
builders, `styleClass`, and the `size-` names `styleClass` derives from
`Ir.sizeScale`; `roleClass_engine_disjoint` is the reason the list exists. -/
def engineClasses : List String :=
  ["abstract", "b", "i", "mono", "sc", "em", "sans", "normal", "rm", "md", "up",
   "section-number", "display", "equation", "eqnum",
   "band-left", "band-right", "booktabs", "bt-cmid", "bt-heavy-above",
   "bt-light-above", "bt-nowrap", "cell-measure", "centered", "ragged", "ragged-right", "column", "columns", "content",
   "deck-progress", "entry",
   "entry-pair", "entry-row", "entry-rows", "fill", "float", "group", "icon",
   "math", "math-display", "nopadl", "nopadr", "note", "picture", "progress",
   "reveal-scroll", "ruled", "section-page", "separator", "slide",
   "slide-foot", "slide-logo", "slide-track", "slides", "snap", "spaced",
   "standout", "step", "table-float"] ++
  Ir.sizeScale.map (fun p => "size-" ++ p.1)

private theorem engineClasses_no_u_prefix :
    (engineClasses.all fun c => decide (c.toList.take 2 ≠ ['u', '-'])) = true := by
  decide

/-- The `u-` prefix makes role classes disjoint from every class the engine
emits: an authored role can restyle itself without ever colliding with the
engine's own hooks, and a stylesheet addressing `.u-…` addresses only
authored roles. -/
theorem roleClass_engine_disjoint (n c : String) (hc : c ∈ engineClasses) :
    roleClass n ≠ c := by
  intro h
  have hall := List.all_eq_true.mp engineClasses_no_u_prefix c hc
  simp only [decide_eq_true_eq] at hall
  apply hall
  rw [← h, roleClass_toList]
  rfl

/-- Over the command-name alphabet — the lexer admits only `isAlpha` and
`'@'` into a control word, so no other character can reach `roleClass`
from a document — the class is one HTML class token: no whitespace (HTML
treats a class value as a space-separated set, so a space would split the
class into two tokens, a break the escaper cannot see) and no quote (the
attribute-breakout character `escapeAttr` kills). The alphabet is spelled
inline because a backend never reaches into the lexer; Tests.lean pins the
spelling to the lexer's own `nameChar` by `rfl`. -/
theorem roleClass_single_token (n : String)
    (hn : (n.toList.all fun c => c.isAlpha || c == '@') = true) :
    ((roleClass n).toList.all fun c =>
      !(c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '"' || c == '\'')) = true := by
  rw [roleClass_toList]
  simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hn ⊢
  refine ⟨by decide, by decide, fun c hc => ?_⟩
  have h := hn c hc
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨⟨fun h' => ?_, fun h' => ?_⟩, fun h' => ?_⟩, fun h' => ?_⟩,
    fun h' => ?_⟩, fun h' => ?_⟩ <;> (subst h'; exact absurd h (by decide))

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

/-- A sourced length in CSS: the custom property the value was declared
under, with the resolved length as its fallback. This is the whole reason
`Ir.Sourced` exists — `tokenVars` emits every declared token into `:root`
so a reader's stylesheet can override it, and an override only reaches the
page through a rule that names the property. A value with no declaration
behind it has nothing to defer to and prints as the length, which is also
what a rule wants for an engine rhythm quantum: a reader cannot override
what the engine did not declare.

The fallback is not redundant belt-and-braces. A token declared by a
theme's bundle but absent from the document's own table is not in `:root`,
and an unresolved `var()` with no fallback makes the whole declaration
invalid — the gap would collapse to zero. -/
def cssSourced (g : Ir.Sourced SymGlue) : String :=
  match g.token with
  | some n => s!"var(--{n}, {cssLength g.value.width})"
  | none => cssLength g.value.width

/-- A declared token reaches the stylesheet as a reference to its own
custom property, in exactly the form the closure check measures, and its
resolved length rides along as the fallback. The artifact-level half of
`Ir.findSourced?_names`: the name the lookup kept is the name the rule
defers to, so a reader's override lands. -/
theorem cssSourced_projects (g : Ir.Sourced SymGlue) (n : String)
    (h : g.token = some n) :
    cssSourced g = s!"var(--{n}, {cssLength g.value.width})" := by
  simp [cssSourced, h]

/-- The complement: a value no declaration named prints as the bare length,
so nothing references a property the engine never emitted. -/
theorem cssSourced_bare (g : SymGlue) :
    cssSourced (Ir.Sourced.bare g) = cssLength g.width := by
  simp [cssSourced, Ir.Sourced.bare]

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

/-- The reduced-motion guard for the reveal: under the reader's reduce
preference the element simply stands, fully visible (WCAG 2.2 SC 2.3.3,
technique C39; CSS Media Queries 5 §12.1). As `motionCss`, the guard
travels with the declaration itself — a `css = none` page ships only the
declared rules, so no global block can be relied on to cover it. -/
def revealMotionGuard : String :=
  "@media (prefers-reduced-motion: reduce) \
{ .reveal-scroll { animation: none; } }\n"

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
animation-range: 0 var(--reveal-range, 100vh); } }\n" ++
  revealMotionGuard

/-- The reveal carries its reduced-motion form by construction:
definitionally the keyframes and trigger followed by the guard —
`motionCss_guarded`'s shape for the one page-level animation site. -/
theorem revealCss_guarded : ∃ rule, revealCss = rule ++ revealMotionGuard :=
  ⟨_, rfl⟩


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

/-- Font declarations shared by markers and listings (CSS Pseudo-Elements 4
§4.1 permits all font properties on `::marker`). The bold weight is
600, the same weight the base stylesheet's level-2 dash carries. An unknown
size name resolves to nothing, which makes the whole marker inexpressible
rather than silently unsized. A listing supplies its frame's length
projection, the same one inline fonts use. -/
private def fontStyleDecls (scale : List (String × Nat)) (st : Style)
    (lengthCss : Affine Measure → String := Ir.Track.contextCss) :
    Option (Array String) :=
  match st with
  | .bold => some #["font-weight: 600;"]
  | .italic => some #["font-style: italic;"]
  | .emph => some #["font-style: italic;"]
  | .mono => some #["font-family: var(--font-mono);"]
  | .sans => some #["font-family: var(--font-sans);"]
  | .smallcaps => some #["font-variant-caps: all-small-caps;"]
  | .roman => some #["font-family: var(--font-body);"]
  | .medium => some #["font-weight: 400;"]
  | .series w => some #[s!"font-weight: {w.css};"]
  | .upright => some #["font-style: normal;", "font-variant-caps: normal;"]
  | .normal => some #[]
  | .size name => (scale.lookup name).map fun k =>
      #[s!"font-size: {decMilli k}em;"]
  | .fontSize size leading => some #[
      s!"font-size: {lengthCss size};",
      s!"line-height: {lengthCss leading};"]
  -- a language changes no marker styling; the wrapper is expressible as
  -- nothing rather than inexpressible
  | .lang _ => some #[]

private def markerColorDecl (c : Ir.Color) (name : Option String) : String :=
  match name with
  | some n => s!"color: var(--{n}, {cssColor c});"
  | none => s!"color: {cssColor c};"

mutual

/-- The plain text of a marker whose every element is text — anything else
is not `::marker` content. Diagnostic locations only group those elements.
This reader stops at a semantic wrapper, unlike the generic text census.
Explicit arms: a new `Inline` constructor must answer here. -/
private def markerTextOne (acc : String) : Inline → Option String
  | .text s => some (acc ++ s)
  | .math _ _ => none
  | .formula _ _ _ => none
  | .styled _ _ => none
  | .colored _ _ _ => none
  | .located _ body => markerTextInto acc body.toList
  | .role _ _ => none
  | .link _ _ => none
  | .decorated _ _ => none
  | .fill => none
  | .hspace _ _ => none
  | .rule _ _ _ => none
  | .strut _ => none
  -- a text command's italic correction is a kern: no ::marker content
  | .italicCorr _ => some acc
  | .pageNumber => none
  | .pageCount => none
  | .linebreak _ => none
  | .onSteps _ _ => none
  | .altSteps _ _ _ => none
  | .image _ _ _ => none
  -- a `content` string cannot carry the icon's accessible name, so an icon
  -- marker is inexpressible here and diagnosed (W0331), never defaulted
  | .icon _ _ => none
  -- an anchor or a reference in a marker has no ::marker expression
  | .label _ => none
  | .ref _ _ _ _ => none
  -- a citation resolves to links, which no ::marker can carry
  | .cite _ _ => none
  -- a footnote's mark is a link, which no ::marker can carry
  | .footnote _ _ => none

private def markerTextInto (acc : String) : List Inline → Option String
  | [] => some acc
  | x :: rest =>
    (markerTextOne acc x).bind fun next => markerTextInto next rest

end

mutual

/-- Resolve one marker element for `::marker`: a whole-content style wrapper
— it must wrap everything inside it, since one `::marker` rule styles the
whole marker — or plain text. `none` is the inexpressible remainder, which
the emitter must diagnose, never silently default (`styleRules`): the same
declaration then reaches both backends or the difference has a name.
Explicit arms (the obligation table; no wildcard in a backend's IR walk). -/
def markerCssOne (scale : List (String × Nat)) (decls : Array String) :
    Inline → Option MarkerCss
  | .text s => some { text := s, decls := decls }
  | .styled st body =>
    match fontStyleDecls scale st with
    | some ds => markerCssList scale (decls ++ ds) body.toList
    | _ => none
  | .colored c name body =>
    markerCssList scale (decls.push (markerColorDecl c name)) body.toList
  | .located _ body => markerCssList scale decls body.toList
  -- a role's class has no ::marker expression; the content passes through,
  -- as it does on the PDF marker path
  | .role _ body => markerCssList scale decls body.toList
  | .math _ _ => none
  | .formula _ _ _ => none
  | .link _ _ => none
  | .decorated _ _ => none
  | .fill => none
  | .hspace _ _ => none
  | .rule _ _ _ => none
  | .strut _ => none
  | .italicCorr _ => none
  | .pageNumber => none
  | .pageCount => none
  | .linebreak _ => none
  | .onSteps _ _ => none
  | .altSteps _ _ _ => none
  | .image _ _ _ => none
  | .icon _ _ => none
  | .label _ => none
  | .ref _ _ _ _ => none
  | .cite _ _ => none
  | .footnote _ _ => none

private def markerCorr : Inline → Bool
  | .italicCorr _ => true
  | _ => false

def markerCssList (scale : List (String × Nat)) (decls : Array String) :
    List Inline → Option MarkerCss
  | [] => some { text := "", decls := decls }
  | x :: rest =>
    if markerCorr x then markerCssList scale decls rest
    else if rest.all markerCorr then markerCssOne scale decls x
    else (markerTextInto "" (x :: rest)).map fun t => { text := t, decls := decls }

end

def markerCss? (m : Array Inline)
    (scale : List (String × Nat) := Ir.sizeScale) : Option MarkerCss :=
  -- Wrapper boundaries cannot change whether a style covers the whole
  -- marker, or turn several text leaves into an inexpressible mixture.
  markerCssList scale #[] (Ir.eraseLocationInlines m).toList

mutual

private theorem markerTextOne_text (x : Inline) (acc t : String)
    (h : markerTextOne acc x = some t) : t = acc ++ Ir.plainTextOne x := by
  match x with
  | .text _ | .italicCorr _ =>
    simp [markerTextOne] at h
    simp [← h, Ir.plainTextOne]
  | .located _ body => exact markerTextInto_text body.toList acc t h
  | .math _ _ | .formula _ _ _ | .styled _ _
  | .colored _ _ _ | .role _ _ | .link _ _
  | .decorated _ _ | .fill | .hspace _ _ | .rule _ _ _
  | .strut _ | .pageNumber | .pageCount | .linebreak _
  | .onSteps _ _ | .altSteps _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .footnote _ _ =>
    simp [markerTextOne] at h

private theorem markerTextInto_text (xs : List Inline) (acc t : String)
    (h : markerTextInto acc xs = some t) : t = acc ++ Ir.plainTextList xs := by
  match xs with
  | [] =>
    simp [markerTextInto] at h
    simp [← h, Ir.plainTextList]
  | x :: rest =>
    simp only [markerTextInto, Option.bind_eq_some_iff] at h
    obtain ⟨next, hb, hr⟩ := h
    rw [markerTextInto_text rest next t hr, markerTextOne_text x acc next hb]
    simp [Ir.plainTextList, String.append_assoc]

end

private theorem markerCorrOne_text (x : Inline) (h : markerCorr x = true) :
    Ir.plainTextOne x = "" := by
  cases x <;> simp [markerCorr, Ir.plainTextOne] at h ⊢

private theorem markerCorr_text (xs : List Inline)
    (h : ∀ x ∈ xs, markerCorr x = true) : Ir.plainTextList xs = "" := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : markerCorr x = true := h x (by simp)
    have hxs : ∀ y ∈ xs, markerCorr y = true := by
      intro y hy
      exact h y (by simp [hy])
    simp [Ir.plainTextList, markerCorrOne_text x hx, ih hxs]

mutual

/-- A marker `::marker` can express shows exactly the declared characters:
the emitted `content` is the marker's own plain text, so the HTML marker and
the PDF marker (which sets the same declared content as a line of its own)
can only differ where a diagnostic already names the substitution. -/
theorem markerCssOne_text (scale : List (String × Nat)) (decls : Array String)
    (x : Inline) (r : MarkerCss)
    (h : markerCssOne scale decls x = some r) : r.text = Ir.plainTextOne x := by
  match x with
  | .text s =>
    simp [markerCssOne] at h
    simp [← h, Ir.plainTextOne]
  | .styled st body =>
    rw [markerCssOne] at h
    split at h
    · rw [Ir.plainTextOne]
      exact markerCssList_text scale _ body.toList r h
    · exact absurd h (by simp)
  | .colored c name body =>
    rw [markerCssOne] at h
    rw [Ir.plainTextOne]
    exact markerCssList_text scale _ body.toList r h
  | .role n body =>
    rw [markerCssOne] at h
    rw [Ir.plainTextOne]
    exact markerCssList_text scale _ body.toList r h
  | .located _ body =>
    rw [markerCssOne] at h
    rw [Ir.plainTextOne]
    exact markerCssList_text scale _ body.toList r h
  | .math _ _ | .formula _ _ _ | .link _ _ | .decorated _ _ | .fill
  | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount
  | .linebreak _ | .onSteps _ _ | .image _ _ _ | .icon _ _ | .label _ | .ref _ _ _ _
  | .cite _ _ | .footnote _ _ =>
    simp [markerCssOne] at h
  | .altSteps _ _ _ => simp [markerCssOne] at h

theorem markerCssList_text (scale : List (String × Nat)) (decls : Array String)
    (xs : List Inline)
    (r : MarkerCss) (h : markerCssList scale decls xs = some r) :
    r.text = Ir.plainTextList xs := by
  match xs with
  | [] =>
    simp [markerCssList] at h
    simp [← h, Ir.plainTextList]
  | x :: rest =>
    rw [markerCssList] at h
    split at h
    · rename_i hx
      rw [markerCssList_text scale decls rest r h]
      simp [Ir.plainTextList, markerCorrOne_text x hx]
    · split at h
      · rename_i hc
        have hrest : ∀ y ∈ rest, markerCorr y = true := by
          simpa only [List.all_eq_true] using hc
        rw [markerCssOne_text scale decls x r h]
        simp [Ir.plainTextList, markerCorr_text rest hrest]
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨t, ht, hr⟩ := h
        rw [← hr]
        simpa using markerTextInto_text (x :: rest) "" t ht

end

theorem markerCss?_text (m : Array Inline) (r : MarkerCss)
    (scale : List (String × Nat) := Ir.sizeScale)
    (h : markerCss? m scale = some r) : r.text = Ir.plainText m := by
  calc
    r.text = Ir.plainText (Ir.eraseLocationInlines m) :=
      markerCssList_text scale #[] (Ir.eraseLocationInlines m).toList r h
    _ = Ir.plainText m := Ir.eraseLocationInlines_text m

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
    -- A defined role: its style addresses the class hook the role already
    -- ships (`roleClass`, injective), so a declared rhythm or state lands
    -- on `.u-<name>` — the same selector a framework stylesheet uses. The
    -- remaining engine elements (the slides furniture) have no selector
    -- here and stay skipped, as before.
    | e => if Ir.styleableElements.contains e then none else some ("." ++ roleClass e)
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
    -- The title heading takes what the page's title door reads, nothing more.
    let st := if element == "titlepage" then Ir.titleHeadingStyle st else st
    let decls :=
      (st.before.map fun g => s!"margin-top: {cssLength g.width};").toList ++
      (st.after.map fun g => s!"margin-bottom: {cssLength g.width};").toList ++
      (st.indent.map fun g => s!"padding-left: {cssLength g.width};").toList ++
      (st.rule.map fun (c, n) =>
        let color := match n with
          | some name => s!"var(--{name}, {cssColor c})"
          | none => cssColor c
        -- The flex items align by baseline; the rule element then lifts
        -- itself half its own ex — the heading's x-height, since it
        -- inherits the heading's font — matching the PDF, which raises the
        -- rule half the heading face's x-height at the heading's size
        -- (`Layout.paraLineGeom`).
        s!"display: flex; align-items: baseline; gap: 0.5em; --rule-color: {color};").toList
    let mut liDecls :=
      (st.gap.map fun g => s!"{tag} > li \{ margin-top: {cssLength g.width}; }\n").toList
    if let some m := st.marker then
      match markerCss? m doc.page.scale with
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
    -- The rule's own geometry, where the document declares it: a baseline
    -- rule drops the x-height translate (`.ruled::after`) — the empty
    -- flex item's synthesised baseline is its bottom border edge (CSS
    -- Flexbox §8.5), which is where TeX's zero-depth `\hrule` ends — and
    -- a declared thickness is the border weight, the same IR fact the PDF
    -- raise and weight project (`Ir.RulePosition.raise`).
    let ruleDecls : List String := if st.rule.isNone then [] else
      (match st.rulePosition with
        | some .baseline => ["transform: none;"]
        | some .xHeight | none => []) ++
      (st.ruleThickness.map fun g => s!"border-top-width: {cssLength g.width};").toList
    let ruleCss := if ruleDecls.isEmpty then "" else
      s!"{tag}.ruled::after \{ {String.intercalate " " ruleDecls} }\n"
    let own := if decls.isEmpty then "" else s!"{tag} \{ {String.intercalate " " decls} }\n"
    -- Bound first: appending a call's result directly is the shape the
    -- cost gate rejects; a name makes the one-off append visible as one.
    let liCss := String.join liDecls
    let interCss := String.join interDecls
    css := css ++ own ++ ruleCss ++ liCss ++ interCss
  return (css, diags)

/-- A per-mille factor as CSS text: 1440 → `1.440`. -/
private def milliFactor (k : Nat) : String :=
  let pad (n : Nat) : String :=
    let s := toString n
    "".pushn '0' (3 - min 3 s.length) ++ s
  s!"{k / 1000}.{pad (k % 1000)}"

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

/-- A vertical gap of `k` screen rhythm quanta, as a rem value. The screen
context's rhythm unit is its own body leading — `bodyLeadingMilli` over the
1 rem base — as the print context's is its (`Ir.leadingFor`); the quantum
is the half-unit in both. A boundary's multiple is declared once
(`Ir.rhythmGapQuanta`); each backend realizes it in its own context's
unit. Computed, never re-spelled: 1450 milli halves exactly, so every
emitted value is exact. -/
def quantaRem (k : Nat) : String := milliFactor (k * bodyLeadingMilli / 2) ++ "rem"

/-- A boundary kind's declared multiple, from the one table. -/
private def gapK (kind : String) : Nat := (Ir.rhythmGapQuanta.lookup kind).getD 0

/-- A print length as screen milli-rem: its multiple of the print quantum
at the body size (`Ir.rhythmQuantum`) realized in the screen's, the
per-context unit `backend_gaps_agree` states, rounded down to the
milli-rem. The one conversion from a print length to a screen gap: the
declared parskip (`parskipVar`) and a list level's spaces (`listRules`)
read it. -/
def screenMilli (size v : Int) : Nat :=
  if Ir.rhythmQuantum size ≤ 0 then 0
  else (v * ((bodyLeadingMilli / 2 : Nat) : Int) / Ir.rhythmQuantum size).toNat

/-- `m` milli-rem as CSS. -/
private def milliRem (m : Nat) : String := milliFactor m ++ "rem"

/-- **A converted gap is its print gap in the screen's quanta** (`_between`):
cross-multiplied, as `backend_gaps_agree` compares the table's rows, the
milli-rem `screenMilli` emits stands at most one milli-rem under the print
length's exact multiple of its quantum — 0.016 CSS px at a 16 px root —
whatever the size and the length. -/
theorem screenMilli_between (size v : Int) (hq : 0 < Ir.rhythmQuantum size) (hv : 0 ≤ v) :
    (screenMilli size v : Int) * Ir.rhythmQuantum size ≤ v * ((bodyLeadingMilli / 2 : Nat) : Int) ∧
      v * ((bodyLeadingMilli / 2 : Nat) : Int) <
        ((screenMilli size v : Int) + 1) * Ir.rhythmQuantum size := by
  have hh : (0 : Int) ≤ ((bodyLeadingMilli / 2 : Nat) : Int) := by decide
  unfold screenMilli
  generalize (Ir.rhythmQuantum size : Int) = q at *
  generalize ((bodyLeadingMilli / 2 : Nat) : Int) = h at *
  have hnq : ¬ q ≤ 0 := Int.not_le.mpr hq
  have hnn : 0 ≤ v * h / q := Int.ediv_nonneg (Int.mul_nonneg hv hh) (Int.le_of_lt hq)
  simp only [hnq, ↓reduceIte, Int.toNat_of_nonneg hnn]
  exact ⟨Int.ediv_mul_le _ (Int.ne_of_gt hq), Int.lt_ediv_add_one_mul_self _ hq⟩

/-- The base sheet's block boundaries: every block-level element the
backend emits into flow, with the declared kind of gap it opens. Emitted
as adjacent-sibling rules (`blockGapCss`): the element below owns the
boundary as `margin-top`, every block element's own margins are zero, so a
boundary has exactly one emitter. That encoding is what the realization
demands: the theorem is about the gap the box model realizes, not the
number in the sheet, and with one side of every boundary zero the block
model (adjacent margins collapse to the larger) and the flex model
(margins stack) realize the same declared value
(`single_owner_gap_exact`) — turning a container flex cannot double a gap.
The site port shipped a 52 px gap where 32 px was declared exactly that
way: spacing declared on both sides of a boundary, summed by a flex
column. A container `gap` would also be single-emission, but only where
the container opts into flex or grid, and one `gap` cannot say that a
heading opens more space than a paragraph; the sibling rule is
context-independent and names the boundary.

One boundary is bottom-owned, deliberately: the gap below a heading is the
heading's own `margin-bottom` (one peer gap, in the base heading rule),
and the default `margin-top` of whatever follows a heading is suppressed
(`blockGapCss`'s last rule), so the emitter count stays one. This is the
PDF's own semantics — a heading's band is the heading's to declare
(`Acc.flushGap` pays owed glue instead of the default, never both) — and
it lets a declared `\style{section}{ after = ... }` or a consumer sheet
own a heading's whole band with one rule on the heading itself. The cost,
stated: everything following a heading binds at that one peer gap — a
float or a second heading directly under a heading realizes 1 quantum
here where the PDF walk gives that element its own larger gap. -/
def blockGapKinds : List (String × String) :=
  [("p", "peer"), ("ul", "peer"), ("ol", "peer"), ("dl", "peer"), ("pre", "peer"),
   ("table.booktabs", "peer"),
   ("h1", "heading"), ("h2", "heading"), ("h3", "heading"), ("h4", "heading")]

/-- The realized gap equals the emitted gap, in both formatting contexts:
at a boundary whose upper side declares no margin, collapsing (block flow
takes the larger of the two adjacent margins) and stacking (a flex or grid
container adds them) agree on the one declared value. This is the theorem
the encoding exists to satisfy — with both sides declared it fails: max
and sum diverge, which is the shipped 52px-for-32px defect. -/
theorem single_owner_gap_exact (g : Int) (h : 0 ≤ g) :
    max 0 g = g ∧ 0 + g = g := by
  omega

/-- Every gap rule's kind is a declared row of the table, with a positive
multiple — no boundary silently falls to zero through a missing lookup.
The float's rules stand outside `blockGapKinds` (they carry the
`--floatsep` token), so its row is its own conjunct; the display's space is
TeX's, not a row (`displayGapRem`), and positive. -/
theorem blockGap_kinds_covers :
    (blockGapKinds.all fun e => 0 < gapK e.2) = true ∧ 0 < gapK "float" ∧
    0 < gapK "caption" ∧ 0 < gapK "trivlist" ∧
    0 < screenMilli Ir.baseFontSize (Ir.displaySkipDefault Ir.baseFontSize).width.sp := by
  decide

/-- One rule of the block-boundary sheet. `reset` states an element's own
vertical margins — zero, replacing the user agent's, or a heading's band
below; `boundary` is a boundary's one emitter, the lower side's
`margin-top`; `parskip` is the paragraph gap in force inside an element,
its `--parskip`, which every peer and list boundary under it reads — as
`\list` makes `\parsep` the `\parskip` inside a list. All render inside
`:where()` (`GapRule.render`), so the whole sheet stands at zero
specificity and order alone ranks its rules. -/
inductive GapRule where
  | reset (sel margin : String)
  | boundary (sel value : String)
  | parskip (sel value : String)
  deriving Repr, DecidableEq

def GapRule.render : GapRule → String
  | .reset sel m => s!":where({sel}) \{ margin: {m}; }\n"
  | .boundary sel v => s!":where({sel}) \{ margin-top: {v}; }\n"
  | .parskip sel v => s!":where({sel}) \{ --parskip: {v}; }\n"

def GapRule.isReset : GapRule → Bool
  | .reset _ _ => true
  | .boundary _ _ => false
  | .parskip _ _ => false

/-- The peer gap: the document's resolved `\parskip` where the page
declares one (`--parskip`, written by `baseCss` through `parskipVar`),
else the table's peer row — the value the PDF walk's `Rd.parskip` spends. -/
private def peerGap : String := s!"var(--parskip, {quantaRem (gapK "peer")})"

/-- A trivlist's boundary: its `\topsep` on top of the peer gap, through the
token the PDF walk reads (`Ir.trivlistSkip`). -/
private def trivlistGap : String :=
  s!"calc(var(--{Ir.trivlistSkipName}, {quantaRem (gapK "trivlist" - gapK "peer")}) + {peerGap})"

/-- The elements a list level spaces: every list a list block emits — a
description's `<dl>` among them (latex.ltx `description` is a `\list`) —
and every quotation (classes.dtx: `quote` is a `\list`), and not the
reference list, whose entries the PDF walk sets a peer gap apart
(`Layout.collectBibliography`), nor an algorithm's line lists, whose lines
stand a leading apart. -/
private def listElems : List String :=
  ["ul:not(.bibliography)", "ol:not(.algorithm):not(.algorithm *)", "blockquote", "dl"]

/-- A list block's item, and not a reference-list entry, an algorithm's
line or an endnote. -/
private def itemSubject : String :=
  "li:not(.bibliography *):not(.algorithm *):not([role=doc-endnotes] *)"

/-- An enclosing list's item, as `\@listdepth` counts the levels: a list
block's `<li>`, a description's `<dd>` or a quotation (a `\list` itself),
the element a nested list stands in. -/
private def itemAncestor : String := ":is(li, dd, blockquote) "

/-- A list's own space at a boundary: the level's length over the
paragraph gap in force where the boundary stands, read on the lower
element — `\@trivlist`'s `\topsep` over the surrounding `\parskip`, and
`\@item`'s `\itemsep` over the item's own. The fallback is TeX's
`\parskip`, zero at its natural width (`Layout.Geom.texParskip`), not the
engine's paragraph mark. -/
private def listSpace (m : Nat) : String := s!"calc({milliRem m} + var(--parskip, 0rem))"

/-- One list level's three spaces in screen milli-rem, `\topsep`,
`\itemsep` and `\parsep` of `Ir.listSkips`, each through `screenMilli`. -/
def listLevelGaps (size : Int) (sk : Ir.ListSkips) : Nat × Nat × Nat :=
  (screenMilli size sk.topsep.width.sp, screenMilli size sk.itemsep.width.sp,
   screenMilli size sk.parsep.width.sp)

/-- A list level's `\@topsepadd` where the list opens a paragraph, in
screen milli-rem: `\topsep` with the level's `\partopsep` on top
(`Ir.partopsepFor`, the site the PDF walk spends), one conversion of the
summed length. -/
def listOpenGap (size : Int) (sk : Ir.ListSkips) (partopsep : SymGlue) : Nat :=
  screenMilli size (sk.topsep.width.sp + partopsep.width.sp)

/-- One list level's rules, `pre` reaching the level — an item ancestor
(`itemAncestor`) per enclosing list, as `\@listdepth` counts them over
every kind: its items', description items' and quotations' paragraphs
stand `\parsep` apart, each list and quotation stands `\@topsepadd`
(`opened`) from its neighbours above and below, and each item after the
first — a description's `<dt>` after the `<dd>` before it — opens
`\itemsep`. A list or quotation
whose `\begin` stands inside an open paragraph carries the in-paragraph
role's class (`Ir.inParagraphRole`), and `\@trivlist` gives it `\topsep`
alone (latex.ltx:15871-15878): its pair stands after the level's own, and
only where the level's `\partopsep` is not zero. An item after one whose
last block is a nested list stands the larger of the two spaces that meet
there, the nested list's `\@topsepadd` and the item's `\itemsep` —
`\addvspace` takes the larger, and the item's `\parskip` stands on top —
the one boundary the nested list's own pair cannot reach, since the item
after it is its parent's sibling: `nested` is the next level's `\topsep`
and its `\@topsepadd` where it opens a paragraph, each rule written only
where it is the larger. -/
private def listLevelRules (pre : String) (g : Nat × Nat × Nat) (opened : Nat)
    (nested : Nat × Nat) : List GapRule :=
  let inPar := roleClass Ir.inParagraphRole
  let after (sel : String) (m : Nat) : GapRule :=
    let last := s!":has(> :is({", ".intercalate listElems}){sel}:last-child)"
    .boundary s!"{pre}li{last} + {itemSubject}, {pre}dd{last} + dt" (listSpace m)
  [.parskip s!"{pre}{itemSubject}, {pre}blockquote > *, {pre}dl > *" (milliRem g.2.2),
   .boundary (", ".intercalate (listElems.map fun e => s!"{pre}* + {e}")) (listSpace opened),
   .boundary (", ".intercalate (listElems.map fun e => s!"{pre}{e} + *")) (listSpace opened),
   .boundary s!"{pre}li + {itemSubject}, {pre}dd + dt" (listSpace g.2.1)] ++
  (if opened == g.1 then [] else
    [.boundary s!"{pre}* + .{inPar}" (listSpace g.1),
     .boundary s!"{pre}.{inPar} + *" (listSpace g.1)]) ++
  (if nested.1 ≤ g.2.1 then [] else [after "" nested.1]) ++
  (if nested.2 ≤ max g.2.1 nested.1 then [] else [after s!":not(.{inPar})" nested.2])

/-- The list rules a page's class owes: LaTeX's `\@list⟨n⟩` for levels one
to three — a deeper level keeps the third's, as `Ir.listSkips` clamps —
read from the one resolving site the PDF walk spends and converted once
(`listLevelGaps`, `listOpenGap`, over the preamble's `tokens` a declared
`\partopsep` rides in). The web's lineage owes none: its lists open the
peer gap and its items stand a leading apart, as its print twin sets
them. -/
def listRules (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens) : List GapRule :=
  let spaces (n : Nat) : Nat × Nat := match Ir.listSkips l size n with
    | some sk => ((listLevelGaps size sk).1, listOpenGap size sk (Ir.partopsepFor l size n tokens))
    | none => (0, 0)
  [1, 2, 3].flatMap fun n => match Ir.listSkips l size n with
    | some sk => listLevelRules (String.join (List.replicate (n - 1) itemAncestor))
        (listLevelGaps size sk) (spaces n).2 (spaces (n + 1))
    | none => []

/-- A lineage's list indents as CSS, per level: a list's items, a
description's `<dd>` and a quotation's two edges stand the level's
`\leftmargin` in, from the one resolving site the page's margins read
(`Ir.leftMarginMilli`), in the em the class spells it in (the page reads
the same thousandths of the body size, `Ir.leftMargin`), under the
custom property of the length a document declares it in
(`Ir.leftMarginName`, which `tokenVars` writes), each level reached
through an item ancestor per enclosing list or quotation, to the kernel's
six. A lineage with no stack, the web's, keeps its lists' one indent. -/
def listIndentCss (l : Ir.ListLineage) : String :=
  String.join ((List.range 6).map fun k =>
    let pre := String.join (List.replicate k itemAncestor)
    let v := s!"var(--{Ir.leftMarginName (k + 1)}, " ++ (match Ir.leftMarginMilli l (k + 1) with
      | some m => s!"{decMilli m}em"
      | none => "1.35rem") ++ ")"
    s!"{pre}ul, {pre}ol, {pre}dd \{ padding-left: {v}; }\n{pre}blockquote \{ padding: 0 {v}; }\n")

/-- The rules a theorem-like block's space owes, on the element its role's
class marks (`Ir.thmSkips` at the top level, the one resolving site the PDF
walk spends, converted once through `screenMilli`): the space above, over
the parskip in force where its spelling's `\@topsep` carries one, and the
space below, over the next block's; the web's lineage keeps the trivlist's.
The mode is read as inside a paragraph: this sheet carries no `\partopsep`
reading of it, as its lists' does not. -/
def thmRules (l : Ir.ListLineage) (size : Int) : List GapRule :=
  Ir.ThmSpace.all.flatMap fun k =>
    let c := "." ++ roleClass (Ir.thmSpaceRole k)
    match Ir.thmSkips l size 1 {} k false with
    | some sk =>
      let above := screenMilli size sk.above.width.sp
      [.boundary s!"* + {c}" (if sk.parskipAbove then listSpace above else milliRem above),
       .boundary s!"{c} + *" (listSpace (screenMilli size sk.below.width.sp))]
    | none => [.boundary s!"* + {c}" trivlistGap, .boundary s!"{c} + *" trivlistGap]

/-- The resets: every block element's own vertical margins, first; a slide's
frame title sets flush in its header band, which owns the title's space. -/
private def gapResets : List GapRule :=
  [.reset "p, ul, ol, li, dl, dd, pre, blockquote" "0",
   .reset "h1, h2, h3, h4" s!"0 0 {quantaRem (gapK "peer")}",
   .reset "section.slide > header h2" "0",
   .reset "figure.float" "0 auto"]

/-- The boundaries the list levels stand after: the peer elements', the
reference list's entries — a peer gap apart, the paragraphs
`Layout.collectBibliography` sets them as — then the trivlist's pair. -/
private def gapBeforeLists : List GapRule :=
  (blockGapKinds.filter (·.2 != "heading")).map (fun (sel, _) =>
    .boundary s!"* + {sel}" peerGap) ++
  [.boundary ".bibliography > li + li" peerGap,
   .boundary s!"* + .{roleClass Ir.trivlistRole}, * + blockquote" trivlistGap,
   .boundary s!".{roleClass Ir.trivlistRole} + *, blockquote + *" trivlistGap]

/-- The display's space, TeX's long `\abovedisplayskip` (`Ir.displaySkipsFor`)
as the screen's multiple of its quantum (`screenMilli`) — the same multiple
at every standard body, since the size files scale the skip with the type
(10, 11 and 12 pt over quanta of 6, 6.6 and 7.2 pt). -/
private def displayGapRem : String :=
  milliRem (screenMilli Ir.baseFontSize (Ir.displaySkipDefault Ir.baseFontSize).width.sp)

/-- The boundaries the list levels stand before: the headings', the float's
and the display's pairs, the float's caption seam, and the heading's
follower, last. A level-1
heading opens its `<section>` (`sectionize`), so no sibling stands above
it and `* + h2` never meets it; the heading owns the boundary above its
section instead, its margin collapsing through the section's edge, which
carries none — on the heading, where a consumer sheet styling its
sections as bands keeps them flush. -/
private def gapAfterLists : List GapRule :=
  (blockGapKinds.filter (·.2 == "heading")).map (fun (sel, kind) =>
    .boundary s!"* + {sel}" (quantaRem (gapK kind))) ++
  [.boundary s!"* + section[id] > h{Ir.headingRank 1}:first-child" (quantaRem (gapK "heading")),
   .boundary "* + figure.float" s!"var(--floatsep, {quantaRem (gapK "float")})",
   .boundary "figure.float + *" s!"var(--floatsep, {quantaRem (gapK "float")})",
   .boundary "* + .display" s!"var(--{Ir.displaySkipAbove}, {displayGapRem})",
   .boundary ".display + *" s!"var(--{Ir.displaySkipBelow}, {displayGapRem})",
   -- The object under a caption above it: the skip facing it is the
   -- caption's own `margin-bottom`, the float's one internal seam, so the
   -- object's peer margin yields, as the page's float plan pays that skip
   -- alone (`Ir.captionSides`).
   .boundary "figure.float > figcaption:first-child + *" "0",
   .boundary ":is(h1, h2, h3, h4) + *" "0"]

/-- The block-boundary sheet, the one emitter of every vertical margin a
block element carries. The resets come first: the element's own margins
at zero specificity, so no element rule stands above a boundary rule —
the defect this list replaced, where `p { margin: 0 }` at (0,0,1) beat
every `:where(* + p)` and no peer gap rendered. Then one adjacent-sibling
rule per block element (`blockGapKinds`), a pair rule standing later than
the element rules it meets, so its value wins the boundary while the
neighbour's own margin stays zero — the PDF walk's `addvspace` taking the
larger: the trivlist's (`\topsep`); a theorem-like block's (`thmRules`);
the page's list levels (`listRules`), after them, so a list's `\topsep`
against a centred block is the larger, and before the headings, so a
heading's space against a list is; the float's (`--floatsep`) and the
display's (`Ir.displayAbove`/`displayBelow`); and last, the follower of a
heading, whose band below is the heading's own (the reset's
`margin-bottom`). Any
consumer rule — a declared `\style` on the bare element or a reader
stylesheet owning a container's spacing with `gap` — wins without a
specificity fight, which is the HTML backend's override contract. -/
def blockGapRules (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens) : List GapRule :=
  gapResets ++ gapBeforeLists ++ thmRules l size ++ listRules l size tokens ++ gapAfterLists

def blockGapCss (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens) : String :=
  String.join ((blockGapRules l size tokens).map GapRule.render)

private theorem dropWhile_append_all {α : Type} (p : α → Bool) (xs ys : List α)
    (h : xs.all p = true) : (xs ++ ys).dropWhile p = ys.dropWhile p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [h.1, ih h.2]

private theorem dropWhile_none {α : Type} (p : α → Bool) (ys : List α)
    (h : ys.all (fun y => !p y) = true) : ys.dropWhile p = ys := by
  cases ys with
  | nil => rfl
  | cons y ys =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [h.1]

private theorem listLevelRules_noReset (pre : String) (g : Nat × Nat × Nat) (o : Nat)
    (n : Nat × Nat) : (listLevelRules pre g o n).all (fun r => !r.isReset) = true := by
  unfold listLevelRules
  split <;> split <;> split <;> rfl

private theorem listRules_noReset (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens) :
    (listRules l size tokens).all (fun r => !r.isReset) = true := by
  simp only [listRules, List.all_flatMap, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  refine ⟨?_, ?_, ?_⟩ <;> split <;> first | rfl | exact listLevelRules_noReset _ _ _ _

private theorem thmRules_noReset (l : Ir.ListLineage) (size : Int) :
    (thmRules l size).all (fun r => !r.isReset) = true := by
  simp only [thmRules, List.all_flatMap, List.all_eq_true]
  intro k _
  split <;> simp [GapRule.isReset]

/-- **Each boundary's gap is its emitter's, and it renders** (`_contract`),
for every class's list lineage and body size: every rule of the one
emitter stands at zero specificity, so order alone ranks them, and no
reset stands after a boundary rule — the premise `single_owner_gap_exact`
needs before the emitted gap is the rendered one; the heading's follower
rule stands last. That no base-sheet rule outside the emitter declares a
margin on an element it spaces is the text's to show, and
`htmlRhythmChecks` reads it off every golden page's sheet. -/
theorem blockGap_owner_contract (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens) :
    ((blockGapRules l size tokens).dropWhile GapRule.isReset).all (fun r => !r.isReset) = true ∧
    (blockGapRules l size tokens).getLast? = some (.boundary ":is(h1, h2, h3, h4) + *" "0") := by
  have hall : (gapBeforeLists ++ thmRules l size ++ listRules l size tokens ++ gapAfterLists).all
      (fun r => !r.isReset) = true := by
    simp only [List.all_append, thmRules_noReset, listRules_noReset, Bool.and_true,
      Bool.and_eq_true]
    exact ⟨by decide, by decide⟩
  refine ⟨?_, ?_⟩
  · simp only [blockGapRules, List.append_assoc] at hall ⊢
    rw [dropWhile_append_all _ _ _ (by decide), dropWhile_none _ _ hall]
    exact hall
  · have hlast : gapAfterLists.getLast? = some (.boundary ":is(h1, h2, h3, h4) + *" "0") := by
      decide
    simp only [blockGapRules, List.getLast?_append, hlast, Option.some_or]

/-- **A list's spaces are LaTeX's `\@list⟨n⟩` on both artifacts** (`_agree`):
for any level's spaces — so at every lineage, body size and level
`Ir.listSkips` answers for, the one resolving site the PDF walk spends —
each of the four lengths the level's rules carry (`listLevelGaps`,
`listOpenGap`), its `\topsep` above and below a list inside an open
paragraph, its `\topsep` and `\partopsep` above and below one that opens a
paragraph, its `\itemsep` before an item and its `\parsep` inside one, is
the print length as the screen's multiple of its quantum, to within a
milli-rem (`screenMilli_between`). -/
theorem listGaps_agree (size : Int) (sk : Ir.ListSkips) (pt : SymGlue)
    (hq : 0 < Ir.rhythmQuantum size)
    (h0 : 0 ≤ sk.topsep.width.sp ∧ 0 ≤ sk.itemsep.width.sp ∧ 0 ≤ sk.parsep.width.sp)
    (hp : 0 ≤ sk.topsep.width.sp + pt.width.sp) :
    let h : Int := ((bodyLeadingMilli / 2 : Nat) : Int)
    let q := Ir.rhythmQuantum size
    let g := listLevelGaps size sk
    let o := listOpenGap size sk pt
    ((g.1 : Int) * q ≤ sk.topsep.width.sp * h ∧ sk.topsep.width.sp * h < ((g.1 : Int) + 1) * q) ∧
    ((g.2.1 : Int) * q ≤ sk.itemsep.width.sp * h ∧
      sk.itemsep.width.sp * h < ((g.2.1 : Int) + 1) * q) ∧
    ((g.2.2 : Int) * q ≤ sk.parsep.width.sp * h ∧
      sk.parsep.width.sp * h < ((g.2.2 : Int) + 1) * q) ∧
    ((o : Int) * q ≤ (sk.topsep.width.sp + pt.width.sp) * h ∧
      (sk.topsep.width.sp + pt.width.sp) * h < ((o : Int) + 1) * q) :=
  ⟨screenMilli_between size _ hq h0.1, screenMilli_between size _ hq h0.2.1,
   screenMilli_between size _ hq h0.2.2, screenMilli_between size _ hq hp⟩

/-- The web's lineage owes no list space: a webpage's lists keep the peer
gap and its items a leading apart, where its print twin sets them. -/
theorem listRules_web_exact (size : Int) (tokens : Ir.Tokens) :
    listRules .web size tokens = [] := rfl

/-- The document's declared `\parskip` as the screen peer gap: its multiple
of the print quantum at the document's size, realized in the screen's
(`screenMilli`). Written only where the page
declares one — the `slides` and `resume` class records declare zero, as
their PDF spends nothing between paragraphs — so an undeclared page keeps
the peer rules' fallback. -/
def parskipVar (page : Ir.PageSpec) : String :=
  match page.parskip with
  | none => ""
  | some g => s!"    --parskip: {milliRem (screenMilli page.fontSize g.width.sp)};\n"

/-- The PDF backend's shipped default gap at a boundary kind: the values
placement realizes 1:1 — the peer token (`flushGap_default_exact` pays it
at an undeclared boundary), twice it above a heading (the walk's
`addvspace`, `heading_default_before_exact`), and the float and caption
tokens the float path resolves. The dispatch is the tie between the
table's row names and the engine's tokens; an unknown name is 0, which
`backend_gaps_agree` cannot miss (a zero row agrees with no positive
one). -/
private def pdfGapSp : String → Dim.Sp
  | "peer" => (Ir.parskipDefault Ir.baseFontSize).width.sp
  | "heading" => 2 * (Ir.parskipDefault Ir.baseFontSize).width.sp
  | "caption" => (Ir.captionSepDefault Ir.baseFontSize).width.sp
  | "float" => (Ir.floatSepDefault Ir.baseFontSize).width.sp
  | "trivlist" => (Ir.parskipDefault Ir.baseFontSize).width.sp
      + (Ir.trivlistSkipDefault Ir.baseFontSize).width.sp
  | _ => 0

/-- The screen backend's emitted default gap, in milli-rem: the number
`quantaRem` prints for the kind's row. -/
private def htmlGapMilliRem (kind : String) : Nat :=
  gapK kind * bodyLeadingMilli / 2

/-- The agreement layer, the user's ask: a document's vertical rhythm does
not depend on which artifact is built. Both backends realize every default
boundary from the same declared row (`Ir.rhythmGapQuanta`), each in its
own context's quantum, so the shipped gaps stand in the same ratios row by
row — cross-multiplied here over every pair of rows, PDF sp against
emitted milli-rem, the values the artifacts actually carry. A backend that
re-spelled one multiple fails this build. Two moduli, named rather than
hidden:

- **Preferred values only.** CSS has no glue: the HTML side realizes each
  gap at exactly its preferred value, while the PDF may negotiate within
  declared rubber — shrink spent only against a page break and always
  reported (N0200), stretch never. Cross-backend equality is a statement
  about preferred values; rubber is a PDF-only negotiation, and a document
  that declares rubber is telling the PDF something HTML cannot honour.
- **Per-context units.** The shared thing is the multiple, not the
  length: the PDF's quantum is half its print leading
  (`Ir.rhythmQuantum`), the screen's half its own body leading
  (`bodyLeadingMilli`, the top of Butterick's band, over the 1 rem base).
  Matching absolute lengths would put print leading on a screen or screen
  leading on paper; the rhythm is per typographic context, and each
  backend's context is its own. -/
theorem backend_gaps_agree :
    (Ir.rhythmGapQuanta.all fun e1 =>
      Ir.rhythmGapQuanta.all fun e2 =>
        pdfGapSp e1.1 * (htmlGapMilliRem e2.1 : Int)
          == pdfGapSp e2.1 * (htmlGapMilliRem e1.1 : Int)) = true := by decide

/-- The slide box's inner padding and corner geometry, one spelling each:
the frame-title bar bleeds to the slide edge by negating exactly this
padding, and its top corners round at the slide's radius less the border
(the nested-corner rule: an inner radius concentric with an outer one is
the outer less the gap). Four literals that must stay pairwise equal are
one pair; a 1 px corner mismatch is unrepresentable. -/
private def slidePadV : String := "1.4rem"
private def slidePadH : String := "1.8rem"
private def slideRadiusPx : Nat := 8
private def slideBorderPx : Nat := 1

/-- The deck's safe area: the padding the paged slide keeps clear on
every side, as a token reference with its engine default. Keynote's
default themes keep roughly 5–7% of the slide dimension clear (read from
the bundled masters); the default takes the middle, 6vmin — per mille of
the smaller viewport dimension, so the ratio holds in either orientation.
Overridable like any token (`--safearea`), by a bundle or a reader. -/
private def safeareaVar : String := "var(--safearea, 6vmin)"

/-- The title band's cap: a slide header may take at most this much of
the slide's height — Keynote's default masters hold the title band to
about 1/8 to 1/10 of the slide; the default takes the upper bound, 1/8,
as `--titleband`'s engine value. -/
private def titlebandVar : String := "var(--titleband, 12.5dvh)"

/-- A named step as a CSS factor, through the one resolving site: a
per-mille base makes `Ir.scaleStep` report the step itself, so the bar's
type reads the scale the PDF sets from rather than a second reading of the
table. -/
private def stepFactor (name : String) : String :=
  milliFactor (Ir.scaleStep (1000 : Dim.Sp) name).toNat

/-- The grounds the stylesheet paints under content, each with the selector
of the element it paints: the frame-title bar, the standout inversion, the
title page, and each titled kind's bar — the grounds the realization walk
judges a run on (`Ir.recolorRolesBlock`), read off the one resolved
`Design`. -/
def inkScopes (d : Design) : List (String × Ir.Color) :=
  (d.frametitle.map fun p => ("section.slide > header", p.bg)).toList ++
    (d.footline.bar.map fun bg => ("footer.slide-foot", bg)).toList ++
    [("section.slide.standout", d.standout.bg)] ++
    (d.titlepage.map fun p => ("section.slide.title-page", p.bg)).toList ++
    ([(Ir.TitledKind.block, d.blockTitle), (.alert, d.alertTitle),
        (.example, d.exampleTitle)] : List (Ir.TitledKind × Ir.TitledLook)).filterMap
      fun (k, look) => look.bar.map fun bar => (s!"section.block-{k.name} > header", bar)

/-- One recorded ink as the scoped custom property that re-points its role's
token on its ground: a run's `var(--role)` there resolves to the ink the PDF
paints the same run in. -/
def inkDecl (e : Ir.GroundInk) : String := s!"--{e.role}: {cssColor e.ink};"

/-- The declarations one ground's scope carries: every ink the design
records on that ground. -/
def inkDecls (d : Design) (g : Ir.Color) : List String :=
  (d.inks.toList.filter (·.ground == g)).map inkDecl

/-- **The HTML declares every recorded ink on the ground it was realized
for.** For every scope the stylesheet paints on an ink's ground, the
scope's declarations carry that ink — the HTML half of
`realized_agree`. -/
theorem inkDecls_projects (d : Design) (e : Ir.GroundInk) (he : e ∈ d.inks)
    (g : Ir.Color) (hg : (e.ground == g) = true) :
    s!"--{e.role}: {cssColor e.ink};" ∈ inkDecls d g := by
  simp only [inkDecls, List.mem_map, List.mem_filter, Array.mem_toList_iff]
  exact ⟨e, ⟨he, hg⟩, rfl⟩

/-- The scoped token rules: per ground the stylesheet paints, the inks
recorded there. A design whose pairs all pass records none and emits
nothing. -/
def inkScopeCss (d : Design) : String :=
  String.join ((inkScopes d).filterMap fun (sel, g) =>
    let decls := inkDecls d g
    if decls.isEmpty then none
    else some (sel ++ " {\n" ++ String.join (decls.map fun x => s!"  {x}\n") ++ "}\n"))

/-- **One realized ink per role and ground, in both artifacts.** Every ink
the realized document's design records — a role, the colour it was
declared as, the ground it realized on — is the ink the PDF's run rewrite
gives a run of that role and colour on that ground, and the ink every
scope the stylesheet paints on that ground declares: two projections of
one IR value (`Ir.Design.inks`), in the shape of `backend_gaps_agree`.
The HTML used to realize the bar and standout tokens a second time, over a
palette entry already realized for the page, and shipped a third value
neither the PDF nor the N0022 note named. -/
theorem realized_agree (doc : Doc) (site : Contrast.ColorSite) (h0 : doc.palette.inks = #[])
    (e : Ir.GroundInk) (he : e ∈ (Design.ofDoc (Contrast.realizeDoc doc site).1).inks)
    (g : Ir.Color) (hg : (e.ground == g) = true) :
    Contrast.realizeRecolor doc site doc.palette (some e.ground) (some e.role) e.declared =
        e.ink ∧
      s!"--{e.role}: {cssColor e.ink};" ∈
        inkDecls (Design.ofDoc (Contrast.realizeDoc doc site).1) g :=
  ⟨Contrast.realized_projects doc site h0 e he, inkDecls_projects _ e he g hg⟩

/-- **The title page's slots, pinned**: the stylesheet projection of the IR
value `Layout.B.placeSlot` places by (`Ir.TitleSlot.place`). Each slot's box
stands in the stage at the same page point the page puts it at, through the
same share arithmetic (`Ir.shareOf`; `Ir.pagePoint_agree` proves the
arithmetic, and `titleSlotShipChecks` tests that each axis's share lands on
its own property), and the box point is the same translate of the box's own
extent; the shifts, measure and
inner sep are `em` of the body size, the unit the deck's type scales in, so
the box keeps its place as the stage scales. The slot's content takes its
own template alone, as on the page: the heading's size and weight are the
slot's (`Config.slotTitle`). Emitted for the paged deck, on screen and on
paper alike: a printed deck pages the stage itself (`deckPageRule`), so
the slots stand where the stage puts them. -/
def titleSlotCss (doc : Doc) : String :=
  let slots := ((doc.styles.find? "titlepage").getD {}).slots
  if slots.isEmpty || doc.docClass != .slides then "" else
  let body := max doc.page.fontSize 1
  let emOf (l : Dim.Length) : String :=
    let e := if l.ex != 0 then s!" + {decMilli l.ex}ex" else ""
    s!"{decMilli (l.em + l.sp * 1000 / body)}em{e}"
  let zero : Dim.Length := {}
  let rules := slots.zipIdx.toList.filterMap fun (sl, i) =>
    let (slotWidth, place) := sl.box
    place.map fun pl =>
      let sel := s!"section.slide.title-page > .{roleClass (Ir.titleSlotRole i)}"
      let outer := Dim.Length.ofSp Ir.pgfOuterSep
      let anchorOffset (s : Nat × Nat) : Dim.Length :=
        outer.scale ((s.2 : Int) - (s.1 : Int)) (s.1 + s.2)
      let dx := ((pl.xshift.map (·.width)).getD zero).add
        (anchorOffset pl.anchor.hshares)
      let dy := (pl.yshift.map (·.width)).getD zero
      -- TikZ's `yshift` is up; the stage's `top` grows down. Its outer
      -- sep expands compass anchors but is not CSS padding.
      let up0 : Dim.Length := { sp := -dy.sp, em := -dy.em, ex := -dy.ex }
      let up := up0.add (anchorOffset pl.anchor.vshares)
      let sep := (pl.innerSep.map (·.width)).getD
        (Dim.Length.ofSp (Ir.pgfInnerSep doc.page.fontSize))
      let width := match slotWidth with
        | some w => s!" width: {emOf w.width};"
        | none => ""
      s!"{sel} \{ position: absolute; margin: 0;\n" ++
      s!"  left: calc({decMilli (Ir.shareOf pl.pagePoint.hshares 100000)}% + {emOf dx});\n" ++
      s!"  top: calc({decMilli (Ir.shareOf pl.pagePoint.vshares 100000)}% + {emOf up});\n" ++
      s!"  transform: translate(-{decMilli (Ir.shareOf pl.anchor.hshares 100000)}%, \
-{decMilli (Ir.shareOf pl.anchor.vshares 100000)}%);\n" ++
      s!"  padding: {emOf sep};{width} }\n"
  "@media screen, print { section.slide.title-page { position: relative; }\n" ++
  String.join rules ++
  "section.slide.title-page > [class^=\"u-titlepage-slot-\"] h1 {\n" ++
  "  font-size: 1em; font-weight: inherit; margin: 0; }\n" ++
  "section.slide.title-page > [class^=\"u-titlepage-slot-\"] p { margin: 0; } }\n"

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
  -- The titled block: its header bold, the bar behind it when the design
  -- declares one — `Ir.titledLook` is the one resolving site, mirrored
  -- here as var() fallbacks under the resolved condition, exactly the
  -- frame-title rule. Padding is the rhythm's own quantum, this backend's
  -- realization of the PDF bar's half-body pad.
  "section.block > header { font-weight: bold; }\n" ++
  (String.join ([Ir.TitledKind.block, .alert, .example].map fun kind =>
    match (Ir.titledLook doc.palette kind).bar with
    | some _ =>
      s!"section.block-{kind.name} > header \{ background: var(--{kind.name}titlebg);\n" ++
      s!"  color: var(--{kind.name}titlefg, var(--bg, #fff));\n" ++
      s!"  padding: {quantaRem 1} {quantaRem 2}; }\n"
    | none =>
      match kind with
      | .block => ""
      | .alert =>
        "section.block-alert > header { color: var(--alerttitlefg, var(--alert)); }\n"
      | .example =>
        "section.block-example > header { color: var(--exampletitlefg, var(--example)); }\n")) ++
  (if d.frametitle.isSome then
    "section.slide > header { background: var(--frametitlebg);\n" ++
    "  color: var(--frametitlefg, var(--bg, #fff));\n" ++
    -- The bar sets at the title's own step, so `frametitlepadding` — an em
    -- of the title size, `\ht\strutbox` measured after
    -- `\usebeamerfont{frametitle}` — resolves here against the size it is
    -- defined in, exactly as `collectFrameTitle` resolves it at
    -- `titleSize`. Without the declared size the em would resolve against
    -- the body base and the bar would come out at the body's 0.84em where
    -- the PDF pays the title's; the inner h2 drops to `1em` in the deck's
    -- own override so the step is paid once, not squared.
    s!"  font-size: {stepFactor "Large"}rem;\n" ++
    -- The bar owns no space below: the frame body's first block pays its
    -- own gap (`blockGapCss`), one emitter per boundary.
    s!"  margin: -{slidePadV} -{slidePadH} 0;\n" ++
    s!"  padding: var(--frametitlepadding, {quantaRem 1}) {slidePadH};\n" ++
    s!"  border-radius: {slideRadiusPx - slideBorderPx}px {slideRadiusPx - slideBorderPx}px 0 0; }\n" ++
    "section.slide > header h2 { color: inherit; font-size: 1em; }\n" ++
    -- On the paged deck the slide is the viewport — on paper the page —
    -- cornerless: the bar squares off with it and bleeds through the
    -- safe-area padding, negating exactly the token the slide pads by.
    (if doc.docClass == .slides then
      "@media screen, print { section.slide > header { border-radius: 0;\n" ++
      -- The deck sets type on `main` in `vh`, so the bar retakes the title
      -- step in `em` to ride the stage rather than pinning to the root.
      s!"  font-size: {stepFactor "Large"}em;\n" ++
      s!"  margin: calc(-1 * {safeareaVar}) calc(-1 * {safeareaVar}) 0;\n" ++
      s!"  padding: var(--frametitlepadding, {quantaRem 1}) {safeareaVar}; } }\n"
     else "") else
    "section.slide > header { color: var(--frametitlefg, var(--fg)); }\n" ++
    "section.slide > header h2 { color: inherit; }\n") ++
  -- The headline band: the poster page's <header> around the title matter
  -- and the two corner-logo slots. Colours are the same frametitle tokens
  -- the PDF band resolves (one resolving site per backend, one declared
  -- pair), gated on the pair as the slide bar's rule is; the matter's side
  -- is the `titlepage` style's declared token (undeclared centres,
  -- `\@maketitle`'s own rule). A centred matter stands on the band's centre
  -- whatever logo stands beside it, as the PDF sets it and as the gemini
  -- headline reserves `\maxlogowidth` on both sides "to keep title
  -- centered" (beamerthemegemini.sty): two equal flexible tracks around
  -- it, each logo pinned to its own corner; on a band too narrow for equal
  -- reserves the matter keeps clear of both logos. A declared side sets the
  -- matter from the logo beside it.
  (match doc.headline with
   | some _ =>
     let side : Ir.HAlign := match (doc.styles.find? "titlepage").bind (·.align) with
       | some "left" => .left
       | some "right" => .right
       | _ => .center
     let pad := s!"gap: {quantaRem 2}; padding: {quantaRem 2} {quantaRem 3}; }\n"
     (if side == .center then
       "body > header.headline { display: grid; grid-template-columns: 1fr auto 1fr;\n" ++
       "  align-items: center; " ++ pad ++
       "body > header.headline > .headline-matter { grid-area: 1 / 2; text-align: center; }\n" ++
       "body > header.headline > .headline-logo:first-child { grid-area: 1 / 1;\n" ++
       "  justify-self: start; }\n" ++
       "body > header.headline > .headline-matter ~ .headline-logo { grid-area: 1 / 3;\n" ++
       "  justify-self: end; }\n"
      else
       "body > header.headline { display: flex; align-items: center;\n  " ++ pad ++
       s!"body > header.headline .headline-matter \{ flex: 1; text-align: {side.align}; }\n") ++
     "body > header.headline h1 { margin: 0; }
" ++
     (if d.frametitle.isSome then
       "body > header.headline { background: var(--frametitlebg);
" ++
       "  color: var(--frametitlefg, var(--bg, #fff)); }
" ++
       "body > header.headline h1 { color: inherit; }
"
      else "")
   | none => "") ++
  -- The title page's own ground, gated on the declared pair exactly as the
  -- bar's rule is: a design that declares none emits no rule, so a page the
  -- PDF leaves on the document's ground is not painted here either. The
  -- role is the one the PDF path reads (`Layout.titleGround`, through
  -- `Ir.Design.ofPalette`); the reference resolves against the `:root`
  -- declaration `paletteVars` writes for it.
  (match d.titlepage with
   | some _ =>
     "section.slide.title-page { background: var(--titlepagebg);\n" ++
     "  color: var(--titlepagefg, var(--bg, #fafaf9)); }\n" ++
     "section.slide.title-page h1 { color: inherit; }\n"
   | none => "") ++
  titleSlotCss doc ++
  -- A role names a hue; the contract chooses its lightness on each ground
  -- (`Contrast.realizeDoc`, the one solver site): where a run realized on
  -- a ground the stylesheet paints, the scope carries the ink the palette
  -- records there, so a run's var(--role) resolves to the value the PDF
  -- paints it in rather than the page's.
  inkScopeCss d ++
  -- Rules are available to later palette epochs too; the section node
  -- itself is gated on that epoch's resolved section-progress pair.
  (if doc.docClass.record.model == .frame then
    s!"section.section-page \{ text-align: center; padding: {quantaRem 3} 0;\n" ++
    "  break-inside: avoid; }\n" ++
    "section.section-page h2 { display: inline-block; text-align: left;\n" ++
    "  min-width: 60%; margin: 0; color: var(--sectiontitlefg, var(--fg)); }\n" ++
    -- The height reads the same token the PDF path reads
    -- (`progressheight`), with the same fallback — moloch's own 1pt
    -- (beamerouterthememoloch.dtx) — one resolving site per backend, one
    -- declared value.
    ".progress { background: var(--sectionprogressbg, var(--progressbg, var(--bg)));\n" ++
    "  height: var(--progressheight, 1pt);\n" ++
    s!"  width: 60%; margin: {quantaRem 1} auto 0; }\n" ++
    ".progress > div { background: var(--sectionprogressfg, var(--progressfg)); height: 100%; }\n" ++
    -- The paged deck's own progress: a hairline across the viewport top,
    -- scaled by how far the reader has paged through the deck —
    -- declarative where the platform has scroll-driven animations
    -- (`scroll(root x)`, Scroll-driven Animations 1: the axis is the
    -- deck's own), the same tokens as the section-page bar, and the same
    -- floor as `revealCss`: without the feature the rules never apply and
    -- the deck is fully navigable without its bar. Screen only: paper has
    -- no scroll to report, and the hairline does not print — unstyled it
    -- is an empty box after the last stage's forced break, for which
    -- Chromium opens a blank sheet.
    (if doc.docClass == .slides && d.progress.isSome then
      "@media screen { @supports (animation-timeline: scroll()) {\n" ++
      ".deck-progress { position: fixed; top: 0; left: 0; width: 100%;\n" ++
      "  height: var(--progressheight, 1pt); background: var(--progressfg);\n" ++
      "  transform-origin: 0 50%;\n" ++
      "  animation: ltx-deck-progress linear both;\n" ++
      "  animation-timeline: scroll(root x); }\n" ++
      "@keyframes ltx-deck-progress { from { transform: scaleX(0) } \
to { transform: scaleX(1) } }\n" ++
      "} }\n" ++
      "@media print { .deck-progress { display: none; } }\n"
     else "") else "") ++
  -- The chrome footer: colour from the muted key, size from the shared
  -- scale (the footline step, `Ir.footline`), positions fixed by the declared
  -- side — each slot pinned to its edge, as `Layout.bandSlotX` pins the
  -- page's — so nothing a slot contains can move another. The band holds
  -- one line (`min-height: 1lh`, CSS Values 4 §6.1.3: the element's own
  -- line-height); a colliding slot paints under or over by declared
  -- priority (`z-index` from `BandSlot.rank`, set per span), never moves.
  (if doc.docClass.record.chrome && doc.foot.isNone &&
      (doc.chrome.hasFooter || doc.body.any fun b => match b with
        | .framefoot xs => !xs.isEmpty
        | _ => false) then
    "section.slide > footer.slide-foot { position: relative;\n" ++
    s!"  min-height: 1lh; margin-top: {quantaRem 2}; color: var(--muted);\n" ++
    "  background: var(--footlinebg, transparent); }\n" ++
    "footer.slide-foot > .band-left { position: absolute; left: 0;\n" ++
    "  white-space: nowrap; }\n" ++
    "footer.slide-foot > .band-right { position: absolute; right: 0;\n" ++
    "  white-space: nowrap; }\n" ++
    -- A named size inside a slot is the body's step, as TeX's size
    -- commands are absolute and as the page sets it
    -- (`Layout.setBandSlot`): the footer's own step is undone for it.
    (let step := (Ir.scaleStepIn doc.page.scale 1000 Ir.footline.step).toNat
     String.join (doc.page.scale.map fun (name, k) =>
       s!"footer.slide-foot .size-{name} \{ font-size: \
{milliFactor (k * 1000 / max step 1)}em; }\n")) else "")

/-- One palette entry as the CSS custom-property declaration `:root`
carries: the definition site a role use's `var(--name, …)` reference
resolves against. This is where a role's palette-dependence lives in the
artifact, so `role_use_is_palette_dependent` is stated over it. -/
def paletteVar (n : String) (c : Ir.Color) : String :=
  "    --" ++ n ++ ": " ++ cssColor c ++ ";"

/-- Every palette entry's declaration line, in declaration order. -/
def paletteVars (p : Ir.Palette) : List String :=
  p.entries.toList.map fun (n, c) => paletteVar n c

private theorem hexDigit_inj :
    ∀ i < 16, ∀ j < 16,
      "0123456789abcdef".toList.getD i '0' = "0123456789abcdef".toList.getD j '0' →
        i = j := by
  decide

private theorem hexByte_inj (a b : UInt8)
    (h : Color.hexByte a false = Color.hexByte b false) : a = b := by
  have hl := congrArg String.toList h
  simp only [Color.hexByte, Bool.false_eq_true, ite_false, String.toList_ofList,
    List.cons.injEq, and_true] at hl
  have ha : a.toNat < 256 := a.toNat_lt
  have hb : b.toNat < 256 := b.toNat_lt
  have hdiv := hexDigit_inj (a.toNat / 16) (by omega) (b.toNat / 16) (by omega) hl.1
  have hmod := hexDigit_inj (a.toNat % 16) (by omega) (b.toNat % 16) (by omega) hl.2
  have : a.toNat = b.toNat := by omega
  exact UInt8.toNat_inj.mp this

/-- Two colours never share a rendered hex form unless they agree as sRGB:
`cssColor` determines the screen-facing components exactly — what makes a
differing `:root` declaration a differing artifact. The CMYK rider is not
determined and not claimed: it is the PDF's declared-model channel
(`cmyk_components_kept`), invisible to this backend by design. -/
theorem cssColor_inj (a b : Ir.Color) (h : cssColor a = cssColor b) :
    a.r = b.r ∧ a.g = b.g ∧ a.b = b.b := by
  have hl := congrArg String.toList h
  simp only [cssColor, Color.css, Color.hexByte, Bool.false_eq_true, ite_false,
    String.toList_append, String.toList_ofList,
    List.cons_append, List.nil_append, List.append_assoc] at hl
  have hl6 := List.append_cancel_left hl
  simp only [List.cons.injEq, and_true] at hl6
  obtain ⟨hr1, hr2, hg1, hg2, hb1, hb2⟩ := hl6
  have har : a.r.toNat < 256 := a.r.toNat_lt
  have hag : a.g.toNat < 256 := a.g.toNat_lt
  have hab : a.b.toNat < 256 := a.b.toNat_lt
  have hbr : b.r.toNat < 256 := b.r.toNat_lt
  have hbg : b.g.toNat < 256 := b.g.toNat_lt
  have hbb : b.b.toNat < 256 := b.b.toNat_lt
  have er1 := hexDigit_inj _ (by omega) _ (by omega) hr1
  have er2 := hexDigit_inj _ (by omega) _ (by omega) hr2
  have eg1 := hexDigit_inj _ (by omega) _ (by omega) hg1
  have eg2 := hexDigit_inj _ (by omega) _ (by omega) hg2
  have eb1 := hexDigit_inj _ (by omega) _ (by omega) hb1
  have eb2 := hexDigit_inj _ (by omega) _ (by omega) hb2
  exact ⟨UInt8.toNat_inj.mp (by omega), UInt8.toNat_inj.mp (by omega),
    UInt8.toNat_inj.mp (by omega)⟩

/-- The good theorem, the contrapositive of "frozen at authoring time": for
a role `r` and palettes that differ at `r`, the emitted `:root` custom
property declarations differ — so a use of `r` renders in the palette's
colour for `r`, because its span references `var(--r, …)`
(`role_use_names_its_token`) and that reference resolves against exactly
this block. A hardcoded `\textcolor{#808080}` cannot satisfy this: it
emits no variable reference and no palette can reach it. Stated over
`paletteVars ∘ Palette.declare` — the palette-to-artifact dependence lives
here, not in the whole `emit` string, whose `intercalate` structure would
only obscure the same fact. -/
theorem role_use_is_palette_dependent (p : Ir.Palette) (r : String)
    (c₁ c₂ : Ir.Color) (hne : (c₁.r, c₁.g, c₁.b) ≠ (c₂.r, c₂.g, c₂.b)) :
    paletteVars (p.declare r c₁) ≠ paletteVars (p.declare r c₂) := by
  simp only [paletteVars, Ir.Palette.declare, Array.toList_push, List.map_append,
    List.map_cons, List.map_nil]
  intro h
  have hlast := List.append_cancel_left h
  simp only [List.cons.injEq, and_true] at hlast
  have hl := congrArg String.toList hlast
  simp only [paletteVar, String.toList_append, List.append_assoc] at hl
  have h1 := List.append_cancel_left hl
  have h2 := List.append_cancel_left h1
  have h3 := List.append_cancel_left h2
  have hrgb := cssColor_inj c₁ c₂ (String.ext (List.append_cancel_right h3))
  exact hne (by simp [hrgb.1, hrgb.2.1, hrgb.2.2])

/-- The synthetic family for a slot: `ltx-body`, `ltx-sans`, `ltx-mono` —
never the face's own name, so an installed font of the same name can never
substitute for the shipped file. -/
def slotName : Nat → String
  | 0 => "body"
  | 1 => "sans"
  | _ => "mono"

/-- The synthetic families face `i` serves: one per slot any of whose
index entries — the standard corners and every declared or used weight —
resolves to it, plus `ltx-math` for the math face. Empty for a face only
per-glyph fallback reaches. -/
def namedFamiliesOf (fs : Font.FontSet) (i : Nat) : List String :=
  ((List.range 3).filterMap fun s =>
    if fs.index.any (fun e => e.1.1 == s && e.2 == i) then
      some s!"ltx-{slotName s}"
    else none) ++
  (if fs.math == some i then ["ltx-math"] else [])

/-- Every face ships under at least one family: the slots' own, or a
fallback family of its own (`ltx-fb<i>`) that the slot stacks append, so
the browser's per-character walk down the family list (CSS Fonts 4 §5.2,
the font matching algorithm runs per character) reaches it — the same
per-scalar recourse the PDF path takes through `FontSet.fallback`. -/
def familiesOf (fs : Font.FontSet) (i : Nat) : List String :=
  if (namedFamiliesOf fs i).isEmpty then [s!"ltx-fb{i}"] else namedFamiliesOf fs i

theorem familiesOf_ne_nil (fs : Font.FontSet) (i : Nat) : familiesOf fs i ≠ [] := by
  unfold familiesOf
  split
  · simp
  · next h => exact fun hn => h (by simp [hn])

/-- A slot's full stack: its own family first, then every other family of
the set in face order, then the honest generic. The browser walks the list
per character (CSS Fonts 4 §5.2), which is the CSS spelling of
`FontSet.fallbackFor` — a glyph the slot's face lacks is set from the
first face that covers it, in the set's own order — so the deck whose
mono face lacks ⟨⟩ reads them from its math face on both pages. -/
def stackFor (fs : Font.FontSet) (own generic : String) : String :=
  let rest := (((List.range fs.fonts.size).flatMap fun i =>
    familiesOf fs i).eraseDups.filter (· != own)).map fun f => s!"\"{f}\""
  String.intercalate ", " ([s!"\"{own}\""] ++ rest ++ [generic])

/-- The face's file name in the sibling fonts directory. The index prefix
makes the name collision-free by construction whatever the faces declare;
the PostScript name, kept to its safe characters, keeps it readable. -/
def fontFileName (i : Nat) (f : Font.Font) : String :=
  let safe := f.psName.toList.filter fun c =>
    c.isAlphanum || c == '-' || c == '_' || c == '.'
  s!"f{i}-{String.ofList safe}." ++ (if f.isCff then "otf" else "ttf")

/-- The browser consumes the resolved font program itself, with the same
OpenType container distinction the PDF embedding reads. -/
def fontResource (f : Font.Font) : HtmlResource.Embedded :=
  { media := if f.isCff then .otf else .ttf, bytes := f.data }

def fontResources (fs : Font.FontSet) : Array HtmlResource.Embedded :=
  (Array.range fs.fonts.size).map fun i => fontResource (fs.get i)

/-- One `@font-face` the page ships: face `index` of the set under one
synthetic family, with the descriptors CSS matches on — the face's own
declared weight and italic flag, never the slot's request, so a family's
Light stays 300 and the browser's matching (CSS Fonts 4 §5.2) does the
rest. -/
structure FontFace where
  index : Nat
  family : String
  weight : Nat
  italic : Bool
  file : String
  format : String
  deriving Repr, BEq

/-- The `@font-face` list of the artifact: every face of the resolved set,
under every synthetic family it serves — the HTML's projection of the one
`FontSet` the PDF embeds from. It never sees layout's used-glyph data, so
it declares the whole set: the superset of the PDF's `keep`, which is what
`Pdf.html_fonts_cover_pdf` states. -/
def shipFaces (fs : Font.FontSet) : Array FontFace :=
  (Array.range fs.fonts.size).flatMap fun i =>
    (familiesOf fs i).toArray.map fun fam =>
      { index := i
        family := fam
        weight := (fs.get i).weight
        italic := (fs.get i).isItalic
        file := fontFileName i (fs.get i)
        format := if (fs.get i).isCff then "opentype" else "truetype" }

/-- Every face of the set is declared: for each index a `@font-face` entry
carries it — the emitter-side half of `Pdf.html_fonts_cover_pdf`. -/
theorem shipFaces_covers (fs : Font.FontSet) {k : Nat} (hk : k < fs.fonts.size) :
    ∃ ff ∈ shipFaces fs, ff.index = k := by
  obtain ⟨fam, rest, heq⟩ : ∃ a l, familiesOf fs k = a :: l := by
    cases h : familiesOf fs k with
    | nil => exact absurd h (familiesOf_ne_nil fs k)
    | cons a l => exact ⟨a, l, rfl⟩
  refine ⟨{ index := k, family := fam, weight := (fs.get k).weight
            italic := (fs.get k).isItalic, file := fontFileName k (fs.get k)
            format := if (fs.get k).isCff then "opentype" else "truetype" }, ?_, rfl⟩
  simp only [shipFaces, Array.mem_flatMap]
  refine ⟨k, by simpa using hk, ?_⟩
  simp only [Array.mem_map, List.mem_toArray]
  exact ⟨fam, by simp [heq], rfl⟩

/-- The font files the emitted page references, as write requests for the
driver (effects as data): the bytes are already in the set, and the file
names are the ones the styling references. One request per face. -/
structure FontAsset where
  file : String
  data : ByteArray

def fontAssets (fs : Font.FontSet) : Array FontAsset :=
  (Array.range fs.fonts.size).map fun i =>
    { file := fontFileName i (fs.get i), data := (fs.get i).data }

/-- What this emitter realizes of the output contract, as values the driver
holds against the document's declaration (`Ir.OutputContract.unmet`):
alternatives as the `alt` attribute, colours sRGB by CSS's definition,
faces shipped beside the page when the document's policy asks
(`shipFaces`), one constant class-gated script, mathematics as MathML
Core. Nothing in `emit` reads this record. -/
def profile : Ir.Realization :=
  { alternatives := .attribute
    color := .srgbByDefinition
    fonts := .ships
    scripting := .constantGated
    math := .mathmlCore }

/-- The undeclared contract is met by this emitter (`_exact`): a document
that declares no contract key gets no W0701 from its page. -/
theorem html_default_contract_exact : ({} : Ir.OutputContract).unmet profile = #[] := by
  decide

/-- Every face declared in CSS embeds a captured font program from the
resolved set. This is an artifact resource fact; the shared face-coverage
contract remains `shipFaces_covers`. -/
theorem shipFaces_src_shipped (fs : Font.FontSet) :
    ∀ ff ∈ shipFaces fs, fontResource (fs.get ff.index) ∈ fontResources fs := by
  intro ff hff
  simp only [shipFaces, Array.mem_flatMap] at hff
  obtain ⟨i, hi, hmem⟩ := hff
  simp only [Array.mem_map, List.mem_toArray] at hmem
  obtain ⟨fam, _, rfl⟩ := hmem
  exact Array.mem_map.mpr ⟨i, hi, rfl⟩

/-! ## Captured image resources

The primary and static media faces are embedded from their captured bytes.
The legacy asset names below remain staging identities for report readers;
they no longer determine a published page's URLs or filesystem writes. -/

/-- One image the page links: the file name it takes beside the page and
the store index it came from — a copy request for the driver (effects as
data), the source path being the store entry's. -/
structure ImageAsset where
  file : String
  srcIndex : Nat
  poster : Bool := false
  deriving Repr, BEq

/-- The last path segment of a source spelling. -/
def basename (p : String) : String := (p.splitOn "/").getLastD p

/-- The path the driver resolved for an entry: graphicx's extension
resolution recorded in `href` when the spelling was bare, else the spelling
itself — the file whose bytes were decoded. -/
def resolvedSrc (en : Image.Loaded) : String :=
  if en.href.isEmpty then en.src else en.href

/-- Which entries copy: a loaded image with a browser face. An SVG's print
face is a PDF form, but its original bytes still belong in the browser.
A PDF may also carry a converted SVG. Boundary pictures publish through
their own list. -/
def imageShips (en : Image.Loaded) : Bool :=
  -- premise: Tests.svgAssetChecks — a failed conversion publishes no source bytes.
  !en.src.startsWith Ir.picSrcPrefix && en.webError.isNone &&
  match en.info with
  | some i => i.form.isNone || Image.isSvg (resolvedSrc en) || en.webSvg.isSome
  | none => false

/-- A converted browser face takes the source's basename with an SVG
extension. The store index still distinguishes different selected pages. -/
def browserAssetSrc (en : Image.Loaded) : String :=
  if en.webSvg.isSome then ((System.FilePath.mk (resolvedSrc en)).withExtension "svg").toString
  else resolvedSrc en

private def imageFileName (kind : String) (k : Nat) (href : String)
    (data : Option ByteArray) : String :=
  let assetPrefix := kind ++ ListMark.arabicN k ++ "-" ++
    (data.map (fun bytes => Flate.contentKey bytes ++ "-")).getD ""
  -- Linux NAME_MAX is 255 bytes. Keep the format extension and a readable
  -- suffix when the content key would push a valid basename over that limit.
  let budget := 255 - assetPrefix.utf8ByteSize
  let base := basename href
  let suffix := if base.utf8ByteSize ≤ budget then base else
    (base.toList.foldr (fun c (used, tail) =>
      let used := used + (String.singleton c).utf8ByteSize
      (used, if used ≤ budget then String.singleton c ++ tail else tail)) (0, "")).2
  assetPrefix ++ suffix

/-- The index keeps distinct requests apart (`imageAssetName_inj`).
Captured bytes add their content key so rebuilding an image changes its
browser cache identity; the basename keeps the file readable. -/
def imageAssetName (k : Nat) (href : String) (data : Option ByteArray := none) : String :=
  imageFileName "i" k href data

/-- The static face has its own namespace: the same entry's moving SVG and
print poster must never overwrite each other. -/
def imagePosterName (k : Nat) (en : Image.Loaded) : String :=
  imageFileName "p" k ((System.FilePath.mk (resolvedSrc en)).withExtension "svg").toString
    en.posterSvg

/-- The copy requests of the page: primary faces in store order, followed
by any static faces selected by print or reduced-motion media. -/
def imageAssets (imgs : Image.Store) : Array ImageAsset :=
  ((Array.range imgs.entries.size).filterMap fun k =>
    (imgs.get? k).bind fun en =>
      if imageShips en then
        some { file := imageAssetName k (browserAssetSrc en) en.browserBytes, srcIndex := k }
      else none) ++
  ((Array.range imgs.entries.size).filterMap fun k =>
    (imgs.get? k).bind fun en =>
      if imageShips en && en.posterSvg.isSome then
        some { file := imagePosterName k en, srcIndex := k, poster := true }
      else none)

/-- File names remain literal on disk. URL path separators survive encoding,
but spaces and commas must not split a `srcset` candidate. -/
def imageAssetHref (assetsDir file : String) : String :=
  toString (Std.Http.URI.EncodedString.encode
    (r := fun c => Std.Http.Internal.Char.isUnreserved c || c == '/'.toUInt8)
    (assetsDir ++ "/" ++ file))

/-- A browser face consists of captured bytes, never a path read again at
publication. Boundary pictures enter through the same converted SVG field. -/
def imageResource? (en : Image.Loaded) : Option HtmlResource.Embedded := do
  if en.webError.isSome || !(imageShips en ||
      (en.src.startsWith Ir.picSrcPrefix && en.webSvg.isSome)) then none else do
    let bytes ← en.browserBytes
    let media := if en.webSvg.isSome || Image.isSvg (resolvedSrc en) then .svg
      else if bytes.extract 0 8 == ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩ then .png else .jpeg
    some { media, bytes }

def imagePosterResource? (en : Image.Loaded) : Option HtmlResource.Embedded := do
  let _ ← imageResource? en
  let bytes ← en.posterSvg
  some { media := .svg, bytes }

def imageResources (imgs : Image.Store) : Array HtmlResource.Embedded :=
  imgs.entries.filterMap imageResource? ++ imgs.entries.filterMap imagePosterResource?

/-- Selection is part of the request key. Missing capture remains unresolved
and is rejected by checked publication; it is never silently omitted. -/
def imageRequestHref (_assetsDir : String) (imgs : Image.Store) (req : Image.Request) : String :=
  match imgs.findRequest? req |>.bind imgs.get? with
  | some en => (imageResource? en |>.map (·.uri)).getD (resolvedSrc en)
  | none => req.src

def imageHref (assetsDir : String) (imgs : Image.Store) (src : String) : String :=
  imageRequestHref assetsDir imgs { src }

/-- The static media source embeds its own captured SVG. -/
def imagePosterHref (_assetsDir : String) (imgs : Image.Store) (req : Image.Request) :
    Option String := do
  let k ← imgs.findRequest? req
  let en ← imgs.get? k
  let r ← imagePosterResource? en
  some r.uri

/-- A length on the CSS ruler, in whole pixels, to nearest: CSS fixes
1in = 72pt = 96px (CSS Values 4 §6.2), so a point reads as 4/3 px — the
ruler a browser measures an SVG's `width="56.693pt"` on, and the unit an
`<img>`'s `width`/`height` attributes are in (HTML §4.8.4.4). Nearest, as
Chromium reports the natural size of that SVG: 76 × 38. -/
def cssPxOfSp (l : Int) : Nat := ((4 * l + 3 * spPerPt / 2) / (3 * spPerPt)).toNat

/-- The pixel count is the nearest one (`_between`): for any length, its
pixel count times the pixel's width in sp lies within half a pixel of it.
Spelled `Int` so `omega` reads it. -/
theorem cssPxOfSp_between (l : Int) (h : 0 ≤ l) :
    3 * spPerPt * (cssPxOfSp l : Int) ≤ 4 * l + 3 * spPerPt / 2 ∧
      4 * l + 3 * spPerPt / 2 < 3 * spPerPt * ((cssPxOfSp l : Int) + 1) := by
  unfold cssPxOfSp
  simp only [spPerPt]
  omega

/-- The size an `<img>` declares, in the CSS pixels a browser measures the
image in: a raster's pixel grid, and a PDF page's box — a boundary
picture's too, whose SVG face carries the same box in pt — on the CSS ruler
(`cssPxOfSp`). A PDF page's pixel fields are its box rounded to whole
points (`Image.probe`: only the dump and the placeholder read them); written
as px they undersized every vector image by a quarter, 56 for a box a
browser draws 76 wide. -/
def intrinsicPx (p : Image.Plan) : Nat × Nat :=
  match p.form with
  | some f => (cssPxOfSp f.val.w, cssPxOfSp f.val.h)
  | none => (p.pxW, p.pxH)

/-- Is this entry a page no browser decodes in an `<img>`? A decoded entry
is a raster or carries an SVG browser face (`imageShips`), or is a
PDF page with no browser face (a form XObject: vector for the PDF artifact,
nothing at all to an `<img>`). A boundary picture ships its SVG face and
is not one. Every other failure — a file that did not load, a boundary picture
with no SVG face — was named where it failed, by a diagnostic whose subject
is the source, so it is not named twice. -/
def pdfPageImg (en : Image.Loaded) : Bool :=
  -- premise: Tests.svgAssetChecks — the SVG face is linked and published.
  !en.src.startsWith Ir.picSrcPrefix && !imageShips en &&
  match en.info with
  | some p => p.form.isSome
  | none => false

/-- The emitted image requests with no browser face, each once, in page
order. The typed node's store index retains page and animation selection;
resolved filenames alone cannot distinguish those requests. -/
def undecodableIndices (imgs : Image.Store) (uses : Array String) : Array Nat :=
  ((uses.filterMap String.toNat?).foldl (fun acc k =>
    if acc.contains k then acc else acc.push k) #[]).filter fun k =>
      (imgs.get? k).any pdfPageImg

/-- W0605: this image has no browser face. A failed conversion retains its
reason; an unconverted PDF retains its format explanation. An emitted use
carries its store index in the subject so distinct requests sharing one
filename remain distinct losses under site accounting. -/
def undecodableDiag (src : String) (reason : Option String := none)
    (index : Option Nat := none) : Diag :=
  Diag.of .W0605
    (match reason with
      | some err => s!"image '{src}' could not produce its browser face: {err}; \
the web page shows a labelled placeholder instead"
      | none => s!"image '{src}' is a PDF page no browser decodes; the web page shows a \
placeholder box instead")
    (subject := some (match index with
      | some k => s!"img:{k}:{src}"
      | none => s!"img:{src}"))
    (help := some (match reason with
      | some _ => "fix the conversion error, or include a PNG export for the web page"
      | none => "for the web page, \\includegraphics a PNG export inside \
\\begin{ifbackend}{html}, and move this include inside \\begin{ifbackend}{pdf}"))

/-- No decimal digit is the separator the asset name is split on. -/
private theorem arabicN_no_dash (k : Nat) : ∀ c ∈ (ListMark.arabicN k).toList, c ≠ '-' := by
  intro c hc heq
  simp only [ListMark.arabicN, String.toList_ofList, List.mem_reverse] at hc
  have := ListMark.digitsRev_digits hc
  subst heq
  simp at this

private theorem dash_split (a a' r r' : List Char)
    (ha : ∀ c ∈ a, c ≠ '-') (ha' : ∀ c ∈ a', c ≠ '-')
    (h : a ++ '-' :: r = a' ++ '-' :: r') : a = a' := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => rfl
    | cons c cs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1.symm (ha' c (List.mem_cons_self ..))
  | cons c cs ih =>
    cases a' with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd h.1 (ha c (List.mem_cons_self ..))
    | cons c' cs' =>
      simp only [List.cons_append, List.cons.injEq] at h
      have := ih cs' (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun x hx => ha' x (List.mem_cons_of_mem _ hx)) h.2
      rw [h.1, this]

/-- Equal asset names come from equal store indices (`_inj`): the index
prefix carries identity, so two sources with one basename in two
directories never collide beside the page. Basenames need not be distinct
and are not claimed to be. -/
theorem imageAssetName_inj {k k' : Nat} {h h' : String} {data data' : Option ByteArray}
    (e : imageAssetName k h data = imageAssetName k' h' data') : k = k' := by
  have hl := congrArg String.toList e
  have hi : "i".toList = ['i'] := rfl
  have hd : "-".toList = ['-'] := rfl
  simp only [imageAssetName, imageFileName, String.toList_append, List.append_assoc, hi, hd,
    List.singleton_append] at hl
  exact ListMark.arabicN_inj (String.ext
    (dash_split _ _ _ _ (arabicN_no_dash k) (arabicN_no_dash k') (List.cons.inj hl).2))

/-- Every shipping entry has an asset row (`_covers`): for each store index
whose entry has a browser face, `imageAssets` carries a request naming it —
the `shipFaces_covers` shape. -/
theorem imageAssets_covers (imgs : Image.Store) {k : Nat} {en : Image.Loaded}
    (hen : imgs.get? k = some en) (hr : imageShips en = true) :
    ∃ a ∈ imageAssets imgs, a.srcIndex = k := by
  refine ⟨{ file := imageAssetName k (browserAssetSrc en) en.browserBytes, srcIndex := k },
    ?_, rfl⟩
  apply Array.mem_append.mpr
  left
  simp only [Array.mem_filterMap]
  refine ⟨k, Array.mem_range.mpr ?_, ?_⟩
  · exact (Array.getElem?_eq_some_iff.mp hen).1
  · simp [hen, hr]

/-- Every embedded primary carrier is drawn from the captured resource
projection. No claim about a directory or subsequent file read is needed. -/
theorem img_request_src_shipped (assetsDir : String) (imgs : Image.Store) (req : Image.Request)
    {k : Nat} {en : Image.Loaded} {r : HtmlResource.Embedded}
    (hk : imgs.findRequest? req = some k) (hen : imgs.get? k = some en)
    (hr : imageResource? en = some r) :
    r ∈ imageResources imgs ∧ imageRequestHref assetsDir imgs req = r.uri := by
  refine ⟨Array.mem_append.mpr (.inl (Array.mem_filterMap.mpr ⟨en, ?_, hr⟩)), ?_⟩
  · exact Array.mem_of_getElem? hen
  · simp [imageRequestHref, hk, hen, hr]

/-- The default request projects the same captured resource guarantee. -/
theorem img_src_shipped (assetsDir : String) (imgs : Image.Store) (src : String)
    {k : Nat} {en : Image.Loaded} {r : HtmlResource.Embedded}
    (hk : imgs.find? src = some k) (hen : imgs.get? k = some en)
    (hr : imageResource? en = some r) :
    r ∈ imageResources imgs ∧ imageHref assetsDir imgs src = r.uri :=
  img_request_src_shipped assetsDir imgs { src } hk hen hr

/-- Every static media carrier embeds the exact captured poster bytes. -/
theorem imagePosterHref_covers (assetsDir : String) (imgs : Image.Store) (req : Image.Request)
    {k : Nat} {en : Image.Loaded} {r : HtmlResource.Embedded}
    (hk : imgs.findRequest? req = some k) (hen : imgs.get? k = some en)
    (hr : imagePosterResource? en = some r) :
    r ∈ imageResources imgs ∧ imagePosterHref assetsDir imgs req = some r.uri := by
  refine ⟨Array.mem_append.mpr (.inr (Array.mem_filterMap.mpr ⟨en, ?_, hr⟩)), ?_⟩
  · exact Array.mem_of_getElem? hen
  · simp [imagePosterHref, hk, hen, hr]

def fontFaceRule (fs : Font.FontSet) (ff : FontFace) : String :=
  s!"@font-face \{ font-family: \"{ff.family}\"; font-weight: {ff.weight}; " ++
  s!"font-style: {if ff.italic then "italic" else "normal"}; " ++
  s!"src: url(\"{(fontResource (fs.get ff.index)).uri}\") format(\"{ff.format}\"); }\n"

/-- The `@font-face` block, one rule per `shipFaces` entry. -/
def fontFaceCss (fs : Font.FontSet) : String :=
  String.join ((shipFaces fs).toList.map (fontFaceRule fs))

/-- The face-shipping rules: every `@font-face`, then the body weight the
document resolved and the synthesis contract. The slot's regular face sets
text, so the request must name that face's weight — a Light body family is
a 300, and the browser's matching (CSS Fonts 4 §5.2) would hand a bare
default `font-weight: 400` the family's Regular instead. And the engine
never fakes a weight or a slant: a missing variant resolves to a real face
or stays upright (`FontSet.lookup`), in both backends — so synthesis is
limited to small caps, which both backends do synthesise (CSS Fonts 4
§font-synthesis; the PDF's is Layout's own, from its GSUB read). Without
this line a title asking for 600 over a 300/400 family renders faux-bold
where the PDF sets the family's real Regular. -/
def fontCss (fs : Font.FontSet) : String :=
  fontFaceCss fs ++
  s!"body \{ font-weight: {(fs.get (fs.lookup 0 400 false)).weight}; " ++
  "font-synthesis: small-caps; }\n"

/-- The generic family closing a slot's stack — what a reader sees only if
the shipped face fails to load. From the face's own declarations: `post`
isFixedPitch is monospace, else OS/2 sFamilyClass (8 = Sans Serif, 1–7 the
serif classes — OpenType spec, OS/2 table, sFamilyClass), else the slot's
declared kind, passed in by the caller who knows which declaration filled
the slot — never a guess from the family name. -/
def genericFor (fs : Font.FontSet) (slot : Nat) (declared : String) : String :=
  let f := fs.get (fs.lookup slot 400 false)
  if f.isFixedPitch then "monospace"
  else if f.familyClass == 8 then "sans-serif"
  else if 1 ≤ f.familyClass && f.familyClass ≤ 7 then "serif"
  else declared

/-- Design tokens become CSS custom properties, so the same declarations drive
both backends and a reader's stylesheet can override them. With a resolved
`FontSet` the slot stacks name only the synthetic families (plus the honest
generic), exactly the faces the sibling directory ships; without one they
name the declared families against the platform, today's degraded state. -/
def tokenVars (cfg : Config) (doc : Doc) : String :=
  let palette := paletteVars doc.palette
  let tokens := doc.tokens.entries.toList.map fun (n, g) =>
    s!"    --{n}: {cssLength g.width};"
  let fonts := match cfg.fonts with
    | some fs =>
      -- The declared kind per slot: in the slides class the text slot is
      -- filled from the sans declaration (beamer user guide §18, the
      -- default font theme is sans serif; the driver resolves it so).
      let bodyDeclared :=
        if doc.docClass == DocClass.slides && doc.fonts.sans.isSome then "sans-serif"
        else "serif"
      let slot (s : Nat) (declared : String) : String :=
        stackFor fs s!"ltx-{slotName s}" (genericFor fs s declared)
      [s!"    --font-body: {slot 0 bodyDeclared};",
       s!"    --font-sans: {slot 1 "sans-serif"};",
       s!"    --font-mono: {slot 2 "monospace"};"] ++
      (if fs.math.isSome then
        [s!"    --font-math: {stackFor fs "ltx-math" "math"};"]
       else [])
    | none =>
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

/-- One scale step as a CSS size: the same table the PDF sets from
(`Ir.sizeScale`), so a heading or a standout is the size the scale says,
never a re-spelled decimal. -/
private def scaleSize (name : String) (unit : String) : String :=
  milliFactor ((Ir.sizeScale.lookup name).getD 1000) ++ unit

/-- Size rules generated from the document's ladder (`Ir.PageSpec.scale`),
so the two backends cannot drift apart on what `\Huge` means — the PDF
resolves the same runs through the same ladder (`Layout`'s flatten state).
`em` rather than `rem`: sizes nest. -/
private def sizeRules (scale : List (String × Nat)) : String :=
  String.join (scale.map fun (name, k) =>
    s!".size-{name} \{ font-size: {milliFactor k}em; }\n")

/-! ### The deck stylesheet, as typed rules

The engine cannot prove what a browser does; it can prove what it emits,
and emit so that correctness does not depend on which features a browser
has. Each deck rule is a value (`DeckRule`) carrying its selector, its
declarations, its feature gate and its media partition; one grouping
emitter (`emitDeckRules`) realizes the `@supports` blocks, the
reduced-motion partition and the print partition; and the guarantees are
theorems quantified over the rule set — `deck_css_partition`,
`floor_is_baseline`, `floor_hides_nothing` with `floor_opacity_mem` and
`floor_covered_script_gated`, `guards_by_construction`,
`snapped_uncovers_every_step`, `snap_pages_partition_frames`,
`deck_text_path_free`, and the two cross-backend ones the overlay rules
owe (`html_step_pending_agree`, `alt_backend_agree`) — so a new rule is
in every contract the moment it is written. Minimal changes by
construction: adding or dropping a feature dependency is one `requires`
field; adding a browser fact is one `Feature` row; nothing else moves.

What stays measured, never proved: Chromium's directional snapping on
key presses, Firefox's lack of scroll-driven timelines, the page-scroll
fraction. Those are browser facts, held by the dated Playwright probes
recorded in PLAN's vertical-deck entry — the oracle, not a theorem. -/

/-- A browser feature the deck's stylesheet gates on. Each constructor
carries its `@supports` test (`Feature.test`), a sourced support note
(`Feature.support`), and the property names and selector fragments whose
meaning depends on it (`Feature.dependsOn`) — the table
`deck_css_partition` is stated over. Registering a feature is one
constructor and one arm in each of the three tables; `all_complete` and
`all_nodup` make a miscount a build failure in both directions. -/
inductive Feature where
  /-- Scroll-driven animations' view progress timelines
  (`animation-timeline: view()`, Scroll-driven Animations 1 §3.1): the
  push and the scrubbed step uncover ride them. -/
  | viewTimeline
  /-- Scroll-state container queries (CSS Conditional 5,
  `container-type: scroll-state`): no rule uses it today; the row stands
  so a rule adopting `scroll-state()` is in the partition contract the
  moment it is written. -/
  | scrollState
  /-- The relational selector `:has()` (Selectors 4 §4.5): no rule uses
  it today — the floor's fragment-driven uncover moved onto the script's
  `data-snapped` attribute — and the row stands so a rule adopting
  `:has()` is in the partition contract the moment it is written. -/
  | has
  deriving Repr, DecidableEq

/-- The `@supports` condition that detects the feature. The `has` test is
`selector()` (CSS Conditional 4 §6.1), itself universal since 2020 —
Chromium 83+, Firefox 69+, Safari 14.1+ (caniuse
`mdn-css_at-rules_supports_selector`, read 2026-09-20) — so an engine old
enough to lack it drops the gated block exactly as it would have dropped
the unparseable selector. -/
def Feature.test : Feature → String
  | .viewTimeline => "(animation-timeline: view())"
  | .scrollState => "(container-type: scroll-state)"
  | .has => "selector(:has(a))"

/-- The sourced support note: engine, version, date — caniuse/MDN, read
2026-09-20. A browser fact lives here, nowhere else. -/
def Feature.support : Feature → String
  | .viewTimeline =>
    "Chromium 115+ (Jul 2023), Safari 26; Firefox release unsupported \
(preview builds only; ESR 140 reports the feature false) — caniuse \
mdn-css_properties_animation-timeline_view, read 2026-09-21"
  | .scrollState =>
    "Chromium 133+ (Feb 2025), no Firefox, no Safari — MDN scroll-state \
container queries / caniuse, read 2026-09-20"
  | .has =>
    "Chromium 105+ (Aug 2022), Firefox 121+ (Dec 2023), Safari 15.4+ \
(Mar 2022) — caniuse css-has, read 2026-09-20"

/-- The exact property names whose meaning depends on the feature. A
capability enters a rule through the property that carries it
(`animation-timeline`, never bare `view(y)`): a value rides its
property, so the scan reads names, not values. -/
def Feature.dependsOnProps : Feature → List String
  | .viewTimeline => ["animation-timeline", "view-timeline", "animation-range"]
  | .scrollState => []
  | .has => []

/-- The selector fragments whose meaning depends on the feature. Every
fragment is digit-free, so it lives whole inside one literal selector
chunk (`SelChunk.lits`). -/
def Feature.dependsOnSel : Feature → List String
  | .viewTimeline => []
  | .scrollState => ["scroll-state("]
  | .has => [":has("]

/-- Every feature, in emission order for the `@supports` blocks. -/
def Feature.all : List Feature := [.viewTimeline, .scrollState, .has]

theorem Feature.all_complete : ∀ f : Feature, f ∈ Feature.all := by
  intro f; cases f <;> simp [Feature.all]

theorem Feature.all_nodup : Feature.all.Nodup := by decide

/-- Does `s` contain `frag`? Spelled over the character list so the
partition proofs evaluate it definitionally. -/
def hasFragAux (pat : List Char) : List Char → Bool
  | [] => pat.isEmpty
  | l@(_ :: t) => pat.isPrefixOf l || hasFragAux pat t

def hasFrag (s frag : String) : Bool := hasFragAux frag.toList s.toList

/-- One chunk of a deck selector: literal syntax, an interpolated
ordinal, or the uncovered-step alternatives of the floor's `:is()`.
Ordinals stay apart from the syntax so the feature scan reads syntax and
never a numeral: every fragment in `Feature.dependsOn` is digit-free and
each syntactic token lives whole in one literal, so scanning
`SelChunk.lits` is scanning the rendered selector. -/
inductive SelChunk where
  | lit (s : String)
  | num (n : Nat)
  /-- The uncovered-step alternatives `.step[data-step="j"], …`: the
  list is the data (`snapped_uncovers_every_step` reads it, through
  `uncoveredBy`), the template renders it. -/
  | stepAlts (js : List Nat)
  /-- One compound per declared attribute value on a class:
  `.step-end[data-step-last="j"], …`, the range ends a snap stands past,
  and the alternation groups a snap selects. The class and the attribute
  are the engine's own constants and digit-free, so the rendered
  selector's syntax still lives whole in the literal chunks; the values
  are the rule's data, read off `Ir.stepPending` (`endedBy`,
  `startedBy`). -/
  | attrAlts (cls attr : String) (js : List Nat)
  deriving Repr, DecidableEq

/-- The literal syntax a chunk renders, ordinals excluded. -/
def SelChunk.lits : SelChunk → List String
  | .lit s => [s]
  | .num _ => []
  | .stepAlts _ => [".step[data-step=\"", "\"], "]
  | .attrAlts cls attr _ => [".", cls, "[", attr, "=\"", "\"], "]

def SelChunk.render : SelChunk → String
  | .lit s => s
  | .num n => toString n
  | .stepAlts js =>
    String.intercalate ", " (js.map fun j => s!".step[data-step=\"{j}\"]")
  | .attrAlts cls attr js =>
    String.intercalate ", " (js.map fun j => s!".{cls}[{attr}=\"{j}\"]")

def renderSel (sel : List SelChunk) : String :=
  String.join (sel.map SelChunk.render)

/-- Where a rule stands in the feature partition: the ungated base, a
feature's `@supports` block, or its `@supports not` block. -/
inductive Gate where
  | base
  | supported (f : Feature)
  | unsupported (f : Feature)
  deriving Repr, DecidableEq

/-- The media partition a rule is emitted into: the screen deck, the
screen deck under `prefers-reduced-motion: reduce` (CSS Media Queries 5
§12.1), the printed deck, or `stage` — both media, the rules that make a
frame a stage wherever it is one: its box, its type, its furniture. The
printed deck is the screen deck's stage paged, reveal.js's `?print-pdf`
without its layout pass: the page is the stage (`deckPageRule`), so a
length stated as a share of the stage means the same on paper. -/
inductive Part where
  | screen
  | reduce
  | print
  | stage
  deriving Repr, DecidableEq

/-- One deck rule — what a string concatenation used to spell, as a
value the deck theorems quantify over. -/
structure DeckRule where
  selector : List SelChunk
  decls : List (String × String)
  requires : Gate := .base
  part : Part := .screen
  deriving Repr, DecidableEq

/-- Does the rule's syntax use something whose meaning depends on `f`?
The scan reads the declared property names by equality
(`Feature.dependsOnProps`) and the selector's literal chunks by
substring (`Feature.dependsOnSel`); a value rides its property. -/
def DeckRule.uses (r : DeckRule) (f : Feature) : Bool :=
  r.decls.any (fun d => f.dependsOnProps.contains d.1) ||
    f.dependsOnSel.any fun frag =>
      (r.selector.flatMap SelChunk.lits).any fun s => hasFrag s frag

/-- One rule's CSS text: `sel { p: v; … }`. A selector that opens blocks
of its own (the keyframes chunks) closes every block it left open — its
opens less the closes it already spelled (the explicit `to` frame rides
the `ltx-uncover` selector). -/
def DeckRule.render (r : DeckRule) : String :=
  let sel := renderSel r.selector
  sel ++ " { " ++
    String.join (r.decls.map fun d => d.1 ++ ": " ++ d.2 ++ "; ") ++
    "}" ++ String.join (List.replicate
      (sel.toList.count '{' - sel.toList.count '}') " }") ++ "\n"

/-- One partition's rules grouped by gate — the one grouping function all
three partitions ride: the base in order, then one `@supports` block per
feature, then the `@supports not` blocks. An empty group emits no block. -/
def emitGates (rules : List DeckRule) : String :=
  let group (g : Gate) := rules.filter (fun r => r.requires == g)
  let block (test : String) (rs : List DeckRule) : String :=
    if rs.isEmpty then "" else
      "@supports " ++ test ++ " {\n" ++
        String.join (rs.map DeckRule.render) ++ "}\n"
  String.join ((group .base).map DeckRule.render) ++
    String.join (Feature.all.map fun f => block f.test (group (.supported f))) ++
    String.join (Feature.all.map fun f =>
      block ("not " ++ f.test) (group (.unsupported f)))

/-- The deck stylesheet from its typed rules: the stage partition under
both media first, then the screen partition with its gates, then the
reduced-motion partition *after* the blocks it reverts (equal specificity,
source order decides — CSS Cascade 5 §6.4), then the print partition.
Every rule is emitted exactly once, in its declared partition and gate;
the Tests deck block pins the declaration multiset against the typed
set. -/
def emitDeckRules (rules : List DeckRule) : String :=
  let part (p : Part) := rules.filter (fun r => r.part == p)
  "@media screen, print {\n" ++ emitGates (part .stage) ++ "}\n" ++
  "@media screen {\n" ++
    emitGates (part .screen) ++
    "@media (prefers-reduced-motion: reduce) {\n" ++
      emitGates (part .reduce) ++ "}\n" ++
    "}\n" ++
  "@media print {\n" ++ emitGates (part .print) ++ "}\n"

/-- The deck glides between snap pages; `guards_by_construction` holds
its reduced-motion counterpart (`deckGlideGuard`) to it — the base
stylesheet's global reduce block covers `animation` and `transition`
only, and `scroll-behavior` is neither (WCAG 2.2 SC 2.3.3, technique
C39). -/
def deckGlideRule : DeckRule :=
  { selector := [.lit "html"], decls := [("scroll-behavior", "smooth")] }

/-- The one snap door: every snap area of the deck — a stepless frame's
section, a section page, a stepped frame's spacers — carries `data-snap`
at emission, and this ungated rule is the only place the deck declares
snap alignment (CSS Scroll Snap 1 §4.1 `scroll-snap-align`, §4.3
`scroll-snap-stop: always` so a fling cannot skip a page). The keyboard
script reads the same attribute (`deckScript` queries `[data-snap]`), so
the stylesheet and the script cannot name different snap points — and no
two snap areas can start at one offset, the old horizontal row's
torn-page suspect: the sticky stage never carries the attribute. -/
def deckSnapDoor : DeckRule :=
  { selector := [.lit "[data-snap]"]
    decls := [("scroll-snap-align", "start"), ("scroll-snap-stop", "always")] }

/-- The frame's logo corner: `.slide-logo` spans the stage's safe-area
content box, pinned to its bottom — the furniture band the PDF lays the
logo into at the page's bottom margin — and distributes its content
horizontally by the declared alignment, which rides the element's own
inline style (`Ir.logoAlign`: `flex-end`, beamer's lower-right default,
unless the document styles it). The stage anchors the strip
(`deckStageRule`'s `position: relative`; a stepped track's sticky stage
is a positioned box already), so the logo stands with its frame on every
snap page, as the PDF repeats it on every page of the frame. -/
def deckLogoRule : DeckRule :=
  { selector := [.lit ".slide-logo"]
    decls := [("position", "absolute"), ("bottom", safeareaVar),
      ("left", safeareaVar), ("right", safeareaVar), ("display", "flex")]
    part := .stage }

/-- The stage's ground and ink: the declared pair in force where the stage
stands — the document's (`:root`, `paletteVars`) or a body epoch's (the
node's own inline redefinition, `withEpoch`; custom properties inherit) —
and the stylesheet's own surface and ink only where nothing is declared.
The value reveal.js spells per slide as `data-background-color` is the
declaration this engine already has, the `bg` of the palette in force, so
a frame's ground is data both backends read, never a stylesheet constant:
painting `--surface` whatever the document declared shipped a dark
declared ground as light ink on a light stage, and a theme's dark ink on
the dark scheme's surface. -/
def stageGround : String := "var(--bg, var(--surface))"

/-- The stage's ink, paired with `stageGround`: `color` is computed where it
is declared, so a body epoch's `--fg` redefined on the stage reaches its text
only through a declaration on the stage itself. -/
def stageInk : String := "var(--fg, var(--ink))"

/-- Every frame fills the viewport as one opaque column of the row:
`100vw` wide (exactly the scrollport — the root clips y, so no scrollbar
narrows the viewport under it), one stage tall, its ground and ink the
declared pair in force (`stageGround`, `stageInk`) — opaque on every path,
the user's own rule — and content that spills the stage stays reachable
through the frame's own scroll (`overflow-y: auto`; the scrollbar is the
visible control, the honest floor). Paper has no scroll, so print lifts
the bound and the stage grows onto the next sheet
(`print_lifts_stage_bounds_covers`). `position: relative` anchors the
stage's own furniture (`deckLogoRule`); in a stepped track the sticky
override (`stepStageRule`, higher specificity) is a positioned box
already. -/
def deckStageRule : DeckRule :=
  { selector := [.lit "section.slide, section.section-page"]
    decls := [("width", "100vw"), ("flex", "0 0 100vw"),
      ("height", "100dvh"), ("overflow-y", "auto"),
      ("background", stageGround), ("color", stageInk), ("display", "flex"),
      ("flex-direction", "column"), ("padding", safeareaVar),
      ("position", "relative")]
    part := .stage }

/-- The deck's base screen rules — the floor every browser gets, no
feature gate anywhere. The scroll space is horizontal and snaps
mandatorily on the root (`html` carries `scroll-snap-type`, which UAs
apply to the viewport — Scroll Snap 1 §4.1): frames stand `100vw` wide
in a row, → is next — ←/→, Shift+wheel and a swipe page it natively, the
constant script (`deckScript`) binds the rest of the keys — and the
scroll itself is the motion, the physical reading of "the next slide";
the title band never moves because every frame's band sits at the same
y. One press lands one page: §6.1–6.2 (paging and arrow scrolls carry an
intended direction and must ignore the starting snap position,
`scroll-snap-stop: always` on the door) plus the root's `overflow-y:
clip` — the deck never scrolls vertically, so no scrollbar can steal
width from `100vw` and every snap area is exactly one scrollport wide
(CSS Overflow 3 §3.1; fractional snap widths were the old row's
several-presses suspect). The deck fills the viewport: type is set on
`main` in `vh` — the PDF's own fontSize/stage-height ratio
(`deck_type_is_stage_ratio`) — so every slide scales from the stage, and
the headings retake their scale steps in `em` to ride the same base.
`align-items: flex-start` keeps one frame's box its own. A section page
owns a whole page of the deck, its title and bar centred on both axes
(its own rule: a frame's children must keep the full slide width). -/
def deckBase (bodyVh : String) : List DeckRule :=
  [ { selector := [.lit "html"]
      decls := [("scroll-snap-type", "x mandatory"), ("overflow-y", "clip")] },
    deckGlideRule,
    { selector := [.lit "body"], decls := [("padding", "0")], part := .stage },
    { selector := [.lit "main"]
      decls := [("max-width", "none"), ("margin", "0"), ("font-size", bodyVh)]
      part := .stage },
    { selector := [.lit "main"]
      decls := [("display", "flex"), ("align-items", "flex-start")] },
    deckStageRule,
    deckSnapDoor,
    deckLogoRule,
    { selector := [.lit "section.section-page"]
      decls := [("justify-content", "center"), ("align-items", "center")]
      part := .stage },
    { selector := [.lit "h1"], decls := [("font-size", scaleSize "LARGE" "em")]
      part := .stage },
    { selector := [.lit "h2"], decls := [("font-size", scaleSize "Large" "em")]
      part := .stage },
    { selector := [.lit "h3"], decls := [("font-size", scaleSize "large" "em")]
      part := .stage },
    { selector := [.lit "section.slide > header"]
      decls := [("max-height", titlebandVar)], part := .stage },
    { selector := [.lit "section.slide > header h2"]
      decls := [("font-size", scaleSize "Large" "em")], part := .stage } ]

/-- `deckGlideRule`'s reduced-motion counterpart: the deck pages jump
instead of gliding. -/
def deckGlideGuard : DeckRule :=
  { selector := [.lit "html"], decls := [("scroll-behavior", "auto")]
    part := .reduce }

/-- The deck-wide reduced-motion partition. The base row carries no
animation — the scroll is the motion, and the reader's own scroll is
never taken away (WCAG 2.2 SC 2.3.3) — so only the glide needs a guard;
the stepped track's reverts live with the step rules (`stepFixed`). -/
def deckReduce : List DeckRule := [deckGlideGuard]

/-- The stepped track, gated on `view()` timelines: a frame with N
overlay steps (`Ir.frameSteps`) is one sticky stage over N snap
spacers. The `.slide-track` wrapper is `N × 100vw` wide — a flex row of
its stage and N spacers — and declares the frame's named view progress
timeline (`view-timeline: --frame x`, Scroll-driven Animations 1 §3.4;
§4.2: descendants find the name, and the steps are descendants). -/
def stepTrackRule : DeckRule :=
  { selector := [.lit ".slide-track"]
    decls := [("display", "flex"), ("align-items", "flex-start"),
      ("width", "calc(var(--steps) * 100vw)"),
      ("flex", "0 0 calc(var(--steps) * 100vw)"),
      ("view-timeline", "--frame x")]
    requires := .supported .viewTimeline }

/-- The stage rides its track sticky at the scrollport's left edge (CSS
Positioned Layout 3 §3.4: insets from the nearest scrollport keep the
box in view *within its containing block*, so the stage pins while its
spacers scroll underneath — an arrow press advances one snap point and
the stage does not move; the scroll offset does — and the stage can
never paint over a neighbouring frame: the inset moves a sticky box only
within its own track). `margin-right: -100vw` lays the spacers under the
stage, so spacer k's snap position is `(k−1)·100vw` into the track; the
stage itself carries no snap alignment — only `[data-snap]` elements do
(`deckSnapDoor`) — so no two snap areas share the track's first
offset. -/
def stepStageRule : DeckRule :=
  { selector := [.lit ".slide-track > section.slide"]
    decls := [("position", "sticky"), ("left", "0"),
      ("margin-right", "-100vw")]
    requires := .supported .viewTimeline }

/-- The spacers' geometry on the timeline path: each is one scrollport
wide — the snap area the door rule aligns — and one stage tall, so the
area is never degenerate. -/
def stepSnapSize : DeckRule :=
  { selector := [.lit ".snap"]
    decls := [("flex", "0 0 100vw"), ("height", "100dvh")]
    requires := .supported .viewTimeline }

/-- The uncover's keyframes, gated with the timeline that plays them: a
covered step stands at the design's covered fraction as an opacity (dim,
never hide; the whole step including its own coloured runs, as the PDF's
per-run cover dims every ink), offset by `--motiondistance` in the
direction of travel, and the explicit `to` endpoint restores full
opacity and `transform: none` — the active state is declared, never
synthesized from the normal style (the user's own rule). Keyframes are
keyed by their offset, not source order, so `to` rides the selector
chunk and `from` stays the declaration list `floor_opacity_mem` reads.
Opacity and transform only: neither reflows, so the frame's layout is
fixed from the first paint (CSS Transforms 1 §3). Not
`color: color-mix(… currentColor …)`: inside a keyframe, Chromium
resolves `currentColor` for the `color` property against the element's
own colour, so that from-state equals the to-state and nothing dims — a
rendered probe showed it. Opacity composites in sRGB where the PDF mixes
in Oklab; the same declared fraction, two blends — the divergence PLAN
already names for the covered shade. -/
def stepKeyframes (coveredPct : Nat) : DeckRule :=
  { selector := [.lit "@keyframes ltx-uncover \
{ to { opacity: 100%; transform: none } from"]
    decls := [("opacity", s!"{coveredPct}%"),
      ("transform", "translateX(var(--motiondistance, 1rem))")]
    requires := .supported .viewTimeline }

/-- The steps' uncover, paced by the reader's own paging key: a `.step`
(`--step: n`, the track `--steps: N`) animates to place over
`animation-range: contain (n−2)/(N−1) → contain (n−1)/(N−1)`
(Scroll-driven Animations 1 §3.1: for a subject wider than the
scrollport, `contain` 0% is the earliest edge-coincident position —
snap 1 — and 100% the latest — snap N; the appendix's `animation-range`
takes `<length-percentage>`, explicitly including `calc()`, and the
unitless-custom-property calc is verified against this engine's
Chromium). So item n fades in *during* the smooth scroll from snap n−1
to snap n and holds (fill-mode both). Step 1 items are never covered
(`:not([data-step="1"])`). The range's *end* is not this rule's: a
declared end covers again past itself, on the nested carrier
(`stepRecoverRule`). -/
def stepUncoverRule : DeckRule :=
  { selector := [.lit ".step:not([data-step=\"1\"])"]
    decls := [("animation", "ltx-uncover linear both"),
      ("animation-timeline", "--frame"),
      ("animation-range",
        "contain calc((var(--step) - 2) / (var(--steps) - 1) * 100%) \
contain calc((var(--step) - 1) / (var(--steps) - 1) * 100%)")]
    requires := .supported .viewTimeline }

/-- The floor's spacer collapse: without `view()` timelines the track
geometry never applies and the spacers hide — the stepped frame is one
page like any other (`snap_pages_partition_frames`). -/
def stepSnapHide : DeckRule :=
  { selector := [.lit ".snap"], decls := [("display", "none")]
    requires := .unsupported .viewTimeline }

/-- With spacers hidden, the track is the frame's stable snap box. The
inner stage is sticky: its moving snap area can keep backward-then-forward
navigation on the preceding frame. -/
def stepTrackFloorSnap : DeckRule :=
  { selector := [.lit ".slide-track"]
    decls := [("scroll-snap-align", "start"), ("scroll-snap-stop", "always")]
    requires := .unsupported .viewTimeline }

/-- The floor's covered default, gated on the deck script's presence:
`deckScript` marks `<html data-deck-script>` at startup, and only under
that marker do steps start covered on the floor — the script's
`data-snapped` is the floor's only uncover (`stepSnappedRule`), so with
scripting off nothing may be dimmed that nothing can restore
(`floor_covered_script_gated`): the declarative floor survives the
script's absence at full colour, ←/→ still paging by snap. -/
def stepFloorCovered (coveredPct : Nat) : DeckRule :=
  { selector := [.lit "html[data-deck-script] .step:not([data-step=\"1\"])"]
    decls := [("opacity", s!"{coveredPct}%")]
    requires := .unsupported .viewTimeline }

/-- The steps a floor snap `k` uncovers: every step `2..k` (step 1 is
never covered). The list is the selector's own data — the `:is()`
alternatives render from it — so `snapped_uncovers_every_step` reads the
uncover set the browser reads. -/
def uncoveredBy (k : Nat) : List Nat := (List.range (k - 1)).map (· + 2)

/-- The floor's uncover for snap `k`: the script sets `data-snapped="k"`
on a stepped frame's track when its k-th snap point is current
(`deckScript`), and this rule uncovers every step `j ≤ k` of that frame
— and only that frame's (the attribute lives on the track). Emission
knows the deck's maximum step count, so the rules are spelled
numerically — no `calc()`, no `:has()`, nothing for a fallback engine to
resolve. Outranks the covered default by specificity — two classes and
two attributes against one type, one class and two attributes — so the
gate grouping moves no outcome. -/
def stepSnappedRule (k : Nat) : DeckRule :=
  { selector := [.lit ".slide-track[data-snapped=\"", .num k,
      .lit "\"] :is(", .stepAlts (uncoveredBy k), .lit ")"]
    decls := [("opacity", "100%")]
    requires := .unsupported .viewTimeline }

def stepSnapped (maxSteps : Nat) : List DeckRule :=
  (List.range (maxSteps - 1)).map fun i => stepSnappedRule (i + 2)

/-! ### The range's other end

`\uncover<2-3>` is pending past its end as much as before its start
(`Ir.stepPending`), and the PDF handout dims it again on step 4. The
uncover above reads the start alone, so until these rules the two
artifacts disagreed on every declared end: crisp in HTML, dimmed on
paper. The end's covering is a second wrapper, not a second declaration
on the same one, because one element animates one property once — two
opacity animations compose only by nesting, and opacities multiply, so
covered-before-the-start times covered-again-past-the-end is exactly the
predicate. -/

/-- The recover's keyframes, gated with the timeline that plays them: the
mirror of `stepKeyframes` with the offsets swapped — full colour at the
range's end, the design's covered fraction past it. Opacity only: the
step dims in place, as the PDF's per-run cover does, and the uncover's
`transform` has already landed at `none` by the time this plays. -/
def stepRecoverKeyframes (coveredPct : Nat) : DeckRule :=
  { selector := [.lit "@keyframes ltx-recover { from { opacity: 100% } to"]
    decls := [("opacity", s!"{coveredPct}%")]
    requires := .supported .viewTimeline }

/-- The declared end's carrier, paced by the same reader's key as the
uncover: a `.step-end` (`--step-last: u`, the track `--steps: N`) dims
over `animation-range: contain (u−1)/(N−1) → contain u/(N−1)` — the snap
interval *after* the range's last step, so the step holds full colour
through `u` and fades as the reader leaves it. An end at the deck's last
step puts the range start at 100%: the animation then fills with its
`from` state throughout and nothing dims, which is the honest reading —
no step past it exists. -/
def stepRecoverRule : DeckRule :=
  { selector := [.lit ".step-end"]
    decls := [("animation", "ltx-recover linear both"),
      ("animation-timeline", "--frame"),
      ("animation-range",
        "contain calc((var(--step-last) - 1) / (var(--steps) - 1) * 100%) \
contain calc(var(--step-last) / (var(--steps) - 1) * 100%)")]
    requires := .supported .viewTimeline }

/-- The `data-step-last` values a snap stands past, read off the predicate
itself: `Ir.stepPending 1 (some u) k` is `k > u`, so the enumeration is
the engine's own pending test and not a second spelling of it. Bounded by
the deck's step count, which is what makes the enumeration complete
(`html_step_pending_agree`). -/
def endedBy (maxSteps k : Nat) : List Nat :=
  ((List.range maxSteps).map (· + 1)).filter fun u => Ir.stepPending 1 (some u) k

/-- The floor's recover for snap `k`: with no `view()` timeline the script's
`data-snapped` is the deck's step state, and every declared end below `k`
dims its wrapper again — the floor's mirror of `stepSnappedRule`.
Script-gated like the covered default it completes: with scripting off no
snap state exists, so nothing here is declared and the floor stands at full
colour (`floor_covered_script_gated`). Outranks nothing and is outranked by
nothing: the uncover it corrects addresses `.step`, this addresses the
nested `.step-end`, and the two opacities multiply. -/
def stepRecoverFloorRule (coveredPct maxSteps k : Nat) : DeckRule :=
  { selector := [.lit "html[data-deck-script] .slide-track[data-snapped=\"", .num k,
      .lit "\"] :is(", .attrAlts "step-end" "data-step-last" (endedBy maxSteps k),
      .lit ")"]
    decls := [("opacity", s!"{coveredPct}%")]
    requires := .unsupported .viewTimeline }

def stepRecovered (coveredPct maxSteps : Nat) : List DeckRule :=
  (List.range (maxSteps - 1)).map fun i => stepRecoverFloorRule coveredPct maxSteps (i + 2)

/-- The end carrier's reduced-motion guard, at its own selector: no
animation, full colour (WCAG 2.2 SC 2.3.3), as `stepGuard` is the
uncover's. -/
def stepRecoverGuard : DeckRule :=
  { selector := [.lit ".step-end"]
    decls := [("opacity", "100%"), ("animation", "none")]
    part := .reduce }

/-- The floor recover's reduced-motion counterpart. Under reduce a stepped
frame is one page, so its snap state is the frame's own and no end is past;
this rule says so at the floor recover's own specificity — one element, one
attribute, one class-and-attribute, one `:is()` compound — and the reduce
partition is emitted after the blocks it reverts, so source order decides
(CSS Cascade 5 §6.4). -/
def stepRecoverFloorGuard : DeckRule :=
  { selector := [.lit "html[data-deck-script] .slide-track[data-snapped] \
:is(.step-end[data-step-last])"]
    decls := [("opacity", "100%")]
    part := .reduce }

/-- Whether the emitted rules leave step `(n, last)` covered at snap `k`,
from the selectors' own data and nothing else: the uncover has not reached
its start (`n ∉ uncoveredBy k`, and step 1 is never covered) or the recover
has passed its declared end (`endedBy`). The HTML side of the covering
agreement — what a reader of the stylesheet can compute, against what the
PDF page computes. -/
def htmlStepPendingAt (maxSteps n : Nat) (last : Option Nat) (k : Nat) : Bool :=
  (!(n == 1) && !((uncoveredBy k).contains n)) ||
    (match last with
     | some u => (endedBy maxSteps k).contains u
     | none => false)

/-- The covering agreement, one range at a time: on every step of a deck
whose declared ends fit its step count, the HTML rules cover exactly the
steps `Ir.stepPending` calls pending — the predicate the PDF handout dims
by. Before these rules the two artifacts disagreed past every declared
end, `\uncover<2-3>` standing crisp on step 4 in HTML and dimmed on paper.
`_agree`'s grade: two projections of the one IR predicate, the enumeration
bounds carried as the hypotheses that make the selectors' numeric spelling
complete. -/
theorem html_step_pending_agree (maxSteps n k : Nat) (last : Option Nat)
    (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hlast : ∀ u, last = some u → 1 ≤ u ∧ u ≤ maxSteps) :
    htmlStepPendingAt maxSteps n last k = Ir.stepPending n last k := by
  have hstart : ∀ m, m ∈ uncoveredBy k ↔ (2 ≤ m ∧ m ≤ k) := by
    intro m
    simp only [uncoveredBy, List.mem_map, List.mem_range]
    exact ⟨fun ⟨i, hi, hm⟩ => by omega, fun h => ⟨m - 2, by omega, by omega⟩⟩
  have hend : ∀ u, u ∈ endedBy maxSteps k ↔ (1 ≤ u ∧ u ≤ maxSteps ∧ u < k) := by
    intro u
    simp only [endedBy, List.mem_filter, List.mem_map, List.mem_range,
      Ir.stepPending, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨⟨i, hi, hu⟩, hp⟩ => by omega,
      fun h => ⟨⟨u - 1, by omega, by omega⟩, by omega⟩⟩
  rw [Bool.eq_iff_iff]
  cases last with
  | none =>
    simp only [htmlStepPendingAt, Ir.stepPending, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq, List.contains_eq_mem,
      decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq, hstart,
      Bool.false_eq_true, or_false]
    omega
  | some u =>
    have hu := hlast u rfl
    simp only [htmlStepPendingAt, Ir.stepPending, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq, List.contains_eq_mem,
      decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq, hstart, hend]
    omega

/-- The steps' reduced-motion guard: no step animates and every step
stands at full colour (WCAG 2.2 SC 2.3.3; the base sheet's global reduce
block strips every animation with `!important` — the standing contract —
and the criterion permits removing more than the motion). -/
def stepGuard : DeckRule :=
  { selector := [.lit ".step"]
    decls := [("opacity", "100%"), ("animation", "none")]
    part := .reduce }

/-- The covered default's own reduced-motion counterpart, at its exact
selector: the reduce partition is emitted after the `@supports` blocks
it reverts, so at equal specificity source order decides (CSS Cascade 5
§6.4) and the floor too stands at full colour under reduce. -/
def stepCoveredGuard : DeckRule :=
  { selector := [.lit "html[data-deck-script] .step:not([data-step=\"1\"])"]
    decls := [("opacity", "100%")]
    part := .reduce }

/-- The track's reduced-motion reverts: one page per stepped frame — the
spacers collapse (their presses would be dead with the fade gone), the
track takes one viewport and keeps the frame's snap. -/
def stepTrackWidthReduce : DeckRule :=
  { selector := [.lit ".slide-track"]
    decls := [("width", "100vw"), ("flex", "0 0 100vw")]
    part := .reduce }

def stepSnapReduceHide : DeckRule :=
  { selector := [.lit ".snap"], decls := [("display", "none")]
    part := .reduce }

def stepTrackSnapReduce : DeckRule :=
  { selector := [.lit ".slide-track"]
    decls := [("scroll-snap-align", "start"), ("scroll-snap-stop", "always")]
    part := .reduce }

/-! ### Alternation, selected declaratively

`Ir.Inline.alt`/`Ir.Block.alt` hold two groups and the page inks one
(`Ir.altShowsFirst`). Both groups stand in the tree — the document
declares both, and a stylesheet cannot choose what was never emitted —
so the deck selects one per step with `display`, which is a different
mechanism from `step`'s covering and stays one: a covered step is
content awaiting its turn, at the design's covered fraction; an
unselected group is content this page does not have, and has no box at
all. The group stored first needs no rule to be seen — step 1 inks it
(`Ir.altShowsFirst_id`), so the emitter marks the other `hidden`, which
is what a page with no snap state, no script, no stylesheet, or a print
sheet shows. -/

/-- The `data-step` values a snap has reached, read off the predicate
itself: a start is reached at `k` exactly when nothing is pending before
it (`Ir.stepPending n none k` is `k < n`). A start of 1 is in the set,
unlike `uncoveredBy`'s — an alternation selects from step 1 on, where a
step's covering has nothing to do. -/
def startedBy (maxSteps k : Nat) : List Nat :=
  ((List.range maxSteps).map (· + 1)).filter fun n => !Ir.stepPending n none k

/-- Snap `k` shows the crisp side of every alternation whose start it has
reached. `display: contents` rather than a box value: the wrapper is a
carrier, and its group's content must flow exactly as it flows on the
pages that need no rule at all. -/
def altStartCrispRule (maxSteps k : Nat) : DeckRule :=
  { selector := [.lit ".slide-track[data-snapped=\"", .num k, .lit "\"] :is(",
      .attrAlts "alt-crisp" "data-step" (startedBy maxSteps k), .lit ")"]
    decls := [("display", "contents")] }

/-- The same snap hides the pending side of those alternations: exactly one
group of a node is shown, by construction of the two selectors over one
enumeration. -/
def altStartPendingRule (maxSteps k : Nat) : DeckRule :=
  { selector := [.lit ".slide-track[data-snapped=\"", .num k, .lit "\"] :is(",
      .attrAlts "alt-pending" "data-step" (startedBy maxSteps k), .lit ")"]
    decls := [("display", "none")] }

/-- Past a declared end the sides swap back — the complement of a mid-deck
range is two ranges, which is why alternation needs a node and not a pair
of steps. The correction carries `html`, one element name more than the
start rules, so it outranks them whatever order they are emitted in (CSS
Selectors 4 §17). -/
def altEndCrispRule (maxSteps k : Nat) : DeckRule :=
  { selector := [.lit "html .slide-track[data-snapped=\"", .num k, .lit "\"] :is(",
      .attrAlts "alt-crisp" "data-step-last" (endedBy maxSteps k), .lit ")"]
    decls := [("display", "none")] }

def altEndPendingRule (maxSteps k : Nat) : DeckRule :=
  { selector := [.lit "html .slide-track[data-snapped=\"", .num k, .lit "\"] :is(",
      .attrAlts "alt-pending" "data-step-last" (endedBy maxSteps k), .lit ")"]
    decls := [("display", "contents")] }

/-- The four rules one snap needs: the start reached, then the end passed. -/
def altSnapRules (maxSteps k : Nat) : List DeckRule :=
  [altStartCrispRule maxSteps k, altStartPendingRule maxSteps k,
   altEndCrispRule maxSteps k, altEndPendingRule maxSteps k]

def altSnapped (maxSteps : Nat) : List DeckRule :=
  (List.range (maxSteps - 1)).flatMap fun i => altSnapRules maxSteps (i + 2)

/-- Under reduce a stepped frame is one page (`stepSnapReduceHide`), so its
alternations show step 1's reading: the `hidden` the emitter wrote,
restored at the snap rules' own specificity — and the reduce partition
stands after the blocks it reverts, so source order decides (CSS Cascade 5
§6.4). -/
def altReduceHiddenRule : DeckRule :=
  { selector := [.lit "html .slide-track[data-snapped] .alt[hidden]"]
    decls := [("display", "none")]
    part := .reduce }

def altReduceShownRule : DeckRule :=
  { selector := [.lit "html .slide-track[data-snapped] .alt:not([hidden])"]
    decls := [("display", "contents")]
    part := .reduce }

def altReduceFixed : List DeckRule := [altReduceHiddenRule, altReduceShownRule]

/-- Every rule alternation adds, shipped with the step rules. -/
def altRules (maxSteps : Nat) : List DeckRule :=
  let snapped := altSnapped maxSteps
  altReduceFixed ++ snapped

/-- Which group the emitted rules select at snap `k`, from their own data
and the side the emitter tagged the group with: the pending test the start
and end families implement (`htmlStepPendingAt`), compared against
`Ir.altFirstWhenPending`. The HTML projection of `Ir.altShowsFirst`. -/
def altShownFirstAt (maxSteps n : Nat) (last : Option Nat) (k : Nat) : Bool :=
  htmlStepPendingAt maxSteps n last k == Ir.altFirstWhenPending n last

/-- **`alt_backend_agree`** (`_agree`): the two artifacts ink the same
group on the same step. Both sides are projections of the one IR
predicate — the PDF page tests `Ir.altShowsFirst` where it inks
(`Layout.flattenOne` and `Layout.collectBlock`'s `.alt` arms, whose leaf
identity is `Struct.alt_leaf_projects`), and the HTML deck tests
`Ir.stepPending` in its per-snap selectors against the side page order
put the group on, which is the predicate's own factorization
(`Ir.altShowsFirst_side`). An artifact that decided this for itself could
disagree with the other and no theorem would notice; this is why the
decision is a definition and each backend reads it rather than repeating
it. The bounds are the hypotheses that make the selectors' numeric
spelling complete over the deck's steps. -/
theorem alt_backend_agree (maxSteps n k : Nat) (last : Option Nat)
    (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hlast : ∀ u, last = some u → 1 ≤ u ∧ u ≤ maxSteps) :
    altShownFirstAt maxSteps n last k = Ir.altShowsFirst n last k := by
  rw [altShownFirstAt, html_step_pending_agree maxSteps n k last hn hk hlast,
    Ir.altShowsFirst_side]

/-- The step rules with a closed spelling — every one whose value reads
no parameter, checkable in one `decide`. -/
def stepFixed : List DeckRule :=
  [stepTrackRule, stepStageRule, stepSnapSize, stepUncoverRule,
   stepRecoverRule, stepSnapHide, stepTrackFloorSnap, stepGuard,
   stepRecoverGuard, stepCoveredGuard, stepRecoverFloorGuard,
   stepTrackWidthReduce, stepSnapReduceHide, stepTrackSnapReduce]

/-- Every rule the steps add, shipped exactly when the deck has steps —
a stepless deck has nothing to reveal and no track to lay out. -/
def stepRules (coveredPct maxSteps : Nat) : List DeckRule :=
  stepKeyframes coveredPct :: stepRecoverKeyframes coveredPct ::
    stepFloorCovered coveredPct ::
    (stepFixed ++ stepSnapped maxSteps ++ stepRecovered coveredPct maxSteps)

/-- The printed deck's page: the stage the PDF pages on, as `@page`'s
size with no margin — reveal.js's print export without its layout pass.
The size is the PDF's own MediaBox in CSS `pt` (the engine's point is
PostScript's, 1/72 in, and `Sp.toPtString` is the formatter `Pdf.ptObj`
writes the box with — `deckPageSize` — so the two artifacts' pages are one
value printed twice). With the page area the stage, every length the deck
states as a share of the stage (`deckStageMilli`, in `vw`/`dvh`) and the
stage-ratio type in `vh` mean on paper what they mean on screen (CSS
Values 4 §6.1.2: in paged media the viewport-percentage lengths are
relative to the page area). -/
def deckPageRule (size : String) : DeckRule :=
  { selector := [.lit "@page"], decls := [("size", size), ("margin", "0")]
    part := .print }

/-- The page size `deckPageRule` declares, from the document's stage: the
two numbers `Pdf.ptObj` writes the MediaBox with. -/
def deckPageSize (page : PageSpec) : String :=
  s!"{page.width.toPtString}pt {page.height.toPtString}pt"

/-- A stage on paper: it opens and ends its sheet, and it grows with its
content instead of clipping it — `height` and `overflow-y` lifted
(`print_lifts_stage_bounds_covers`), one sheet tall at least
(`min-height`), so a frame that fits still fills its sheet, its declared
distribution and its furniture where the screen puts them. The break
before a stage keeps it off a sheet that content outside any stage
opened (an unthemed deck's section heading stands on its own sheet, as
it did while a stage could not split). A frame that runs long breaks
between its lines onto the next sheet, as the PDF's continuation pages
do, and each continuation opens below the stage's safe area on its own
ground (`box-decoration-break: clone`, CSS Fragmentation 3 §5.4). The
ground is the author's, not decoration a reader's toner setting may drop
(`print-color-adjust: exact`, CSS Color Adjustment 1 §3.1). What the PDF
adds on a continuation page and a sheet cannot is the frame's title band
and footer: the HTML has no layout pass to know where a sheet breaks, so
each stands once, where the frame opens and where it ends. -/
def printStageRule : DeckRule :=
  { selector := [.lit "section.slide, section.section-page"]
    decls := [("break-after", "page"), ("break-before", "page"), ("height", "auto"),
      ("min-height", "100dvh"), ("overflow-y", "visible"),
      ("box-decoration-break", "clone"), ("print-color-adjust", "exact")]
    part := .print }

/-- The sheet's own ground: where a frame's last continuation leaves its
sheet unfilled, the page shows the stage's ground (`stageGround`), not
white paper — the PDF paints the ground on every page of a frame. The
root carries it on every sheet, exactly, and the adjustment inherits. -/
def printSheetGround : DeckRule :=
  { selector := [.lit "html"]
    decls := [("background", stageGround), ("print-color-adjust", "exact")]
    part := .print }

/-- How far ahead of the declared vertical distribution a frame's end
spacer claims the leftover (`printFrameEnd`): a hundredfold over the
largest pair of fill shares any alignment declares
(`printEndGrow_outranks_contract`), so the spacer takes its whole safe area
before a fill grows, to within one part in a hundred of the leftover. -/
def printEndGrow : Nat := 1000000

/-- The end spacer outranks every declared distribution a hundredfold:
the golden title page's 3618 + 2000 is the largest, and a new alignment
with larger shares fails here instead of moving a printed frame's
content. `_contract`'s grade: one bound, every alignment. -/
theorem printEndGrow_outranks_contract :
    ∀ v : Ir.VAlign, 100 * (v.shares.1 + v.shares.2) ≤ printEndGrow := by
  intro v
  cases v <;> decide

/-- A frame's bottom safe area on paper is room its content may take
before the frame continues, not a box that continues by itself. Padding
would: a frame whose content fits its sheet but not its sheet less the
safe area printed one blank sheet holding only its padding — three in a
measured 31-frame deck, where the HTML's rhythm runs a few points taller
than the PDF's. So on paper a frame keeps its safe area as a trailing
spacer that takes its whole safe area from the leftover first
(`printEndGrow`) and gives it back when the content needs the room: a
frame with room to spare lays out exactly as its padding would, a frame
that overruns by less than the safe area prints on one sheet with its
last line that much nearer the edge, and only content longer than the
sheet continues. A section page keeps its padding: it holds a title and
a bar. -/
def printFrameEnd : List DeckRule :=
  [ { selector := [.lit "section.slide"], decls := [("padding-bottom", "0")]
      part := .print },
    { selector := [.lit "section.slide::after"]
      decls := [("content", "\"\""), ("flex", s!"{printEndGrow} 0 0"),
        ("max-height", safeareaVar)]
      part := .print } ]

/-- The print rules every deck carries, steps aside. -/
def printPaged : List DeckRule := [printStageRule, printSheetGround] ++ printFrameEnd

/-- The print partition: the screen deck's stages, paged — the stage
partition carries their box, type and furniture onto paper, and the stage
itself grows onto as many sheets as its content needs (`printPaged`). For
a stepped deck the snap spacers hide and every step prints at full
colour: paper has no steps to reveal (the user's own rule, beside the
unconditional covered floor it was written against). -/
def deckPrint (maxSteps : Nat) : List DeckRule :=
  printPaged ++
    (if 2 ≤ maxSteps then
      [ { selector := [.lit ".snap"], decls := [("display", "none")]
          part := .print },
        { selector := [.lit ".step"], decls := [("opacity", "100%")]
          part := .print } ]
     else [])

/-- A numbered union dims precisely outside its emitted membership set.
Both a stepped track and a one-reveal section own `data-snapped`: the
script advances the track, while the section declares its only step.
The script-free floor remains fully uncovered. -/
def stepSetPendingRule (cp k : Nat) : DeckRule :=
  { selector := [.lit "html[data-deck-script] [data-snapped=\"", .num k,
      .lit "\"] .step-set:not([data-steps~=\"", .num k, .lit "\"])"]
    decls := [("opacity", s!"{cp}%")] }

def altSetShownRule (k : Nat) : DeckRule :=
  { selector := [.lit "[data-snapped=\"", .num k,
      .lit "\"] .alt-set[data-steps~=\"", .num k, .lit "\"]"]
    decls := [("display", "contents")] }

def altSetHiddenRule (k : Nat) : DeckRule :=
  { selector := [.lit "[data-snapped=\"", .num k,
      .lit "\"] .alt-set:not([data-steps~=\"", .num k, .lit "\"])"]
    decls := [("display", "none")] }

/-- Same specificity as pending's snap selector, emitted after it under
reduce. Paper already excludes the screen-only pending rule. -/
def stepSetGuard : DeckRule :=
  { selector := [.lit "html[data-deck-script] [data-snapped] .step-set[data-steps]"]
    decls := [("opacity", "100%")]
    part := .reduce }

/-- A pending ancestor has already covered every descendant. Stop the
descendant's own cover, including its end carrier, so nesting implements
`OverlaySpec.pending_nested_exact` once rather than multiplying opacity.
The ancestor's own end carrier is deliberately outside this selector. -/
def nestedCoverRule (k : Nat) : DeckRule :=
  let parent := [.lit "html[data-deck-script] [data-snapped=\"", .num k,
    .lit "\"] :is(.step, .step-set):not([data-steps~=\"", .num k, .lit "\"])"]
  { selector := parent ++ [.lit " :is(.step, .step-set), "] ++ parent ++
      [.lit " :is(.step, .step-set) > .step-end"]
    decls := [("opacity", "100%"), ("animation", "none")] }

/-- Without a numbered state owner that can advance, the cover floor is
fully readable. Apply that floor in timeline-capable browsers too: two
independent opacity timelines cannot implement the shared pending latch. -/
def coverStaticFloor : DeckRule :=
  { selector := [.lit "html:not([data-deck-script]) :is(.step, .step-end, .step-set)"]
    decls := [("opacity", "100%"), ("animation", "none")] }

def setRules (cp ms : Nat) : List DeckRule :=
  stepSetGuard :: coverStaticFloor :: (List.range ms).flatMap fun i =>
    [stepSetPendingRule cp (i + 1), altSetShownRule (i + 1), altSetHiddenRule (i + 1),
      nestedCoverRule (i + 1)]

private theorem setRules_cases {P : DeckRule → Prop} {cp ms : Nat}
    (hg : P stepSetGuard) (hf : P coverStaticFloor)
    (hp : ∀ k, P (stepSetPendingRule cp k))
    (hs : ∀ k, P (altSetShownRule k)) (hh : ∀ k, P (altSetHiddenRule k))
    (hn : ∀ k, P (nestedCoverRule k)) :
    ∀ r ∈ setRules cp ms, P r := by
  intro r hr
  simp only [setRules, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | ⟨i, _, rfl | rfl | rfl | rfl⟩
  · exact hg
  · exact hf
  · exact hp _
  · exact hs _
  · exact hh _
  · exact hn _

/-- Every rule of the deck's stylesheet, in emission order. The
parameters are the whole document-dependence: the stage-ratio type size,
the printed page's size, the design's covered fraction, and the deck's
maximum step count. -/
def deckRules (bodyVh pageSize : String) (coveredPct maxSteps : Nat) : List DeckRule :=
  deckBase bodyVh ++ deckReduce ++
    ((if 2 ≤ maxSteps then stepRules coveredPct maxSteps ++ altRules maxSteps else []) ++
      setRules coveredPct maxSteps) ++
    deckPageRule pageSize :: deckPrint maxSteps

/-- The one case split over the deck's rule set: every deck theorem
below quantifies over `deckRules` through this. A new rule family is a
new hypothesis here — the compiler names every theorem it now owes. The
step hypotheses receive the fact that the steps shipped (`2 ≤ ms`), so a
theorem may cite a step rule's membership. -/
private theorem deckRules_forall {P : DeckRule → Prop} {v pg : String} {cp ms : Nat}
    (hbase : ∀ r ∈ deckBase v, P r)
    (hreduce : ∀ r ∈ deckReduce, P r)
    (hkey : 2 ≤ ms → P (stepKeyframes cp))
    (hrkey : 2 ≤ ms → P (stepRecoverKeyframes cp))
    (hcov : 2 ≤ ms → P (stepFloorCovered cp))
    (hfix : 2 ≤ ms → ∀ r ∈ stepFixed, P r)
    (hsnapped : 2 ≤ ms → ∀ k, P (stepSnappedRule k))
    (hrecovered : 2 ≤ ms → ∀ k, P (stepRecoverFloorRule cp ms k))
    (haltfix : 2 ≤ ms → ∀ r ∈ altReduceFixed, P r)
    (haltsnap : 2 ≤ ms → ∀ k, ∀ r ∈ altSnapRules ms k, P r)
    (hsets : ∀ r ∈ setRules cp ms, P r)
    (hpage : ∀ s, P (deckPageRule s))
    (hprint : ∀ r ∈ deckPrint ms, P r) :
    ∀ r ∈ deckRules v pg cp ms, P r := by
  intro r hr
  simp only [deckRules, List.mem_append, List.mem_cons] at hr
  rcases hr with ((h | h) | (h | h)) | (rfl | h)
  · exact hbase r h
  · exact hreduce r h
  · split at h
    case isTrue hms =>
      simp only [stepRules, stepSnapped, stepRecovered, altRules, altSnapped,
        List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
        List.mem_range] at h
      rcases h with (rfl | rfl | rfl | ((h | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩)) |
        (h | ⟨i, -, h⟩)
      · exact hkey hms
      · exact hrkey hms
      · exact hcov hms
      · exact hfix hms r h
      · exact hsnapped hms _
      · exact hrecovered hms _
      · exact haltfix hms r h
      · exact haltsnap hms _ r h
    case isFalse => cases h
  · exact hsets r h
  · exact hpage pg
  · exact hprint r h

/-- The two reduce-partition alternation rules, as a case split: both are
closed spellings, so a per-rule fact is two `rfl`s. -/
private theorem altReduceFixed_cases {P : DeckRule → Prop}
    (h1 : P altReduceHiddenRule) (h2 : P altReduceShownRule) :
    ∀ r ∈ altReduceFixed, P r := by
  intro r hr
  simp only [altReduceFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h1
  · exact h2

/-- A decidable or propositional fact over one snap's alternation rules,
from the four named rules: they share their spelling but for the data, and
no per-rule check reads the data. -/
private theorem altSnapRules_cases {P : DeckRule → Prop} {ms k : Nat}
    (h1 : P (altStartCrispRule ms k)) (h2 : P (altStartPendingRule ms k))
    (h3 : P (altEndCrispRule ms k)) (h4 : P (altEndPendingRule ms k)) :
    ∀ r ∈ altSnapRules ms k, P r := by
  intro r hr
  simp only [altSnapRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

/-- Family memberships, spelled once against the append spine. -/
private theorem mem_deckRules_base {r : DeckRule} {v pg : String} {cp ms : Nat}
    (h : r ∈ deckBase v) : r ∈ deckRules v pg cp ms := by
  simp only [deckRules, List.mem_append]
  exact Or.inl (Or.inl (Or.inl h))

private theorem mem_deckRules_reduce {r : DeckRule} {v pg : String} {cp ms : Nat}
    (h : r ∈ deckReduce) : r ∈ deckRules v pg cp ms := by
  simp only [deckRules, List.mem_append]
  exact Or.inl (Or.inl (Or.inr h))

private theorem mem_deckRules_step {r : DeckRule} {v pg : String} {cp ms : Nat}
    (hms : 2 ≤ ms) (h : r ∈ stepRules cp ms) : r ∈ deckRules v pg cp ms := by
  simp only [deckRules, List.mem_append]
  refine Or.inl (Or.inr (Or.inl ?_))
  simpa only [ite_eq_left hms, List.mem_append] using
    (Or.inl h : r ∈ stepRules cp ms ∨ r ∈ altRules ms)

/-- A closed step rule's membership, through the `stepFixed` spine. -/
private theorem mem_stepRules_fixed {r : DeckRule} {cp ms : Nat}
    (h : r ∈ stepFixed) : r ∈ stepRules cp ms := by
  simp only [stepRules, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))

/-- The print partition of a stepless deck is contained in the stepped
one, so a decidable per-rule fact is checked once, on `deckPrint 2`. -/
private theorem deckPrint_subset {ms : Nat} : ∀ r ∈ deckPrint ms, r ∈ deckPrint 2 := by
  intro r hr
  simp only [deckPrint, List.mem_append] at hr ⊢
  rcases hr with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    split at h
    · simpa using h
    · cases h

/-- Discharge a decidable per-rule fact over every rule family at once:
the closed families by `decide`, the parameter-carrying ones by `rfl` —
their checks never read a parameter (values are compared by name
equality only; ordinal chunks carry no syntax). -/
private theorem deckRules_check {p : DeckRule → Bool} (v pg : String) (cp ms : Nat)
    (hbase : ∀ r ∈ deckBase v, p r = true)
    (hreduce : ∀ r ∈ deckReduce, p r = true)
    (hkey : p (stepKeyframes cp) = true)
    (hrkey : p (stepRecoverKeyframes cp) = true)
    (hcov : p (stepFloorCovered cp) = true)
    (hfix : ∀ r ∈ stepFixed, p r = true)
    (hsnapped : ∀ k, p (stepSnappedRule k) = true)
    (hrecovered : ∀ k, p (stepRecoverFloorRule cp ms k) = true)
    (haltfix : ∀ r ∈ altReduceFixed, p r = true)
    (haltsnap : ∀ k, ∀ r ∈ altSnapRules ms k, p r = true)
    (hsets : ∀ r ∈ setRules cp ms, p r = true)
    (hpage : ∀ s, p (deckPageRule s) = true)
    (hprint : ∀ r ∈ deckPrint 2, p r = true) :
    ∀ r ∈ deckRules v pg cp ms, p r = true :=
  deckRules_forall hbase hreduce (fun _ => hkey) (fun _ => hrkey) (fun _ => hcov)
    (fun _ => hfix) (fun _ _ => hsnapped _) (fun _ _ => hrecovered _)
    (fun _ => haltfix) (fun _ k => haltsnap k) hsets hpage
    (fun r hr => hprint r (deckPrint_subset r hr))

/-- Membership in the base family, for the rules with a parametric
value: the check is discharged by `rfl` after the case split. -/
private theorem deckBase_cases {P : DeckRule → Prop} {v : String}
    (h1 : P { selector := [.lit "html"]
              decls := [("scroll-snap-type", "x mandatory"), ("overflow-y", "clip")] })
    (h2 : P deckGlideRule)
    (h3 : P { selector := [.lit "body"], decls := [("padding", "0")], part := .stage })
    (h4 : P { selector := [.lit "main"]
              decls := [("max-width", "none"), ("margin", "0"), ("font-size", v)]
              part := .stage })
    (h4a : P { selector := [.lit "main"]
               decls := [("display", "flex"), ("align-items", "flex-start")] })
    (h5 : P deckStageRule)
    (h6 : P deckSnapDoor)
    (h6a : P deckLogoRule)
    (h7 : P { selector := [.lit "section.section-page"]
              decls := [("justify-content", "center"), ("align-items", "center")]
              part := .stage })
    (h8 : P { selector := [.lit "h1"], decls := [("font-size", scaleSize "LARGE" "em")]
              part := .stage })
    (h9 : P { selector := [.lit "h2"], decls := [("font-size", scaleSize "Large" "em")]
              part := .stage })
    (h10 : P { selector := [.lit "h3"], decls := [("font-size", scaleSize "large" "em")]
               part := .stage })
    (h11 : P { selector := [.lit "section.slide > header"]
               decls := [("max-height", titlebandVar)], part := .stage })
    (h12 : P { selector := [.lit "section.slide > header h2"]
               decls := [("font-size", scaleSize "Large" "em")], part := .stage }) :
    ∀ r ∈ deckBase v, P r := by
  intro r hr
  simp only [deckBase, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;>
    assumption

/-- `deck_css_partition`'s per-rule check: a rule whose syntax uses a
fragment depending on feature `F` is gated `supported F`. -/
def gateRespects (r : DeckRule) : Bool :=
  Feature.all.all fun f => r.requires == Gate.supported f || !(r.uses f)

/-- Every rule using a property or selector fragment whose meaning
depends on a feature (`Feature.dependsOnProps`, `Feature.dependsOnSel`)
is emitted inside that feature's supported block, and — contrapositively
— no rule inside a feature's unsupported block or the base uses one. So
a browser lacking F never parses a rule that needs it, and never loses a
rule that does not. `_covers`'s grade, over the whole rule set: a new
rule enters the contract the moment it is written. -/
theorem deck_css_partition (v pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms, gateRespects r = true :=
  deckRules_check v pg cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl rfl (by decide) (fun _ => rfl) (fun _ => rfl)
    (by decide) (fun _ => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)) (fun _ => rfl) (by decide)

/-- The Baseline floor: the property names the base, the `@supports not`
blocks, the reduced-motion partition and the print handout may use.
Every entry is universal across current engines (caniuse, read
2026-09-20): scroll snap (`scroll-snap-*`: Chromium 69+, Firefox 68+,
Safari 11+), `scroll-behavior` (Chromium 61+, Firefox 36+, Safari
15.4+), flex and the box properties (universal since 2017), custom
properties (Chromium 49+, Firefox 31+, Safari 9.1+), `@supports` itself
(Chromium 28+, Firefox 22+, Safari 9+), animations, transforms,
opacity, and the fragmentation properties print engines honour
(`break-*`). The `dvh` unit rides several values (Chromium 108+,
Firefox 101+, Safari 15.4+; 2022). The box offset properties (`bottom`,
`left`, `right`) are CSS 2. The printed page's `size` (CSS Paged Media 3
§7) and `print-color-adjust` (CSS Color Adjustment 1 §3.1) are print-only
and degrade to the reader's own page and toner setting where unsupported
— measured honoured by Chromium 151 (the page size and the grounds of a
printed deck, `print-color-adjust` with backgrounds off). The same holds
for `box-decoration-break` (CSS Fragmentation 3 §5.4), print-only here:
Chromium 151 clones a continuing stage's padding onto each sheet
(measured on a printed breaking frame); where unsupported it degrades to
`slice`, and every line still reaches paper — a continuation sheet's text
just starts at its edge. `break-before` is `break-after`'s twin (CSS
Fragmentation 3 §3.1) and `padding-bottom` is CSS 2's. The selector
side of the floor is `deck_css_partition`; attribute selectors
(`[data-snap]`, `[data-deck-script]`) are CSS 2. -/
def baselineProps : List String :=
  ["scroll-snap-type", "scroll-snap-align", "scroll-snap-stop",
   "scroll-behavior", "padding", "padding-bottom", "margin", "margin-top", "max-width",
   "width", "flex", "background", "overflow-y",
   "min-height", "max-height", "height", "font-size", "color",
   "text-align", "opacity", "transform", "display", "flex-direction",
   "justify-content", "align-items", "position", "content",
   "animation", "border", "border-radius", "break-inside", "break-after",
   "break-before", "size", "print-color-adjust", "box-decoration-break",
   "bottom", "left", "right"]

/-- Is the rule part of the floor — the CSS every engine applies? The
base and every `@supports not` block, in every media partition. -/
def onFloor (r : DeckRule) : Bool :=
  match r.requires with
  | .base => true
  | .unsupported _ => true
  | .supported _ => false

/-- "Works in Firefox", in the only form the engine can state it: every
property the floor uses is in the declared, sourced `baselineProps` — a
browser with no gated feature at all still understands every rule it is
given. `_mem`'s grade: each floor property is drawn from the declared
set. -/
theorem floor_is_baseline (v pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms,
      (!(onFloor r) || r.decls.all fun d => baselineProps.contains d.1) = true :=
  deckRules_check v pg cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl rfl (by decide) (fun _ => rfl) (fun _ => rfl)
    (by decide) (fun _ => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)) (fun _ => rfl) (by decide)

/-- Content, as the floor theorems see it: the frame stages and the
steps — the fragments that address what the deck *shows*. -/
def contentFrags : List String :=
  ["section.slide", "section.section-page", ".step[", ".step:"]

def targetsContent (r : DeckRule) : Bool :=
  contentFrags.any fun frag =>
    (r.selector.flatMap SelChunk.lits).any fun s => hasFrag s frag

/-- The floor is visible by theorem, not by review: no deck rule — in
*any* partition — sets `display: none` or `visibility: hidden` on
content (`contentFrags`). What the guards and the printed deck hide is
only the spacers. `floor_opacity_mem` and `floor_covered_script_gated`
are the dimming half.

One family stands deliberately outside `contentFrags`: an overlay
alternation's group wrappers (`.alt-crisp`, `.alt-pending`), which the
snap rules do hide with `display: none`. That is the point of the second
mechanism — an unselected group is content this page does not have, and
the page's other group is showing in its place, which is a contract about
*which* of two, not about visibility. `alt_backend_agree` is that
contract; extending `contentFrags` to cover the groups would make this
theorem false while saying nothing truer. -/
theorem floor_hides_nothing (v pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms,
      (!(targetsContent r) ||
        (!(r.decls.contains ("display", "none")) &&
         !(r.decls.contains ("visibility", "hidden")))) = true :=
  deckRules_check v pg cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl rfl (by decide) (fun _ => rfl) (fun _ => rfl)
    (by decide) (fun _ => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)) (fun _ => rfl) (by decide)

/-- The opacity values a rule sets. -/
def opacityValues (r : DeckRule) : List String :=
  r.decls.filterMap fun d => if d.1 == "opacity" then some d.2 else none

/-- The dimming half of the visible floor: every opacity any deck rule
sets is full or the design's own covered fraction — never below it, and
never a hide wearing a dim's clothes. `_mem`'s grade: each value is
drawn from the two the design allows. -/
theorem floor_opacity_mem (v pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms, ∀ o ∈ opacityValues r,
      o = "100%" ∨ o = s!"{cp}%" := by
  refine deckRules_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact deckBase_cases (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
  · intro r hr
    simp only [deckReduce, deckGlideGuard, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl
    exact fun o ho => nomatch ho
  · exact fun _ o ho => Or.inr (List.mem_singleton.mp ho)
  · exact fun _ o ho => Or.inr (List.mem_singleton.mp ho)
  · exact fun _ o ho => Or.inr (List.mem_singleton.mp ho)
  · intro _ r hr
    simp only [stepFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
      first
        | exact fun o ho => Or.inl (List.mem_singleton.mp ho)
        | exact fun o ho => nomatch ho
  · exact fun _ k o ho => Or.inl (List.mem_singleton.mp ho)
  · exact fun _ k o ho => Or.inr (List.mem_singleton.mp ho)
  · intro _ r hr
    simp only [altReduceFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact fun o ho => nomatch ho
  · exact fun _ k => altSnapRules_cases (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
  · exact setRules_cases
      (fun o ho => Or.inl (List.mem_singleton.mp ho))
      (fun o ho => Or.inl (List.mem_singleton.mp ho))
      (fun _ o ho => Or.inr (List.mem_singleton.mp ho))
      (fun _ o ho => nomatch ho) (fun _ o ho => nomatch ho)
      (fun _ o ho => Or.inl (List.mem_singleton.mp ho))
  · exact fun _ o ho => nomatch ho
  · intro r hr
    have hr2 := deckPrint_subset r hr
    simp only [deckPrint, List.mem_append] at hr2
    rcases hr2 with h1 | h2
    · have hnone : ∀ q ∈ printPaged, opacityValues q = [] := by decide
      intro o ho
      rw [hnone r h1] at ho
      exact nomatch ho
    · split at h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl
        · exact fun o ho => nomatch ho
        · exact fun o ho => Or.inl (List.mem_singleton.mp ho)
      · cases h2

/-- Does the rule's selector carry the deck script's own marker,
`[data-deck-script]` — the attribute only `deckScript` sets? -/
def scriptGated (r : DeckRule) : Bool :=
  (r.selector.flatMap SelChunk.lits).any fun s => hasFrag s "[data-deck-script]"

/-- The floor never dims without the script: every rule of the base or
an `@supports not` block that sets an opacity below full carries
`html[data-deck-script]` in its selector, so with scripting off (or the
node absent) every step stands at full colour and the deck is the
pure-CSS pager — the covered state a script cannot uncover is never
declared. The dimming half of `floor_hides_nothing` made exact.
`_contract`'s grade. -/
theorem floor_covered_script_gated (v pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms,
      (!(onFloor r) || scriptGated r ||
        r.decls.all fun d => d.1 != "opacity" || d.2 == "100%") = true :=
  deckRules_check v pg cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl rfl (by decide) (fun _ => rfl) (fun _ => rfl)
    (by decide) (fun _ => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)) (fun _ => rfl) (by decide)

/-- The motion properties the reduced-motion contract covers: the base
sheet's global reduce block strips `animation` and `transition`;
`scroll-behavior` is neither and needs the declared guard (WCAG 2.2
SC 2.3.3, technique C39; CSS Media Queries 5 §12.1). -/
def motionProps : List String := ["animation", "transition", "scroll-behavior"]

/-- The static value a guard must set a motion property back to. -/
def motionOff : String → String
  | "scroll-behavior" => "auto"
  | _ => "none"

/-- Does reduce-partition rule `g` cover `r`'s selector? Equal
selectors, or `g`'s compound extended by a pseudo-class (`.step` guards
`.step:not(…)`): everything `r` matches, `g` matches. The prefix test is
spelled over the character lists so the proofs evaluate it. -/
def guardCovers (g r : DeckRule) : Bool :=
  g.part == Part.reduce &&
    (renderSel g.selector == renderSel r.selector ||
      (renderSel g.selector ++ ":").toList.isPrefixOf
        (renderSel r.selector).toList)

/-- Is every active motion property guarded by some rule of the searched
set's reduce partition? A property already set to its static value needs
no second reset. The reduce and print partitions are exempt — the guards
themselves, and paper, which has no motion; a stage rule plays on screen
too, so it owes its guard like a screen rule. -/
def motionGuarded (rules : List DeckRule) (r : DeckRule) : Bool :=
  (r.part == Part.reduce || r.part == Part.print) ||
    r.decls.all fun d =>
      !(motionProps.contains d.1) || d.2 == motionOff d.1 ||
        rules.any fun g => guardCovers g r && g.decls.contains (d.1, motionOff d.1)

/-- `motionGuarded` from one named witness. -/
private theorem motionGuarded_of_guard {rules : List DeckRule} {r g : DeckRule}
    (hg : g ∈ rules)
    (hchk : ∀ d ∈ r.decls, motionProps.contains d.1 = true →
      (guardCovers g r && g.decls.contains (d.1, motionOff d.1)) = true) :
    motionGuarded rules r = true := by
  unfold motionGuarded
  cases hpart : (r.part == Part.reduce || r.part == Part.print)
  · rw [Bool.false_or, List.all_eq_true]
    intro d hd
    cases hmp : motionProps.contains d.1
    · rw [Bool.not_false, Bool.true_or, Bool.true_or]
    · rw [Bool.not_true, Bool.false_or]
      rw [List.any_eq_true.mpr ⟨g, hg, hchk d hd hmp⟩, Bool.or_true]
  · rw [Bool.true_or]

/-- Every rule that activates a motion property (`motionProps`) has a
reduced-motion counterpart *in the same emitted rule set*, covering its
selector and setting the property back to its static value: a guard is
not a suffix a definition happens to end with; it is a rule the reduce
partition must contain, and the partition is emitted after the blocks it
reverts (`emitDeckRules`; CSS Cascade 5 §6.4). `_contract`'s grade. -/
theorem guards_by_construction (v pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms, motionGuarded (deckRules v pg cp ms) r = true := by
  refine deckRules_forall ?_ ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => altReduceFixed_cases rfl rfl)
    (fun _ k => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl))
    (fun _ => rfl) ?_
  · exact deckBase_cases rfl
      (motionGuarded_of_guard (g := deckGlideGuard)
        (mem_deckRules_reduce (by decide)) (by decide))
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · intro r hr
    simp only [deckReduce, deckGlideGuard, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl
    rfl
  · intro hms r hr
    have hstep : stepGuard ∈ deckRules v pg cp ms :=
      mem_deckRules_step hms (mem_stepRules_fixed (by decide))
    have hend : stepRecoverGuard ∈ deckRules v pg cp ms :=
      mem_deckRules_step hms (mem_stepRules_fixed (by decide))
    simp only [stepFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    case inr.inr.inr.inl =>
      exact motionGuarded_of_guard hstep (by decide)
    case inr.inr.inr.inr.inl =>
      exact motionGuarded_of_guard hend (by decide)
    all_goals rfl
  · intro r hr
    have hr2 := deckPrint_subset r hr
    simp only [deckPrint, List.mem_append] at hr2
    rcases hr2 with h1 | h2
    · simp only [printPaged, printFrameEnd, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at h1
      rcases h1 with (rfl | rfl) | (rfl | rfl) <;> rfl
    · split at h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl <;> rfl
      · cases h2

/-- The declarations that bound a stage on screen and would clip it on
paper, each with the value that lifts it in print. A scroll container is
monolithic — it holds no break point, so what exceeds its box is clipped
at the sheet's edge (CSS Fragmentation 3 §4.1) — and a fixed height stops
the box growing with its content. Paper has no scroll: the stage grows
instead, and breaks between its lines as the PDF's continuation pages
do. -/
def stageBounds : List (String × String) := [("height", "auto"), ("overflow-y", "visible")]

/-- Does print-partition rule `g` lift every bound stage rule `r` declares?
Ungated, so it holds in every engine, and at `r`'s own selector, so the
print partition — emitted after the stage partition (`emitDeckRules`) —
wins at equal specificity by source order (CSS Cascade 5 §6.4). -/
def liftsOnPaper (g r : DeckRule) : Bool :=
  g.part == Part.print && g.requires == Gate.base &&
    renderSel g.selector == renderSel r.selector &&
    r.decls.all fun d => match List.lookup d.1 stageBounds with
      | none => true
      | some lift => g.decls.contains (d.1, lift)

/-- A content rule of the stage partition that declares a bound is lifted
on paper by some rule of the searched set. -/
def printLifts (rules : List DeckRule) (r : DeckRule) : Bool :=
  !(r.part == Part.stage && targetsContent r &&
      r.decls.any fun d => (List.lookup d.1 stageBounds).isSome) ||
    rules.any fun g => liftsOnPaper g r

/-- `printLifts` from one named witness. -/
private theorem printLifts_of_lift {rules : List DeckRule} {r g : DeckRule}
    (hg : g ∈ rules) (hl : liftsOnPaper g r = true) : printLifts rules r = true := by
  unfold printLifts
  rw [List.any_eq_true.mpr ⟨g, hg, hl⟩, Bool.or_true]

private theorem mem_deckRules_print {r : DeckRule} {v pg : String} {cp ms : Nat}
    (h : r ∈ deckPrint ms) : r ∈ deckRules v pg cp ms := by
  simp only [deckRules, List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr h)

/-- A stage never clips on paper: every bound a stage rule declares
(`stageBounds`) is lifted by an ungated print rule at its own selector, so
on paper a frame grows with its content and a frame that runs long
continues on the next sheet, as the PDF's continuation pages do, where on
screen it scrolls. Before the lift the stage's `height: 100dvh;
overflow-y: auto` held on paper too, and a breaking frame printed 14 of
its 30 items. `_covers`'s grade over the rule set, the shape of
`guards_by_construction`: a stage rule that declares a bound enters the
contract the moment it is written. -/
theorem print_lifts_stage_bounds_covers (v pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms, printLifts (deckRules v pg cp ms) r = true := by
  refine deckRules_forall ?_ ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => altReduceFixed_cases rfl rfl)
    (fun _ k => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl))
    (fun _ => rfl) ?_
  · exact deckBase_cases rfl rfl rfl rfl rfl
      (printLifts_of_lift (g := printStageRule)
        (mem_deckRules_print (List.mem_append_left _ (by decide))) (by decide))
      rfl rfl rfl rfl rfl rfl rfl rfl
  · intro r hr
    simp only [deckReduce, deckGlideGuard, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl
    rfl
  · intro _ r hr
    simp only [stepFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> rfl
  · intro r hr
    have hr2 := deckPrint_subset r hr
    simp only [deckPrint, List.mem_append] at hr2
    rcases hr2 with h1 | h2
    · simp only [printPaged, printFrameEnd, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at h1
      rcases h1 with (rfl | rfl) | (rfl | rfl) <;> rfl
    · split at h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl <;> rfl
      · cases h2

/-- Every step of every stepped frame is reachable in the floor: for
each step `n` of a deck whose maximum step count is `ms`
(`Ir.frameSteps`; step 1 is never covered), the emitted rules contain
an uncover rule whose snap is a spacer `k ≥ n` uncovering `n` —
concretely `k = n`, the `data-snapped` value the script writes when the
reader's key lands that snap point. The uncover set `uncoveredBy k` is
the selector's own data: the `:is()` alternatives render from it
(`SelChunk.stepAlts`). `_covers`'s grade. -/
theorem snapped_uncovers_every_step (v pg : String) (cp ms n : Nat)
    (h2 : 2 ≤ n) (hn : n ≤ ms) :
    ∃ k, n ≤ k ∧ stepSnappedRule k ∈ deckRules v pg cp ms ∧ n ∈ uncoveredBy k := by
  refine ⟨n, Nat.le_refl n, ?_, ?_⟩
  · refine mem_deckRules_step (Nat.le_trans h2 hn) ?_
    simp only [stepRules, stepSnapped, List.mem_cons, List.mem_append,
      List.mem_map, List.mem_range]
    refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨n - 2, by omega, ?_⟩))))
    rw [Nat.sub_add_cancel h2]
  · simp only [uncoveredBy, List.mem_map, List.mem_range]
    exact ⟨n - 2, by omega, by omega⟩

/-- The snap partition, from the typed rules — the CSS half of "every
frame is reachable by paging in every engine", on the horizontal axis.
The `[data-snap]` door (`deckSnapDoor`, ungated) is the deck's one snap
declaration: the emitter marks a stepless frame's section, a section
page, and a stepped frame's spacers (`track_snaps_exact` counts them),
so on the timeline path the snap points count one per stepless frame
plus one per step — the PDF handout's own pagination
(`pages_partition_frames`, the owed PDF half, is this count's twin: its
per-frame page count is `Ir.frameSteps`, this count's source).
On the floor the spacers hide (`stepSnapHide`) and the track takes the
frame's one snap (`stepTrackFloorSnap`): one snap point per frame.
`_covers`'s grade over the partition: each fact is the membership of the
rule that carries it, in the gate that scopes it. -/
theorem snap_pages_partition_frames (v pg : String) (cp ms : Nat) (hms : 2 ≤ ms) :
    (deckSnapDoor ∈ deckRules v pg cp ms ∧ deckSnapDoor.requires = .base ∧
      ("scroll-snap-align", "start") ∈ deckSnapDoor.decls) ∧
    (stepSnapHide ∈ deckRules v pg cp ms ∧
      stepSnapHide.requires = .unsupported .viewTimeline ∧
      ("display", "none") ∈ stepSnapHide.decls) ∧
    (stepTrackFloorSnap ∈ deckRules v pg cp ms ∧
      stepTrackFloorSnap.requires = .unsupported .viewTimeline ∧
      stepTrackFloorSnap.selector = [.lit ".slide-track"] ∧
      ("scroll-snap-align", "start") ∈ stepTrackFloorSnap.decls) :=
  ⟨⟨mem_deckRules_base (by simp [deckBase]), rfl, by decide⟩,
   ⟨mem_deckRules_step hms (mem_stepRules_fixed (by decide)), rfl, by decide⟩,
   ⟨mem_deckRules_step hms (mem_stepRules_fixed (by decide)), rfl, rfl, by decide⟩⟩

/-- The text census does not depend on which path a browser takes:
trivially, since the stylesheet ships no text — no deck rule sets a
non-empty `content` — and the tree is one, whichever `@supports` branch
an engine parses; its census against the IR is the emission conservation
the census checks pin (`censusTable` in Tests). Stated as the projection
statement the theorem-layers rule asks for; `_text`'s grade, the census
contribution being empty. -/
theorem deck_text_path_free (v pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms,
      (r.decls.all fun d =>
        d.1 != "content" || (d.2 == "\"\"" || d.2 == "none")) = true :=
  deckRules_check v pg cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl rfl (by decide) (fun _ => rfl) (fun _ => rfl)
    (by decide) (fun _ => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)) (fun _ => rfl) (by decide)

/-- A length's share of the deck stage, in milli-percent: the one
projection every deck emission rides when it states a PDF stage length
against the viewport — the type size over the stage height, an image
dimension over the stage width or height. `Int` binders, not `Sp`, so
`omega` can read the ratio statements below. -/
def deckStageMilli (x stage : Int) : Int :=
  x * 100000 / stage

/-- The projection is the ratio, exact up to the printed milli: the
emitted value times the stage never exceeds the length (at the 100000
scale) and falls short by less than one stage. The fact both ratio
statements below instantiate. -/
theorem deckStageMilli_share (x stage : Int) (hs : 0 < stage) :
    deckStageMilli x stage * stage ≤ x * 100000 ∧
    x * 100000 < deckStageMilli x stage * stage + stage := by
  have hne : stage ≠ 0 := by omega
  have hmod := Int.emod_nonneg (x * 100000) hne
  have hlt := Int.emod_lt_of_pos (x * 100000) hs
  have heq := Int.mul_ediv_add_emod (x * 100000) stage
  unfold deckStageMilli
  rw [Int.mul_comm (x * 100000 / stage) stage]
  generalize hr : x * 100000 % stage = r at hmod hlt heq
  generalize hp : stage * (x * 100000 / stage) = p at heq ⊢
  generalize ha : x * 100000 = a at heq ⊢
  omega

/-- The cross-backend type ratio, exact up to the printed milli: the
deck's body size over the viewport height is the very ratio the PDF
stage declares — `fontSize` over the page height (`Ir.slidesStage169`'s
90mm carries beamer's 11pt as ≈4.31% of the stage; beamer user guide
§18.2.1 for the size, the stage for the height) — so the two artifacts
show the same type-to-stage proportion whatever the screen's size.
`backend_gaps_agree`'s mold: the shared thing is the ratio, each backend
realizing it in its own context's unit (the PDF in its stage, the screen
in its viewport). -/
theorem deck_type_is_stage_ratio (fontSize height : Int) (hh : 0 < height) :
    deckStageMilli fontSize height * height ≤ fontSize * 100000 ∧
    fontSize * 100000 < deckStageMilli fontSize height * height + height :=
  deckStageMilli_share fontSize height hh

/-- The cross-backend image ratio, the same mold: the deck's HTML states
an image dimension as its share of the stage (`deckStageMilli`, printed
in `vw`/`dvh` — the stage realized as the viewport, CSS Values 4 §6.1.2),
and the PDF's image box is `Image.resolveSize` over the same request
(graphicx's semantics, sourced at `resolveSize`). For a declared width
the two are one number: the box *is* the resolved request (the first
conjunct, definitional), and the emitted milli times the stage brackets
the box's share to within one printed milli — both are `size / stage`. -/
theorem image_share_agrees (l : Image.Len) (iW iH textW textH stage : Int)
    (hs : 0 < stage) :
    (Image.resolveSize { width := some l } iW iH textW textH).1
        = l.resolve textW textH ∧
    deckStageMilli (l.resolve textW textH) stage * stage
        ≤ (Image.resolveSize { width := some l } iW iH textW textH).1 * 100000 ∧
    (Image.resolveSize { width := some l } iW iH textW textH).1 * 100000
        < deckStageMilli (l.resolve textW textH) stage * stage + stage :=
  ⟨rfl, deckStageMilli_share (l.resolve textW textH) stage hs⟩

/-! ### The deck's constant script

The one script the slides class ships (screen behaviour, no data). The
architecture rule ("no backend emits script") bends here because every
reason behind the rule is discharged by construction: the script is one
closed literal — no document text, palette, or path flows into it
(`deck_script_constant` pins the exact text; the definition takes no
argument) — it rides the typed tree as a raw-text script node the
emitter's `</script` guard already covers, it ships only for the slides
class (`deck_script_gated`), and the deck degrades to the pure-CSS pager
when scripting is off (`floor_covered_script_gated`). The user chose
this over the pure-CSS floor when Home/End did not move the deck. -/

/-- The keyboard, fragment and floor-uncover script. It binds, on the deck's snap
points: ArrowRight/ArrowDown/PageDown/Space → next; ArrowLeft/ArrowUp/
PageUp/Shift+Space → previous; Home/End → first/last. It ignores key
events whose target is editable or that carry modifiers other than
Shift, and respects reduced motion (`matchMedia` → instant scroll, and
each stepped frame is one stop, even when its spacers are hidden). "Snap
point" is the same list the CSS snaps to, read by the same selector the
stylesheet declares alignment on: `[data-snap]` (`deckSnapDoor`) — one
door, so the script and the stylesheet cannot name different elements.
Where `view()` timelines are missing (`CSS.supports` is the same test
`Feature.viewTimeline` gates on) the spacers are hidden and paging a
stepped frame moves no pixel; the script still tracks the current snap
and writes `data-snapped="k"` on its track, which the floor's numeric
uncover rules read (`stepSnappedRule`). At startup it marks
`<html data-deck-script>`, the gate the floor's covered default rides
(`stepFloorCovered`): without the script that covered state is never
declared. Every snap carries its canonical `data-slide-label`: the shared
frame number, with a dotted suffix on every reveal of a stepped frame;
`titlepage` and `section-k` for front matter; an `appendix-` prefix after a
frame-number restart. Bare frame numbers still reach the first reveal,
and authored title-slug links still resolve. Keyboard
moves push history, native scrolling replaces the current fragment, and
hash navigation restores the snap without adding history. -/
def deckScript : String :=
  "(() => {
  document.documentElement.dataset.deckScript = \"\";
  const snaps = Array.from(document.querySelectorAll(\"[data-snap]\"));
  if (snaps.length === 0) return;
  const reduce = matchMedia(\"(prefers-reduced-motion: reduce)\");
  const stageOf = (el) => el.closest(\".slide-track\") || el;
  const links = snaps.map(s => s.dataset.slideLabel);
  const routes = new Map(links.map((key, i) => [key, i]));
  links.forEach((key, i) => {
    if (key.endsWith(\".1\")) routes.set(key.slice(0, -2), i);
  });
  const box = (el) => {
    const r = el.getBoundingClientRect();
    const stage = stageOf(el);
    return r.width > 0 ? r : (stage.querySelector(\"section.slide\") || stage).getBoundingClientRect();
  };
  let cur = 0;
  let destination = null;
  let seenHash = location.hash;
  if (\"scrollRestoration\" in history) history.scrollRestoration = \"manual\";
  const mark = () => {
    const track = snaps[cur].closest(\".slide-track\");
    if (!track) return;
    let k = 0;
    for (const s of snaps) {
      if (s.closest(\".slide-track\") === track) k += 1;
      if (s === snaps[cur]) break;
    }
    track.dataset.snapped = String(k);
  };
  const writeHash = (mode) => {
    const hash = \"#\" + encodeURIComponent(links[cur]);
    if (location.hash !== hash)
      history[mode === \"push\" ? \"pushState\" : \"replaceState\"](history.state, \"\", hash);
    seenHash = location.hash;
  };
  const go = (i, mode, instant = false) => {
    cur = Math.min(Math.max(i, 0), snaps.length - 1);
    destination = cur;
    mark();
    if (mode) writeHash(mode);
    const el = snaps[cur].getBoundingClientRect().width > 0
      ? snaps[cur] : stageOf(snaps[cur]);
    el.scrollIntoView({ behavior: instant || reduce.matches ? \"instant\" : \"smooth\",
      inline: \"start\", block: \"nearest\" });
    if (Math.abs(box(snaps[cur]).left) < 1) destination = null;
  };
  const sync = () => {
    if (location.hash !== seenHash) return;
    if (destination !== null) {
      if (Math.abs(box(snaps[destination]).left) >= 1) return;
      destination = null;
    }
    let best = cur;
    for (let i = 0; i < snaps.length; i += 1)
      if (Math.abs(box(snaps[i]).left) < Math.abs(box(snaps[best]).left)) best = i;
    if (box(snaps[best]).left !== box(snaps[cur]).left) {
      cur = best;
      mark();
      writeHash(\"replace\");
    }
  };
  const readHash = () => {
    seenHash = location.hash;
    let key;
    try { key = decodeURIComponent(location.hash.slice(1)); } catch (_) { return; }
    if (!key) { go(0, null, true); return; }
    let i = routes.get(key);
    if (i === undefined) {
      const target = document.getElementById(key);
      if (!target) return;
      i = snaps.indexOf(target);
      if (i < 0) i = snaps.findIndex(s => stageOf(s).contains(target));
    }
    if (i >= 0) go(i, null, true);
  };
  addEventListener(\"scroll\", sync, { passive: true });
  addEventListener(\"hashchange\", readHash);
  for (const event of [\"wheel\", \"touchstart\", \"pointerdown\"])
    addEventListener(event, () => { destination = null; }, { passive: true });
  readHash();
  if (!location.hash) { sync(); writeHash(\"replace\"); }
  const skip = (i, dir) => {
    if (!reduce.matches) return i;
    while (snaps[i] && stageOf(snaps[i]) === stageOf(snaps[cur])) i += dir;
    if (!snaps[i]) return cur;
    while (i > 0 && stageOf(snaps[i - 1]) === stageOf(snaps[i])) i -= 1;
    return i;
  };
  addEventListener(\"keydown\", (e) => {
    if (e.ctrlKey || e.altKey || e.metaKey || e.defaultPrevented) return;
    const t = e.target;
    if (t instanceof Element &&
        (t.isContentEditable || /^(input|textarea|select|button)$/i.test(t.tagName))) return;
    let i = null;
    if (e.key === \"Home\") i = 0;
    else if (e.key === \"End\") {
      i = snaps.length - 1;
      while (reduce.matches && i > 0 && stageOf(snaps[i - 1]) === stageOf(snaps[i])) i -= 1;
    }
    else if ((e.key === \" \" && e.shiftKey) || e.key === \"ArrowLeft\" ||
        e.key === \"ArrowUp\" || e.key === \"PageUp\") i = skip(cur - 1, -1);
    else if ((e.key === \" \" && !e.shiftKey) || e.key === \"ArrowRight\" ||
        e.key === \"ArrowDown\" || e.key === \"PageDown\") i = skip(cur + 1, 1);
    if (i === null) return;
    e.preventDefault();
    go(i, \"push\");
  });
})();"

/-- The script is a constant: this pin *is* the guarantee — the day an
interpolation or parameter enters `deckScript`, this `rfl` stops
compiling and the architecture discussion reopens. A constant has no
escaping obligation (nothing a document writes can reach it), which is
the condition under which the no-script rule bends. `_exact`'s grade,
the golden's mechanism in a theorem's seat. -/
theorem deck_script_constant : deckScript =
  "(() => {
  document.documentElement.dataset.deckScript = \"\";
  const snaps = Array.from(document.querySelectorAll(\"[data-snap]\"));
  if (snaps.length === 0) return;
  const reduce = matchMedia(\"(prefers-reduced-motion: reduce)\");
  const stageOf = (el) => el.closest(\".slide-track\") || el;
  const links = snaps.map(s => s.dataset.slideLabel);
  const routes = new Map(links.map((key, i) => [key, i]));
  links.forEach((key, i) => {
    if (key.endsWith(\".1\")) routes.set(key.slice(0, -2), i);
  });
  const box = (el) => {
    const r = el.getBoundingClientRect();
    const stage = stageOf(el);
    return r.width > 0 ? r : (stage.querySelector(\"section.slide\") || stage).getBoundingClientRect();
  };
  let cur = 0;
  let destination = null;
  let seenHash = location.hash;
  if (\"scrollRestoration\" in history) history.scrollRestoration = \"manual\";
  const mark = () => {
    const track = snaps[cur].closest(\".slide-track\");
    if (!track) return;
    let k = 0;
    for (const s of snaps) {
      if (s.closest(\".slide-track\") === track) k += 1;
      if (s === snaps[cur]) break;
    }
    track.dataset.snapped = String(k);
  };
  const writeHash = (mode) => {
    const hash = \"#\" + encodeURIComponent(links[cur]);
    if (location.hash !== hash)
      history[mode === \"push\" ? \"pushState\" : \"replaceState\"](history.state, \"\", hash);
    seenHash = location.hash;
  };
  const go = (i, mode, instant = false) => {
    cur = Math.min(Math.max(i, 0), snaps.length - 1);
    destination = cur;
    mark();
    if (mode) writeHash(mode);
    const el = snaps[cur].getBoundingClientRect().width > 0
      ? snaps[cur] : stageOf(snaps[cur]);
    el.scrollIntoView({ behavior: instant || reduce.matches ? \"instant\" : \"smooth\",
      inline: \"start\", block: \"nearest\" });
    if (Math.abs(box(snaps[cur]).left) < 1) destination = null;
  };
  const sync = () => {
    if (location.hash !== seenHash) return;
    if (destination !== null) {
      if (Math.abs(box(snaps[destination]).left) >= 1) return;
      destination = null;
    }
    let best = cur;
    for (let i = 0; i < snaps.length; i += 1)
      if (Math.abs(box(snaps[i]).left) < Math.abs(box(snaps[best]).left)) best = i;
    if (box(snaps[best]).left !== box(snaps[cur]).left) {
      cur = best;
      mark();
      writeHash(\"replace\");
    }
  };
  const readHash = () => {
    seenHash = location.hash;
    let key;
    try { key = decodeURIComponent(location.hash.slice(1)); } catch (_) { return; }
    if (!key) { go(0, null, true); return; }
    let i = routes.get(key);
    if (i === undefined) {
      const target = document.getElementById(key);
      if (!target) return;
      i = snaps.indexOf(target);
      if (i < 0) i = snaps.findIndex(s => stageOf(s).contains(target));
    }
    if (i >= 0) go(i, null, true);
  };
  addEventListener(\"scroll\", sync, { passive: true });
  addEventListener(\"hashchange\", readHash);
  for (const event of [\"wheel\", \"touchstart\", \"pointerdown\"])
    addEventListener(event, () => { destination = null; }, { passive: true });
  readHash();
  if (!location.hash) { sync(); writeHash(\"replace\"); }
  const skip = (i, dir) => {
    if (!reduce.matches) return i;
    while (snaps[i] && stageOf(snaps[i]) === stageOf(snaps[cur])) i += dir;
    if (!snaps[i]) return cur;
    while (i > 0 && stageOf(snaps[i - 1]) === stageOf(snaps[i])) i -= 1;
    return i;
  };
  addEventListener(\"keydown\", (e) => {
    if (e.ctrlKey || e.altKey || e.metaKey || e.defaultPrevented) return;
    const t = e.target;
    if (t instanceof Element &&
        (t.isContentEditable || /^(input|textarea|select|button)$/i.test(t.tagName))) return;
    let i = null;
    if (e.key === \"Home\") i = 0;
    else if (e.key === \"End\") {
      i = snaps.length - 1;
      while (reduce.matches && i > 0 && stageOf(snaps[i - 1]) === stageOf(snaps[i])) i -= 1;
    }
    else if ((e.key === \" \" && e.shiftKey) || e.key === \"ArrowLeft\" ||
        e.key === \"ArrowUp\" || e.key === \"PageUp\") i = skip(cur - 1, -1);
    else if ((e.key === \" \" && !e.shiftKey) || e.key === \"ArrowRight\" ||
        e.key === \"ArrowDown\" || e.key === \"PageDown\") i = skip(cur + 1, 1);
    if (i === null) return;
    e.preventDefault();
    go(i, \"push\");
  });
})();" := rfl

/-- The script's one emission site: a raw-text script node through the
typed tree — the emitter's `</script` payload guard covers it like every
script node — exactly when the class is `slides`. -/
def deckScriptNodes (deck : Bool) : Array Node :=
  if deck then #[Node.script #[] deckScript] else #[]

/-- The gate, definitionally: the node ships iff the deck asked for it —
the webpage fixture's byte-identity is the census half (no other class's
page moves). `_contract`'s grade, riding the definition. -/
theorem deck_script_gated (b : Bool) :
    deckScriptNodes b = if b then #[Node.script #[] deckScript] else #[] := rfl

/-- The slide sections' stylesheet, split by class. A deck (the `slides`
class) is one tree with two media renderings: on screen a paged
full-viewport deck laid out as a horizontal row — → is next, one snap
page per frame (and per overlay step), the scroll itself the motion —
paging natively on ←/→, Shift+wheel and swipe, and on every other key
through the constant script (`deckScript`); the scroller is the root
(`html` carries `scroll-snap-type`, which UAs apply to the viewport —
Scroll Snap 1 §4.1), so the keys need no focus. In print the stages page:
one frame or section page per sheet, the sheet the PDF's own page
(`deckPageRule`). A section page is one snap page like any frame, its
content centred on both axes. Every other class keeps the card rendering
on both media: deck rules and the script are the slides class's own,
which is what keeps the site port's webpage output unchanged. -/
private def slideCss (doc : Doc) : String :=
  -- The handout card, today's rendering, byte for byte: the only-media
  -- form for every non-deck class, the print twin for the deck.
  let handout :=
    s!"section.slide \{ border: {slideBorderPx}px solid var(--rule); border-radius: {slideRadiusPx}px;\n" ++
    s!"  padding: {slidePadV} {slidePadH}; margin: 0; break-inside: avoid; }\n" ++
    s!"* + section.slide \{ margin-top: {slidePadV}; }\n"
  -- The slide header's shared type rule, inside this split so the deck's
  -- screen override below can stand after it and win the cascade; the
  -- title's margins are the gap sheet's (`gapResets`).
  let headerH2 :=
    s!"section.slide > header h2 \{ font-size: {scaleSize "Large" "rem"}; }\n"
  if doc.docClass == .slides then
    let maxSteps := doc.body.foldl (fun n b => max n (Ir.frameSteps b)) 1
    -- The pre-reveal shade is spelled from the resolved design: the very
    -- fraction the PDF's cover mixes by (`Ir.Design.cover`, Core/Oklab),
    -- as the uncover's from-state and the floor's covered default. The
    -- type size on `main` is the PDF's own fontSize/stage-height ratio
    -- (`deck_type_is_stage_ratio`), printed in vh.
    headerH2 ++
      emitDeckRules (deckRules
        s!"{milliFactor (deckStageMilli doc.page.fontSize doc.page.height).toNat}vh"
        (deckPageSize doc.page) (Design.ofDoc doc).coveredFraction maxSteps)
  else handout ++ headerH2

/-- Whether the document carries a listing whose apparatus the stylesheet
must draw — a caption or line numbers: the gate on the listing CSS, so a
document without one ships exactly the stylesheet it shipped before. -/
private def docHasListing (doc : Doc) : Bool :=
  Ir.foldBlocks (fun b bl => b || match bl with
      | .verbatim _ _ spec => spec.caption.isSome || spec.numbers
      | _ => false)
    (fun b _ => b) false doc.body

/-- Whether the document carries a reference list: the gate on its rules,
so a document without one ships exactly the stylesheet it shipped before. -/
private def docHasBibliography (doc : Doc) : Bool :=
  Ir.foldBlocks (fun b bl => b || bl matches .bibliography ..) (fun b _ => b) false doc.body

/-- The reference list as the page sets it (`Layout.collectBibliography`),
from the same resolving sites: author-year entries hang their continuation
lines `\bibhang` in; numbered entries hang their labels right-aligned in a
column as wide as the widest label — a grid whose rows share its columns
(`subgrid`), since only the browser can measure a label — `\labelsep`
(.5em, article.cls:338) before the text; `\bibsep` between entries, its
default the page's value over the page's size, in `em` so it follows the
reader's type. A declared token reaches both as its custom property. -/
private def bibCss (doc : Doc) : String :=
  let hang := s!"var(--{Ir.bibHangName}, {cssLength (Ir.bibHang {}).width})"
  let size := doc.page.fontSize
  let sepMilli := (Ir.bibSepDefault size).width.sp * 1000 / (max size 1)
  let sep := s!"var(--{Ir.bibSepName}, {decMilli sepMilli}em)"
  s!"ul.bibliography \{ display: grid; row-gap: {sep}; padding: 0; list-style: none; }\n" ++
  s!"ul.bibliography.unmarked > li \{ padding-left: {hang}; text-indent: calc(-1 * {hang}); }\n" ++
  "ul.bibliography:not(.unmarked) { grid-template-columns: max-content minmax(0, 1fr);\n" ++
  "  column-gap: 0.5em; }\n" ++
  "ul.bibliography:not(.unmarked) > li { display: grid; grid-column: 1 / -1;\n" ++
  "  grid-template-columns: subgrid; }\n" ++
  ".bib-marker { text-align: right; }\n"

/-- The HTML projection of an OpenType feature record. Parameterized so
the backend agreement theorem ranges over the same value the live
stylesheet resolves below. -/
def kernCssFor (features : Ir.Features) : String :=
  if features.kern then "  font-kerning: normal;\n" else ""

/-- The kerning request from the one live feature value. -/
def kernCss : String := kernCssFor Ir.features

/-- Whether a declared style paints a colour of its own outside the inline
regions the document walk reads (`Ir.foldDoc` covers each style's font
template and marker): a heading's rule, a title page's separator, a link's
hover and focus inks, or a coloured run in the author line's template or a
title slot's. -/
def styleColored (st : ElementStyle) : Bool :=
  st.rule.isSome || st.separator.isSome || st.hover.isSome || st.focus.isSome ||
    st.color.isSome ||
    ((st.authorFont.getD #[]) :: st.slots.toList.flatMap (fun s =>
      s.parts.toList.flatMap fun p => [p.content, p.font.getD #[]])).any
      (Ir.foldInlines (fun a i => a || i matches .colored _ _ _) false)

/-- Whether a loaded image can paint on the page's own ground. Raster
transparency is explicit in the plan. An SVG can be transparent too, and
its PDF print face does not certify an opaque browser background. -/
def imageSeeThrough (en : Image.Loaded) : Bool :=
  imageShips en && match en.info with
    | some p => p.alpha != .opaque || Image.isSvg (resolvedSrc en) || en.webSvg.isSome
    | none => false

/-- Whether the page ships the dark colour scheme. Only the engine's own
token set has a proven dark variant (`Contrast.dark_contract`). A colour
the document chose — a palette entry, its own or a bundle's, an epoch's
palette, a coloured run anywhere the document sets one (`Ir.foldDoc`: the
body, the furniture, a style's templates), a rule or a picture, whose marks
paint the colour they declare, a style's own colours (`styleColored`), or
an image that lets the ground through (`imageSeeThrough`) — was judged
against the light ground (`Contrast`'s pairing judge) or not at all, and
the dark block would stand it on a ground no judge read it on: a declared
ink equal to the light default read 1.00:1 there, and a picture's or a
clear image's black ink about as much. Such a page declares the one scheme
its colours were judged in. The judge (`schemeFailures`) reads this same
decision. -/
def dualScheme (imgs : Image.Store) (doc : Doc) : Bool :=
  doc.palette.entries.isEmpty &&
    !Ir.foldBlocks (fun a b => a || b matches .setPalette _ || b matches .picture _ ||
        b matches .rule _ _ _) (fun a _ => a) false doc.body &&
    !Ir.foldDoc (fun a i => a || i matches .colored _ _ _) false doc &&
    !doc.styles.entries.any (styleColored ·.2) &&
    !imgs.entries.any imageSeeThrough

/-- **The dark variant ships only over the engine's own colours**
(`_contract`): a page that ships it declares no palette entry, no style
paints a colour of its own, and no image it shows lets the ground through
— the two sources review S-1 found the decision blind to, stated over the
decision the stylesheet and the judge both read. -/
theorem dualScheme_contract (imgs : Image.Store) (doc : Doc) (h : dualScheme imgs doc = true) :
    doc.palette.entries = #[] ∧
    (∀ e ∈ doc.styles.entries, styleColored e.2 = false) ∧
    (∀ en ∈ imgs.entries, imageSeeThrough en = false) := by
  simp only [dualScheme, Bool.and_eq_true, Bool.not_eq_true', Array.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨hp, _⟩, _⟩, hs⟩, hi⟩ := h
  refine ⟨hp, fun e he => ?_, fun en hen => ?_⟩
  · cases hc : styleColored e.2
    · rfl
    · have : doc.styles.entries.any (styleColored ·.2) = true := Array.any_eq_true'.mpr ⟨e, he, hc⟩
      simp [this] at hs
  · cases hc : imageSeeThrough en
    · rfl
    · have : imgs.entries.any imageSeeThrough = true := Array.any_eq_true'.mpr ⟨en, hen, hc⟩
      simp [this] at hi

/-- The class a float kind's `<figure>` carries: the selector its caption
scope's rule addresses. A figure is the plain float. -/
private def floatKindClass : Ir.FloatKind → String
  | .figure => "float"
  | .table => "table-float"
  | .sub => "subfloat"
  | .algorithm => "algorithm-float"

/-- Each float kind reads its own caption tokens before the document's,
the order `Ir.CaptionSkip.keys` resolves them in on the page, and places
them by the kind's declared position (`Ir.captionSides`, the one resolving
site): one custom-property indirection per kind and side — `--ltx-capsep`
facing the object and `--ltx-capfar` on the text side for a caption below,
the `-top` pair for one above — so a `\captionsetup[table]` gap reaches
tables and no figure. -/
private def captionScopeCss (pos : Array (String × Ir.CaptionPos)) : String :=
  let chain (s : Ir.CaptionSkip) (k : Ir.FloatKind) : String :=
    let dflt := match s with
      | .above => quantaRem (gapK "caption")
      | .below => "0px"
    (s.keys k).foldr (fun key acc => s!"var(--{key}, {acc})") dflt
  String.join ([Ir.FloatKind.figure, .table, .sub, .algorithm].map fun k =>
    let p := Ir.captionPosOf pos k
    let (obj, far) := Ir.captionSides p false
    let (objTop, farTop) := Ir.captionSides p true
    let s := k.captionScope
    s!"figure.{floatKindClass k} \{ --ltx-capsep: {chain obj k}; --ltx-capfar: {chain far k};\n" ++
    s!"  --ltx-capsep-top: {chain objTop k}; --ltx-capfar-top: {chain farTop k};\n" ++
    s!"  --ltx-capmargin: var(--{s}captionmargin, var(--captionmargin, 0px)); }\n")

/-- The HTML line-through rule thickness, derived from the one shared token
`Ir.lineThroughThickness` the PDF path also lowers (`Layout.lineThroughThickness`
aliases it), so a strike is one weight on either artifact. -/
def lineThroughThicknessCss : String := s!"{Ir.lineThroughThickness.toPtString}pt"

@[simp] theorem lineThroughThicknessCss_agree :
    lineThroughThicknessCss = s!"{Ir.lineThroughThickness.toPtString}pt" := rfl

/-- The base stylesheet. Small on purpose: a generated document should not
ship a framework to use four of its rules. Dark mode is a variant of the same
token set, not an inversion hack. The typography with an authority behind it
is derived above (`Ir.sizeScale` for the headings and standout,
`Ir.leadingMilli` and `bodyLeadingMilli` for the leadings); the remaining
paddings, margins, radii and breakpoints are this stylesheet's own screen
furniture — stated as the engine's choices, no external authority names
them, and each is overridable by a reader stylesheet, which is the HTML
backend's contract. -/
def baseCss (cfg : Config) (doc : Doc) : String :=
  -- The two token sets are `Contrast.light`/`Contrast.dark`, not literals
  -- here: every pairing they create is proved legible over there
  -- (`light_contract`, `dark_contract`), and a value only a backend knows
  -- would be a value no theorem covers.
  let lt := Contrast.light
  let dk := Contrast.dark
  let parskip := parskipVar doc.page
  let dual := dualScheme cfg.imgs doc
  ":root {\n" ++
  (if dual then "    color-scheme: light dark;\n" else "    color-scheme: light;\n") ++
  s!"    --measure: {measureEm doc.page};\n" ++
  parskip ++
  s!"    --ink: {cssColor lt.ink};\n" ++
  s!"    --surface: {cssColor lt.surface};\n" ++
  s!"    --muted: {cssColor lt.muted};\n" ++
  s!"    --accent: {cssColor lt.accent};\n" ++
  s!"    --tint: {cssColor lt.tint};\n" ++
  s!"    --rule: {cssColor lt.rule};\n" ++
  "    --font-body: Georgia, \"Times New Roman\", serif;\n" ++
  "    --font-sans: system-ui, -apple-system, \"Segoe UI\", sans-serif;\n" ++
  "    --font-mono: ui-monospace, SFMono-Regular, Menlo, monospace;\n" ++
  "}\n" ++
  (if !dual then "" else
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
  "}\n") ++
  -- The document's own declarations, after the dark variant: a declared
  -- token or font is the document's value in every scheme the page
  -- ships. A page with a declared colour ships one scheme (`dualScheme`),
  -- so the dark variant never stands a declared colour on a ground no
  -- judge read it on; a media query adds no specificity, so at the shared
  -- :root specificity source order is the whole cascade here — the same
  -- equal-specificity, order-decides contract the declared stylesheet
  -- link relies on below.
  (let tv := tokenVars cfg doc
   if tv.isEmpty then "" else ":root {\n" ++ tv ++ "\n}\n") ++
  "*, *::before, *::after { box-sizing: border-box; }\n" ++
  "body {\n" ++
  "  margin: 0;\n" ++
  s!"  padding: {quantaRem 3} 1.25rem {quantaRem 6};\n" ++
  "  background: var(--surface);\n" ++
  "  color: var(--ink);\n" ++
  "  font-family: var(--font-body);\n" ++
  -- 1rem: the reader's own declared size, the browser-consensus default.
  -- It also makes the screen rhythm rational — the unit is exactly
  -- `bodyLeadingMilli` milli-rem, so every gap `quantaRem` emits is an
  -- exact decimal.
  "  font-size: 1rem;\n" ++
  s!"  line-height: {milliFactor bodyLeadingMilli};\n" ++
  "  text-rendering: optimizeLegibility;\n" ++
  -- The same feature record the PDF path applies (Ir.features): the two
  -- artifacts request kerning from one value, agreement by the theorem
  -- `Pdf.features_agree` over this declaration.
  kernCss ++
  "  -webkit-font-smoothing: antialiased;\n" ++
  "}\n" ++
  "main { max-width: var(--measure); margin: 0 auto; }\n" ++
  -- Headings from the IR's own scale — the sizes the PDF sets
  -- (`Layout.sectionSize`, classes.dtx §Sectioning: the title at LARGE, a
  -- section at Large, a subsection at large), so `heading_hierarchy`'s
  -- ordering covers this backend for free; the line height is the
  -- engine's one leading ratio. Hand-picked decimals here once drifted a
  -- rounding step from the scale sixty lines above the rules generated
  -- from it. Margins are not declared here or on any block element: the
  -- resets and every boundary's one emitter are `blockGapRules`, all at
  -- zero specificity, where an element rule here would outrank them.
  "h1, h2, h3, h4 {\n" ++
  "  font-family: var(--font-sans);\n" ++
  "  font-weight: 600;\n" ++
  s!"  line-height: {milliFactor Ir.leadingMilli};\n" ++
  "  text-wrap: balance;\n" ++
  "}\n" ++
  s!"h1 \{ font-size: {scaleSize "LARGE" "rem"}; }\n" ++
  s!"h2 \{ font-size: {scaleSize "Large" "rem"}; }\n" ++
  s!"h3 \{ font-size: {scaleSize "large" "rem"}; }\n" ++
  -- hyphens follows the declared language: the browser's dictionaries on
  -- the same lang= tags the engine's patterns read — one declaration, two
  -- conforming hyphenators (the agreement is about tags, never breaks).
  "p { hyphens: auto; }\n" ++
  -- A list's items, a description's text under its label and a
  -- quotation's two edges stand their level's `\leftmargin` in, as the
  -- page sets them (`listIndentCss`).
  listIndentCss doc.docClass.record.lists ++
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
  -- The underline band comes from the font's own post metrics, as the PDF
  -- draws it (Font.band): CSS Text Decoration 4 §2.4.1 and §2.8.2 bind
  -- `from-font` to the face's declared thickness and position ("must"),
  -- so both backends declare the same band source. The old 0.15em offset
  -- and 1px thickness were neither sourced nor the font's.
  "a { color: inherit; text-decoration-thickness: from-font;\n" ++
  "    text-underline-position: from-font; text-decoration-skip-ink: auto; }\n" ++
  "u { text-decoration: underline; text-decoration-skip-ink: auto;\n" ++
  "    text-decoration-thickness: from-font; text-underline-position: from-font; }\n" ++
  s!"s \{ text-decoration-line: line-through; text-decoration-thickness: {lineThroughThicknessCss};\n" ++
  "    text-decoration-skip-ink: none; }\n" ++
  "a:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }\n" ++
  "code, pre { font-family: var(--font-mono); font-size: 0.925em; }\n" ++
  "pre > code { font-size: inherit; }\n" ++
  -- Flexbox 1 §4.5 gives scroll containers no automatic minimum size.
  -- Keep code at its content height; a crowded stage owns vertical scrolling.
  s!"pre \{ background: var(--tint); padding: {quantaRem 1} 1rem; overflow-x: auto;\n" ++
  "      border-radius: 4px; flex-shrink: 0; }\n" ++
  -- A captioned listing wears the figure-caption shape, caption above
  -- (listings' captionpos default); declared line numbers are a CSS
  -- counter the stylesheet draws before each line — furniture, outside
  -- the reader's selection and copy, no script. Emitted only when the
  -- document carries a listing that needs it.
  (if docHasListing doc then
    "figure.listing { margin: 0; }\n" ++
    s!"figure.listing > figcaption \{ text-align: center; margin-bottom: {quantaRem 1}; }\n" ++
    "pre.numbered { counter-reset: listing-line; }\n" ++
    "pre.numbered .line::before { counter-increment: listing-line;\n" ++
    "  content: counter(listing-line); display: inline-block; width: 2.25em;\n" ++
    "  padding-right: 1em; text-align: right; color: var(--muted);\n" ++
    "  user-select: none; }\n"
   else "") ++
  (if docHasBibliography doc then bibCss doc else "") ++
  alignScopeRule "centered" .center ++
  raggedRule .left ++ raggedRule .right ++
  -- A minipage's or a \parbox's content starts from no side of its own
  -- (`\@parboxrestore`, latex.ltx), whatever scope the box stands in.
  alignScopeRule "column" .left ++
  -- A table is a box in its scope's line (`alignScopeRule`); outside any
  -- scope it stands flush left, as it always did.
  "table { margin-left: var(--ltx-box-left, 0); margin-right: var(--ltx-box-right, auto); }\n" ++
  ".fill { flex: 1 1 auto; }\n" ++
  s!".spaced \{ margin-top: var(--sep, {slidePadV}); }\n" ++
  -- General rows keep the prior flex behavior. An exact pair switches to a
  -- grid that reserves the right max-content column before the left wraps.
  ".entry, .entry-row { display: flex; flex-wrap: wrap; column-gap: 0.4rem;\n" ++
  "  align-items: baseline; }\n" ++
  ".entry > .group + .group, .entry-row > .group + .group { margin-left: auto; }\n" ++
  -- A fill spans its line whatever the paragraph's alignment (TeX's glue
  -- orders, `Layout.setsToMeasure`): the first group starts at the left.
  ".entry > .group:first-child, .entry-row > .group:first-child { text-align: left; }\n" ++
  ".entry > .group:last-child, .entry-row > .group:last-child { text-align: right; }\n" ++
  ".entry-pair { display: grid;\n" ++
  "  grid-template-columns: minmax(0, 1fr) max-content; }\n" ++
  ".entry-rows { display: flex; flex-direction: column; }\n" ++
  ".sans { font-family: var(--font-sans); }\n" ++
  -- The other font-axis classes (fntguide §2.2 through `Ir.Style`): roman
  -- family, medium series, upright shape — each resets exactly its axis.
  ".rm { font-family: var(--font-body); }\n" ++
  ".md { font-weight: 400; }\n" ++
  ".up { font-style: normal; font-variant-caps: normal; }\n" ++
  ".ruled::after { content: \"\"; flex: 1; border-top: 1px solid var(--rule-color);\n" ++
  -- Half the x-height up from the baseline, in the rule's own inherited
  -- ex — the heading's face — where the PDF draws it (Layout.paraLineGeom;
  -- Hochuli: a rule relates to the type it cuts). A heading declaring
  -- `rule-position = baseline` overrides this per element (`styleRules`).
  "  transform: translateY(-0.5ex); }\n" ++
  -- Uniform small caps (CSS Fonts 4 §font-variant-caps: `all-small-caps`
  -- asks for c2sc + smcp), so mixed-case source sets at one height and the
  -- text carries the real casing. The browser uses the face's own small
  -- caps when it has them and synthesises otherwise, which is the better
  -- of the two mechanisms; the PDF path does the same from its own GSUB
  -- read, so the two backends agree on what \scshape means.
  ".sc { font-variant-caps: all-small-caps; }\n" ++
  -- booktabs' formal table: the three rule weights and their paddings come
  -- from the sourced constants in Ir (booktabs.dtx §The code), emitted
  -- here so the two backends cannot drift; each is overridable through
  -- its token (`--heavyrulewidth` etc. land in `tokenVars` when declared).
  -- Borders take `currentColor`, as the PDF path draws rules in `fg`. A
  -- header cell is a `th` for meaning only (`Ir.tableHeaderRows`): every
  -- cell rule addresses both tags, and the UA's bold, centred `th` is
  -- inherited away so the head sets exactly as its `td` did — the
  -- authored `\textbf` is what makes a head bold, in both backends.
  "table.booktabs { border-collapse: collapse; }\n" ++
  s!"table.booktabs td, table.booktabs th \{ padding: 0 var(--tabcolsep, {cssLength Ir.tabColSep});\n" ++
  "  vertical-align: top; }\n" ++
  "table.booktabs th { font-weight: inherit; text-align: inherit; }\n" ++
  "table.booktabs.nopadl tr > td:first-child,\n" ++
  "table.booktabs.nopadl tr > th:first-child { padding-left: 0; }\n" ++
  "table.booktabs.nopadr tr > td:last-child,\n" ++
  "table.booktabs.nopadr tr > th:last-child { padding-right: 0; }\n" ++
  s!"tr.bt-heavy-above > td, tr.bt-heavy-above > th \{ border-top: var(--heavyrulewidth, {cssLength Ir.heavyRuleWidth}) solid;\n" ++
  s!"  padding-top: var(--belowrulesep, {cssLength Ir.belowRuleSep}); }\n" ++
  s!"tr.bt-light-above > td, tr.bt-light-above > th \{ border-top: var(--lightrulewidth, {cssLength Ir.lightRuleWidth}) solid;\n" ++
  s!"  padding-top: var(--belowrulesep, {cssLength Ir.belowRuleSep}); }\n" ++
  s!"tr.bt-heavy-below > td, tr.bt-heavy-below > th \{ border-bottom: var(--heavyrulewidth, {cssLength Ir.heavyRuleWidth}) solid;\n" ++
  s!"  padding-bottom: var(--aboverulesep, {cssLength Ir.aboveRuleSep}); }\n" ++
  s!"tr.bt-light-below > td, tr.bt-light-below > th \{ border-bottom: var(--lightrulewidth, {cssLength Ir.lightRuleWidth}) solid;\n" ++
  s!"  padding-bottom: var(--aboverulesep, {cssLength Ir.aboveRuleSep}); }\n" ++
  s!"tr.bt-pre > td, tr.bt-pre > th \{ padding-bottom: var(--aboverulesep, {cssLength Ir.aboveRuleSep}); }\n" ++
  s!"td.bt-cmid, th.bt-cmid \{ border-top: var(--cmidrulewidth, {cssLength Ir.cmidRuleWidth}) solid;\n" ++
  s!"  padding-top: var(--belowrulesep, {cssLength Ir.belowRuleSep}); }\n" ++
  -- A natural `l`/`c`/`r` column is left to `auto`: the browser measures it,
  -- as the PDF path measures it from the fonts. CSS reality: `white-space`
  -- set on a `<col>` has no effect — only `width`, `background`, `border`
  -- and `visibility` apply to a column (CSS Tables §17.3). So the nowrap
  -- that stops auto-layout squeezing a natural column to min-content lands
  -- on its cells (`bt-nowrap`, placed in `tableCellNode`), inside `:where()`
  -- so it never outranks an authored rule.
  ":where(table.booktabs td.bt-nowrap, table.booktabs th.bt-nowrap)" ++
  " { white-space: nowrap; }\n" ++
  -- Float and caption gaps: the same tokens the PDF path reads, the
  -- defaults this context's own rhythm multiples of the declared rows
  -- (`Ir.rhythmGapQuanta`; the boundary rules live in `blockGapCss`).
  -- Pseudocode lists: nesting indents by the same token the PDF path
  -- reads (`--algindent`; algorithm2e's \SetInd{0.5em}{1em} + 0.4pt,
  -- ≈1.5em, following the type), and the declared line numbers are one
  -- CSS counter over every <li>, nested levels included — generated
  -- furniture, never content.
  "ol.algorithm { list-style: none; padding-left: 0; counter-reset: algline; }\n" ++
  "ol.algorithm ol { list-style: none; padding-left: var(--algindent, 1.5em); }\n" ++
  -- the class-default enumerate markers set ::marker content per level;
  -- pseudocode lists are not enumerates, so the content resets too
  "ol.algorithm li::marker, ol.algorithm ol > li::marker,\n" ++
  "ol.algorithm ol ol > li::marker, ol.algorithm ol ol ol > li::marker {\n" ++
  "  content: none; }\n" ++
  "ol.algorithm.numbered { padding-left: var(--algnumindent, 2em); position: relative; }\n" ++
  "ol.algorithm.numbered li { counter-increment: algline; }\n" ++
  -- one number column reserved inside the block, whatever the line's
  -- depth — the PDF's marker column over the same token (`algnumindent`,
  -- `Layout.collectAlgorithm`): algorithm2e's own inset, so a number
  -- stands in the algorithm's box and never in the page margin
  "ol.algorithm.numbered li::before { content: counter(algline);\n" ++
  "  color: var(--muted); font-size: 0.8em; width: 1.5em;\n" ++
  "  position: absolute; left: 0; text-align: right; }\n" ++
  "figure.float > table { margin-left: auto; margin-right: auto; }\n" ++
  "figure.float > img { display: block; margin: 0 auto; }\n" ++
  captionScopeCss doc.captionPos ++
  "figure.float > figcaption { margin-top: var(--ltx-capsep);\n" ++
  "  padding: 0 var(--ltx-capmargin) var(--ltx-capfar);\n" ++
  "  text-align: center; text-wrap: balance; }\n" ++
  -- The text-side skip is padding: it stands inside the float, beside
  -- the float's own separation, and a margin there would collapse into it.
  -- The object's own peer margin yields to the caption's skip facing it
  -- (`blockGapCss`'s caption boundary).
  "figure.float > figcaption:first-child { margin-top: 0;\n" ++
  "  padding-top: var(--ltx-capfar-top); padding-bottom: 0;\n" ++
  "  margin-bottom: var(--ltx-capsep-top); }\n" ++
  blockGapCss doc.docClass.record.lists doc.page.fontSize doc.tokens ++
  -- Slides: the class-split deck/handout rules, header type included
  -- (`slideCss`); the standout rule below holds on both media.
  slideCss doc ++
  -- A standout frame inverts: the palette's standout keys override, and
  -- without them the page's own fg/bg swap — the same rule as the PDF path.
  -- Its size is the scale's own Large step (`\Large\bfseries`, the shipped
  -- bundles' standout template), never a re-spelled decimal.
  "section.slide.standout { background: var(--standoutbg, var(--fg, #18181b));\n" ++
  "  color: var(--standoutfg, var(--bg, #fafaf9)); text-align: center;\n" ++
  s!"  font-size: {scaleSize "Large" "em"}; font-weight: 600;\n" ++
  "  display: flex; flex-direction: column; justify-content: center; }\n" ++
  sizeRules doc.page.scale ++
  -- The math face the document resolved, through its token — the `math`
  -- element selector reaches native MathML, whose engine default is the
  -- `math` generic family (MathML Core, user agent stylesheet); Chromium's
  -- MathML Core reads the web font's MATH table. The stack behind the var
  -- is the degraded state for a page with no shipped face.
  "math, .math { font-family: var(--font-math, \"Latin Modern Math\", \"STIX Two Math\", math); }\n" ++
  -- A display formula's block centres its line; the skips around it are
  -- the block boundary's (`blockGapCss`'s display rules, the tokens the
  -- PDF walk reads), never a margin on the formula element itself — one
  -- emitter per boundary, so a flex or block container realizes the same
  -- gap (`single_owner_gap_exact`).
  ".display { text-align: center; }\n" ++
  -- The numbered display: the formula's box takes the measure and centres
  -- its own text; the tag sits on the right edge, vertically centred on
  -- the formula (amsmath's equation shape).
  ".equation { display: flex; align-items: center; }\n" ++
  ".equation > .math { flex: 1 1 auto; text-align: center; }\n" ++
  "@media print {\n" ++
  "  body { background: #fff; color: #000; padding: 0; }\n" ++
  -- Paper has no scroll, and a scroll box is monolithic there, so it
  -- clips what runs past it: on paper a code block wraps a line wider than
  -- itself inside the box instead. A departure from LaTeX's verbatim, which
  -- overruns the measure: only such a line moves, and every character
  -- reaches the sheet.
  "  pre { overflow-x: visible; white-space: pre-wrap; overflow-wrap: anywhere; }\n" ++
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
  | .roman => "rm"
  | .medium => "md"
  -- unused: the styled arm emits `.series` as a per-run numeric
  -- `font-weight`, the value CSS matches faces by, never a class
  | .series w => s!"w{w.css}"
  | .upright => "up"
  | .size n => "size-" ++ n
  -- unused: arbitrary sizes emit one inline declaration.
  | .fontSize _ _ => "fontsize"
  -- unused: the styled arm emits `.lang` as a `lang` attribute, the
  -- declaration WCAG 2.2 SC 3.1.2 reads, never a class
  | .lang tag => "lang-" ++ tag

/-- The shares of a slide's leftover vertical space above and below its
content: the frame's declared distribution, projected from the one IR
table (`Ir.VAlign.shares` carries the sourcing) exactly as
`Layout.VDist.of` projects it for the PDF page — a backend may not read
another backend, so each projects the IR and `vdist_shares_agree` in
Tests states the agreement. A page-opening path owes a declared
distribution, never a default (the obligation table). -/
def vdistShares : Ir.VAlign → Nat × Nat := Ir.VAlign.shares

/-- The overlay attributes a step's wrapper carries: its range as data, and
the `--step` index the uncover reads. -/
def stepAttrs (n : Nat) (last : Option Nat) : Array (String × String) :=
  (#[("class", "step"), ("data-step", toString n)] ++
    (match last with
     | some u => #[("data-step-last", toString u)]
     | none => #[])) ++
    #[("style", s!"--step: {n}")]

/-- The declared end's own carrier, nested inside the step's wrapper when
the range has one. Two wrappers rather than one because one element
animates one property once: the start's uncover and the end's recover both
ride `opacity`, and opacities multiply through nesting — covered before the
start, full inside the range, covered again past the end, which is
`Ir.stepPending` (`html_step_pending_agree`). A range with no declared end
never covers again and gets no wrapper. -/
def stepEndNodes (tag : String) (last : Option Nat) (kids : Array Node) : Array Node :=
  match last with
  | none => kids
  | some u =>
    #[Html.elem tag kids
      #[("class", "step-end"), ("data-step-last", toString u),
        ("style", s!"--step-last: {u}")]]

/-- One alternation group, in its own wrapper. `first` is page order — the
group step 1 inks (`Ir.altShowsFirst_id`), so the other carries `hidden`
and every rendering with no snap state shows step 1's reading: the floor
with scripting off, the print handout, a page shipped with no stylesheet
at all. The class names which side of the spec the group stands on, read
from `Ir.altFirstWhenPending`, so the deck's per-snap selectors decide by
the same arithmetic the PDF page decides by (`alt_backend_agree`) instead
of re-deriving the selection here or in CSS. -/
def altGroupNode (tag : String) (n : Nat) (last : Option Nat) (first : Bool)
    (kids : Array Node) : Node :=
  let pendingSide := Ir.altFirstWhenPending n last == first
  Html.elem tag kids
    ((#[("class", if pendingSide then "alt alt-pending" else "alt alt-crisp"),
        ("data-step", toString n)] ++
      (match last with
       | some u => #[("data-step-last", toString u)]
       | none => #[])) ++
      (if first then #[] else #[("hidden", "hidden")]))

/-- The shared selector's finite projection, serialized as CSS whitespace
separated tokens. No backend interprets overlay source. -/
def overlayStepTokens (spec : Ir.OverlaySpec) (steps : Nat) : String :=
  String.intercalate " " ((spec.selectedSteps steps).map toString)

/-- Range animations need a multi-reveal track and positive, ordered
endpoints. Every other selector uses finite membership, including a
one-reveal frame and zero or reversed endpoints. -/
def overlayUsesRange (steps : Nat) (spec : Ir.OverlaySpec) : Bool :=
  (2 ≤ steps) && spec.more.isEmpty && (1 ≤ spec.first) &&
    match spec.last with
    | none => true
    | some u => spec.first ≤ u && u ≤ steps

/-- The optimized representation is used only inside the bounds its CSS
rules enumerate. Ordered endpoints also prevent two nested carriers from
covering the same content twice. -/
theorem overlayUsesRange_contract (steps : Nat) (spec : Ir.OverlaySpec)
    (h : overlayUsesRange steps spec = true) :
    2 ≤ steps ∧ spec.more = [] ∧ 1 ≤ spec.first ∧
      ∀ u, spec.last = some u → spec.first ≤ u ∧ u ≤ steps := by
  cases spec with
  | mk n last more =>
    cases more <;> cases last <;> simp_all [overlayUsesRange]

/-- One body carrier for an exact selector. Representable singletons keep
the range animation; finite membership uses the deck's numbered snap state.
Without that state the fully uncovered handout floor applies to both. -/
def overlayNode (tag : String) (steps : Nat) (spec : Ir.OverlaySpec)
    (kids : Array Node) : Node :=
  if overlayUsesRange steps spec then
    Html.elem tag (stepEndNodes tag spec.last kids)
      ((stepAttrs spec.first spec.last).push ("data-steps", overlayStepTokens spec steps))
  else
    Html.elem tag kids #[("class", "step-set"),
      ("data-steps", overlayStepTokens spec steps)]

/-- Both alternatives stay declared once, in page order. Their finite
membership sets are complementary at every numbered snap. -/
def overlayAltNode (tag : String) (steps : Nat) (spec : Ir.OverlaySpec)
    (first : Bool) (kids : Array Node) : Node :=
  if overlayUsesRange steps spec then altGroupNode tag spec.first spec.last first kids
  else
    Html.elem tag kids (#[("class", "alt alt-set"),
      ("data-steps", String.intercalate " " ((spec.pageSteps steps first).map toString))] ++
      if first then #[] else #[("hidden", "hidden")])

mutual

private def anchorIdsOne (acc : Array String) : Node → Array String
  | .elem _ attrs kids =>
    let ids := attrs.filterMap fun (key, value) => if key == "id" then some value else none
    anchorIdsList (acc ++ ids) kids.toList
  | .text _ | .style _ | .script _ _ => acc

private def anchorIdsList (acc : Array String) : List Node → Array String
  | [] => acc
  | x :: xs => anchorIdsList (anchorIdsOne acc x) xs

end

mutual

/-- Relocate only named anchors. All tags, content, links, accessibility
attributes and unrelated IDs remain the original typed nodes. -/
private def unanchorOne (ids : Array String) : Node → Node
  | .elem tag attrs kids => .elem tag
      (attrs.filter fun (key, value) => !(key == "id" && ids.contains value))
      (unanchorList ids #[] kids.toList)
  | .text s => .text s
  | .style css => .style css
  | .script attrs js => .script attrs js

private def unanchorList (ids : Array String) (acc : Array Node) : List Node → Array Node
  | [] => acc
  | x :: xs => unanchorList ids (acc.push (unanchorOne ids x)) xs

end

/-- An anchor shared by exclusive alternatives has one stable target outside
both carriers. Hidden DOM still owns its IDs (HTML's id uniqueness rule), so
copying a note reference or label into both branches would create duplicate
IDs and make backlinks depend on which hidden branch the browser finds first.
This is an artifact fact: the IR alternatives may share semantic identity. -/
def overlayAlternatives (tag : String) (steps : Nat) (spec : Ir.OverlaySpec)
    (first other : Array Node) : Array Node :=
  let otherIds := anchorIdsList #[] other.toList
  let shared := ((anchorIdsList #[] first.toList).filter otherIds.contains).toList.eraseDups.toArray
  let anchors := shared.map fun id =>
    Html.elem "span" #[] #[("id", id), ("data-alt-anchor", "")]
  anchors ++ #[overlayAltNode tag steps spec true (unanchorList shared #[] first.toList),
    overlayAltNode tag steps spec false (unanchorList shared #[] other.toList)]

/-- An artifact-specific projection of IR membership: matching a numbered
HTML token selects exactly the step layout selects, within the frame. -/
theorem overlay_membership_agree (spec : Ir.OverlaySpec) (steps k : Nat)
    (hk : 1 ≤ k) (hsteps : k ≤ steps) :
    (spec.selectedSteps steps).contains k = spec.selects k := by
  apply Bool.eq_iff_iff.mpr
  simp [Ir.OverlaySpec.selectedSteps_mem, hk, hsteps]

/-- Read covering from the representation `overlayNode` emits: range
selectors or a finite token set. The artifact chooses a representation,
never a different meaning for the selector. -/
def overlayPendingAt (steps : Nat) (spec : Ir.OverlaySpec) (k : Nat) : Bool :=
  if overlayUsesRange steps spec then htmlStepPendingAt steps spec.first spec.last k
  else !(spec.selectedSteps steps).contains k

/-- Covering agrees with the IR for every numbered selector and every
page in the frame; zero, reversed and union intervals need no exclusions. -/
theorem overlay_pending_agree (spec : Ir.OverlaySpec) (steps k : Nat)
    (hk : 1 ≤ k) (hsteps : k ≤ steps) :
    overlayPendingAt steps spec k = spec.pending k := by
  by_cases h : overlayUsesRange steps spec = true
  · obtain ⟨_, hmore, hn, hlast⟩ := overlayUsesRange_contract steps spec h
    have he : ∀ u, spec.last = some u → 1 ≤ u ∧ u ≤ steps := by
      intro u hu
      have hh := hlast u hu
      exact ⟨by omega, hh.2⟩
    simpa [overlayPendingAt, h, Ir.OverlaySpec.pending, Ir.OverlaySpec.selects,
      Ir.OverlaySpec.ranges, hmore] using
      html_step_pending_agree steps spec.first k spec.last hn hk he
  · unfold overlayPendingAt
    rw [ite_eq_right h, overlay_membership_agree spec steps k hk hsteps]
    rfl

/-- Read page-order alternation from either representation actually emitted
by `overlayAltNode`. The first page is still the script-free reading. -/
def overlayFirstAt (steps : Nat) (spec : Ir.OverlaySpec) (k : Nat) : Bool :=
  if overlayUsesRange steps spec then altShownFirstAt steps spec.first spec.last k
  else (spec.pageSteps steps true).contains k

/-- Both artifacts select the same alternative for an arbitrary selector.
The contract is shared by replacements, conditional styles and any payload
carried through `OverlaySpec.pageOrder`. -/
theorem overlay_alternation_agree (spec : Ir.OverlaySpec) (steps k : Nat)
    (hk : 1 ≤ k) (hsteps : k ≤ steps) :
    overlayFirstAt steps spec k = spec.showsFirst k := by
  by_cases h : overlayUsesRange steps spec = true
  · obtain ⟨_, hmore, hn, hlast⟩ := overlayUsesRange_contract steps spec h
    have he : ∀ u, spec.last = some u → 1 ≤ u ∧ u ≤ steps := by
      intro u hu
      have hh := hlast u hu
      exact ⟨by omega, hh.2⟩
    simpa [overlayFirstAt, h, Ir.altShowsFirst, Ir.OverlaySpec.showsFirst,
      Ir.OverlaySpec.pending, Ir.OverlaySpec.selects, Ir.OverlaySpec.ranges, hmore] using
      alt_backend_agree steps spec.first k spec.last hn hk he
  · apply Bool.eq_iff_iff.mpr
    simp [overlayFirstAt, h, Ir.OverlaySpec.pageSteps_mem, hk, hsteps]

/-- Does a string carry anything to read: a character that is not white
space. The one blankness test for an accessible name, here and in the
judge (`carriesName`): accname 1.2 does not take a name that is empty once
trimmed of white space. -/
def nonBlank (s : String) : Bool := s.toList.any (!·.isWhitespace)

/-- The first of two strings that carries anything to read. -/
def firstNonBlank (a b : String) : String := if nonBlank a then a else b

theorem firstNonBlank_contract (a b : String) (hb : nonBlank b = true) :
    nonBlank (firstNonBlank a b) = true := by
  unfold firstNonBlank
  split
  · assumption
  · exact hb

/-- What a picture is called when nothing it says is known: the locale's
figure word, and the engine's English word only where a locale carries
none. -/
def figureWord (loc : Locale) : String := firstNonBlank loc.figure "figure"

theorem figureWord_contract (loc : Locale) : nonBlank (figureWord loc) = true :=
  firstNonBlank_contract _ _ (by decide)

/-- An attribute's value on an element's attribute list. -/
def attrOf? (attrs : Array (String × String)) (k : String) : Option String :=
  (attrs.find? (·.1 == k)).map (·.2)

/-- An `<img>`'s alternative, a function of its one `Alt` by construction.
Described, `alt` the text (WCAG 2.2 technique H37); decorative, `alt=""`
with `role="presentation"`, the declared decorative role the page judge
reads (`a11yElem`); undeclared, `alt=""` — what the engine has always
shipped there, kept, and named by N0376 instead. -/
def imgAltAttrs : Ir.Alt → Array (String × String)
  | .described t => #[("alt", t)]
  | .decorative => #[("alt", ""), ("role", "presentation")]
  | .undeclared => #[("alt", "")]

/-- A picture or image placeholder's role and name project its one
alternative. Described, `role="img"` makes its children presentational
(WAI-ARIA 1.2 §5.3) and `aria-label` names it; decorative,
`aria-hidden="true"` removes it from the accessibility tree; undeclared,
the locale's figure word supplies a name. -/
def pictureAltAttrs (floor : String) : Ir.Alt → Array (String × String)
  | .described t => #[("role", "img"), ("aria-label", firstNonBlank t floor)]
  | .decorative => #[("aria-hidden", "true")]
  | .undeclared => #[("role", "img"), ("aria-label", floor)]

/-- Absolute font size and leading keep their physical lengths in the IR;
on a deck they use the body's stage-height share (`deck_type_is_stage_ratio`),
so they scale with its named size ladder. Context-dependent expressions keep
their CSS resolution rather than being evaluated against a guessed measure. -/
private def fontLengthCss (cfg : Config) (e : Affine Measure) : String :=
  if cfg.deck && e.rigidAbsolute && !(e.anyRef fun _ => true) then
    let length := (e.eval fun _ => {}).width.sp
    s!"{decMilli (deckStageMilli length cfg.page.height)}vh"
  else Ir.Track.contextCss e

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
    -- text width is a percentage — HTML's measure is the container, which
    -- is also what the PDF resolves it against (`Layout.collectPara`: the
    -- current measure, minipage semantics). In flow classes an absolute
    -- length is `pt` — paper is paper — and a `\textheight` fraction has
    -- no CSS analog, so the intrinsic size stands. On the paged deck
    -- (`cfg.deck`) the stage is the viewport, so every stage-resolved
    -- dimension is emitted as its share of the stage (`deckStageMilli`,
    -- `image_share_agrees`): absolute lengths and `\textheight` fractions
    -- become `vw`/`dvh` — a print length on a stage that is the viewport
    -- was the "very small image" defect. `height: auto` (or width) keeps
    -- the browser on the intrinsic ratio, the same invariant the PDF path
    -- proves.
    let index? := cfg.imgs.findRequest? (size.request src)
    let loaded? := index?.bind cfg.imgs.get?
    let info? := loaded?.bind (·.info)
    let canvas? := loaded?.bind (·.canvasSize)
    let pixels? : Option (Nat × Nat) := info?.map fun inf =>
      match canvas? with
      | some (w, h) => (cssPxOfSp w, cssPxOfSp h)
      | none => intrinsicPx inf
    -- A boundary picture with no face in the store ships its request key as
    -- the `src`, which draws nothing, so the text alternative is all that
    -- reaches the page: never decorative. With no author text it is named
    -- by what it is (`figureWord`); the loss's own code is the fulfilment's
    -- to carry, and `Image.Loaded` keeps none.
    let alt := if src.startsWith Ir.picSrcPrefix && info?.isNone then
        (match alt with
          | .undeclared => .described (figureWord cfg.locale)
          | .decorative => .decorative
          | .described t => .described t) else alt
    -- The link names the copy published beside the page (`imageHref`) —
    -- or, for an entry that ships none, the file on disk: a bare graphicx
    -- name resolved to a file with an extension must name that file, not
    -- the spelling in the source.
    let href := imageRequestHref cfg.assetsDir cfg.imgs (size.request src)
    let horizontal (l : Image.Len) : Bool :=
      l.value.anyRef fun m => m != .textHeight
    let vertical (l : Image.Len) : Bool :=
      l.value.anyRef (· == .textHeight)
    let cssDim (l : Image.Len) (isVertical : Bool) : Option String :=
      if vertical l then none
      else if isVertical then some (Ir.Track.contextCss l.value)
      else some (Ir.Track.css (.affine l.value))
    let deckDim (l : Image.Len) (isVertical : Bool) : Option String :=
      if horizontal l && !vertical l then
        some (if isVertical then Ir.Track.contextCss l.value
          else Ir.Track.css (.affine l.value))
      else if !horizontal l then
        let (stage, unit) :=
          if isVertical then (cfg.page.height, "dvh") else (cfg.page.width, "vw")
        let textW := cfg.page.width - 2 * cfg.page.hmargin
        let textH := cfg.page.height - 2 * cfg.page.vmargin
        some (decMilli (deckStageMilli (l.resolve textW textH) stage) ++ unit)
      else none
    let dim (l : Image.Len) (vertical : Bool) : Option String :=
      if cfg.deck then deckDim l vertical else cssDim l vertical
    let wCss := size.width.bind (dim · false)
    let hCss := size.height.bind (dim · true)
    -- In a fill row a text-width fraction is the row's (`Config.inFillRow`),
    -- in `cqi`, after the percentage a browser without container units keeps.
    let wRow := size.width.bind fun l =>
      if cfg.inFillRow && horizontal l && !vertical l then
        some (Ir.Track.contextCss l.value)
      else none
    let width (w : String) : String := match wRow with
      | some r => s!"width: {w}; width: {r}"
      | none => s!"width: {w}"
    let style : Option String :=
      match wCss, hCss with
      | some w, some h =>
        -- `keepaspectratio` is graphicx's fit: the box is the image scaled
        -- by the smaller of the two ratios (`Image.resolveSize`), so the box
        -- is what it draws, never a letterbox around it.
        match size.keepAspect, pixels? with
        | true, some (pw, ph) =>
          let (rw, rh) := canvas?.getD (Int.ofNat pw, Int.ofNat ph)
          let floor := if wRow.isSome then s!"width: {w}; " else ""
          some (s!"{floor}width: min({wRow.getD w}, calc({h} * {rw} / {rh})); " ++
            "height: auto")
        | true, none => some s!"{width w}; height: {h}; object-fit: contain"
        | false, _ => some s!"{width w}; height: {h}"
      | some w, none => some s!"{width w}; height: auto"
      | none, some h => some s!"height: {h}; width: auto"
      | none, none =>
        if size.width.isNone && size.height.isNone &&
            (size.scaleNum != 1 || size.scaleDen != 1) then
          (loaded?.bind (·.size?)).map fun (iw, _) =>
            let scaled := iw * size.scaleNum / size.scaleDen
            if cfg.deck then
              s!"width: {decMilli (deckStageMilli scaled cfg.page.width)}vw; height: auto"
            else
              s!"width: {Dim.Sp.toPtString scaled}pt; height: auto"
        else none
    -- animate §6.1 fixes the canvas to frame one. A later poster's natural
    -- ratio must not replace it once the browser decodes the image.
    let style := match canvas? with
      | some (w, h) =>
        let ar := s!"aspect-ratio: {w} / {h}; object-fit: fill"
        some (match style with | some s => s ++ "; " ++ ar | none => ar)
      | none => style
    let requestAttrs := match index? with
      | some k => if loaded?.any pdfPageImg then #[("data-image-index", toString k)] else #[]
      | none => #[]
    if loaded?.any (·.webError.isSome) then
      let attrs := pictureAltAttrs (figureWord cfg.locale) alt
      let label := (attrOf? attrs "aria-label").getD ""
      -- A failed conversion still reserves the exact intrinsic pixel box, so
      -- the page keeps the same geometry a successful face would have.
      let dims := match pixels? with
        | some (pw, ph) => [s!"width: {pw}px", s!"height: {ph}px"]
        | none => []
      let styleText := String.intercalate "; "
        (["display: inline-block"] ++ dims ++ (style.map (fun s => [s])).getD [])
      acc.push (Html.elem "span" #[Html.text label]
        (attrs ++ requestAttrs ++ #[("data-image-src", href),
          ("style", styleText)]))
    else
    let attrs := #[("src", href)] ++ requestAttrs ++ imgAltAttrs alt ++
      (match pixels? with
       | some (pw, ph) =>
         #[("width", toString pw), ("height", toString ph)]
       | none => #[]) ++
      (match style with
       | some st => #[("style", st)]
       | none => #[])
    let img := Html.elem "img" #[] attrs
    acc.push (match imagePosterHref cfg.assetsDir cfg.imgs (size.request src) with
      | some poster => Html.elem "picture" #[
          Html.elem "source" #[] #[("media", "print, (prefers-reduced-motion: reduce)"),
            ("srcset", poster)], img]
      | none => img)
  | .math display src =>
    -- Until native MathML lands for what the parser cannot model, the
    -- element's own text is the floor — the formula's content, never its
    -- markup (`Ir.floorInk_mem`). The source rides in a data attribute,
    -- where an optional client-side renderer can find it and no reader is
    -- shown a control sequence.
    let tag := if display then "div" else "span"
    acc.push (Html.elem tag #[Html.text (Ir.mathFloor src)]
      #[("class", if display then "math math-display" else "math"),
        ("data-tex", src)])
  | .formula display src body =>
    -- Native MathML Core from the parsed atoms — the same math AST the PDF
    -- lays out; the census theorem (MathMl.mathml_glyphs_agree) holds the
    -- element's leaf text to the formula's glyph text. The TeX source
    -- still rides in data-tex so the opt-in --math-boundary client
    -- renderer can find and replace the element; without the tool the
    -- MathML itself is the rendering — MathML Core is in every current
    -- engine (caniuse.com/mathml, 2026: Chromium 109+, Firefox, Safari).
    acc.push (MathMl.formula display
      #[("class", if display then "math math-display" else "math"),
        ("data-tex", src)] body (mathMarks cfg))
  | .styled st body =>
    let kids := inlineNodesInto { cfg with mathStyles := cfg.mathStyles.push st } #[] body.toList
    match st with
    | .bold => acc.push (Html.elem "strong" kids)
    | .italic => acc.push (Html.elem "em" kids)
    | .emph => acc.push (Html.elem "em" kids)
    | .mono => acc.push (Html.elem "code" kids)
    | .normal => acc ++ kids
    -- A series is the numeric weight per run (CSS Fonts 4 §2.2): the
    -- browser matches it against the `@font-face` weights the emission
    -- ships, the same `(slot, weight, italic)` selection the PDF resolves
    -- through `FontSet.lookup` (`Layout.weight_agree`).
    | .series w =>
      acc.push (Html.elem "span" kids #[("style", s!"font-weight: {w.css}")])
    | .fontSize size leading =>
      acc.push (Html.elem "span" kids #[
        ("style", s!"font-size:{fontLengthCss cfg size};line-height:{fontLengthCss cfg leading}")])
    -- The language of a run is a declaration, not a style: the span
    -- carries `lang` (HTML §3.2.6.2; WCAG 2.2 SC 3.1.2), which CSS
    -- `hyphens: auto` and assistive technology both read.
    | .lang tag => acc.push (Html.elem "span" kids #[("lang", tag)])
    | other => acc.push (Html.elem "span" kids #[("class", styleClass other)])
  | .role n body =>
    -- The class hook survives as an addressable class. A title-part role
    -- also projects its exact size and baseline skip from the one IR part;
    -- ordinary authored roles remain style-free.
    let part := Ir.titlePartOf ((cfg.styles.find? "titlepage").getD {}).slots n
    let style := part.bind fun p =>
      let decls :=
        (p.size.map fun z => s!"font-size:{fontLengthCss cfg (.lit z)};").toList ++
        (p.leading.map fun z => s!"line-height:{fontLengthCss cfg (.lit z)};").toList
      if decls.isEmpty then none else some (String.join decls)
    let attrs := #[some ("class", roleClass n), style.map ("style", ·)].filterMap id
    let inner := match part with
      | some p =>
        match p.size with
        | some size =>
          -- Cancellation reads the size component of TextStyle.metrics;
          -- a missing title leading contributes no attachment dimension.
          let st := Ir.Style.fontSize (.lit size) (.lit (p.leading.getD size))
          { cfg with mathStyles := cfg.mathStyles.push st }
        | none => cfg
      | none => cfg
    acc.push (Html.elem "span" (inlineNodesInto inner #[] body.toList) attrs)
  | .colored c name body =>
    -- A named colour becomes a custom-property reference with the literal as
    -- fallback, so the token really is the styling API: a host page can
    -- restyle the document by redefining --primary.
    let value := match name with
      | some n => s!"color: var(--{n}, {cssColor c})"
      | none => s!"color: {cssColor c}"
    acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList) #[("style", value)])
  | .located _ body => inlineNodesInto cfg acc body.toList
  | .link url body =>
    acc.push (Html.elem "a" (inlineNodesInto cfg #[] body.toList)
      #[("href", url), ("style", "color: inherit")])
  -- The anchor a cross-reference lands on: an empty span carrying the
  -- label's id, through the typed tree and the attribute escaper (the key
  -- is author text entering an attribute; `Ir.labelAnchor_single_token`
  -- holds its shape).
  | .label key =>
    acc.push (Html.elem "span" #[] #[("id", Ir.labelAnchor key)])
  -- A resolved reference is an in-page link showing its number; an
  -- unresolved one shows LaTeX's own '??', already diagnosed by name
  -- (W0349), with nothing to link to.
  | .ref _ _ text target =>
    match target with
    | some a =>
      acc.push (Html.elem "a" #[Html.text text]
        #[("href", "#" ++ a), ("style", "color: inherit")])
    | none => acc.push (Html.text text)
  | .decorated kind body =>
    let tag := match kind with
      | .underline => "u"
      | .lineThrough => "s"
    acc.push (Html.elem tag (inlineNodesInto cfg #[] body.toList))
  | .onSteps spec body =>
    -- Every step is fully visible here — the handout state, the floor the
    -- deck's reveal degrades to. On the paged deck the class-gated
    -- stylesheet uncovers the step in place as the reader's arrow
    -- advances the frame's snap points (`deckStepCss`); the `--step`
    -- index names its snap point, and the range rides as data either way.
    -- A declared end rides its own nested carrier (`stepEndNodes`), which
    -- is what covers the step again past it.
    acc.push (overlayNode "span" cfg.overlaySteps spec (inlineNodesInto cfg #[] body.toList))
  | .altSteps spec firstPage otherPage =>
    -- One wrapper per group, each carrying the range and its side: the
    -- deck's snap rules show exactly one (`alt_backend_agree`), and with
    -- no snap state the group stored first is what shows. Both groups stay
    -- in the tree because the document declares both; selection is
    -- `display`-level, never `step`'s covering.
    acc ++ overlayAlternatives "span" cfg.overlaySteps spec
      (inlineNodesInto cfg #[] firstPage.toList) (inlineNodesInto cfg #[] otherPage.toList)
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
  -- Glue is room in the line, not ink. Infinite stretch keeps the fill
  -- carrier; a finite component remains its authored inline offset.
  | .hspace e _ =>
    let finite := e.withoutFil
    let room := Ir.Track.css (.affine finite)
    let node := Html.elem "span" #[] #[("style", s!"margin-inline-start:{room}")]
    if e.hasFil then
      (acc.push node).push (Html.elem "span" #[] #[("class", "fill")])
    else acc.push node
  | .rule width height raise =>
    let w := Ir.Track.css (.affine width)
    let h := Ir.Track.contextCss height
    let r := Ir.Track.contextCss raise
    acc.push (Html.elem "span" #[] #[
      ("style", s!"display:inline-block;inline-size:{w};block-size:{h};vertical-align:{r};background:currentColor")])
  -- A strut props its line open in print; a continuous page reads at its
  -- own line-height, so the carrier is empty and adds no box.
  | .strut _ => acc
  -- An italic correction is TeX's kern; a browser sets its own italics.
  | .italicCorr _ => acc
  -- An unresolved citation shows its marks; resolution would have replaced
  -- this node with the style's linked inlines, and the diagnostic that let
  -- it through already named the gap.
  | .cite _ keys => acc.push (Html.text (Ir.citeMarks keys))
  -- The mark: a superscripted link to the note's endnote entry (W3C
  -- DPUB-ARIA 1.1, doc-noteref). The body renders once, in the one
  -- doc-endnotes section before the article end — never twice.
  | .footnote num _ =>
    let n := num.getD 0
    acc.push (Html.elem "sup"
      #[Html.elem "a" #[Html.text (toString n)]
        #[("href", s!"#fn{n}"), ("id", s!"fnref{n}"),
          ("role", "doc-noteref"), ("style", "color: inherit")]])
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

/-- The tag of a table cell: `th` in the header prefix `Ir.tableHeaderRows`
names, `td` below it. -/
def tableCellTag (headerRows i : Nat) : String :=
  if i < headerRows then "th" else "td"

theorem tableCellTag_th_iff (headerRows i : Nat) :
    tableCellTag headerRows i = "th" ↔ i < headerRows := by
  unfold tableCellTag
  split
  · simp_all
  · simp_all

private def readsInlineMeasure (e : Affine Measure) : Bool :=
  e.anyRef (· != .textHeight)

/-- Whether an emitted inline property reads `cqi`. The leaf runs through
`Ir.foldInlines`, so nested styles and roles are covered by the shared IR
walk rather than a backend-specific recursion. -/
private def contextUnitLeaf (found : Bool) : Inline → Bool
  | .styled st _ => found || match st with
    | .fontSize size leading => readsInlineMeasure size || readsInlineMeasure leading
    | .bold | .italic | .mono | .smallcaps | .emph | .sans | .normal | .roman
    | .medium | .series _ | .upright | .size _ | .lang _ => false
  | .rule _ height raise =>
    found || readsInlineMeasure height || readsInlineMeasure raise
  | .image _ size _ => found || size.height.any fun l =>
    readsInlineMeasure l.value && !l.value.anyRef (· == .textHeight)
  | .text _ | .math _ _ | .formula _ _ _ | .colored _ _ _ | .located _ _ | .role _ _
  | .link _ _ | .decorated _ _ | .onSteps _ _ | .altSteps _ _ _ | .fill
  | .hspace _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount
  | .icon _ _ | .label _ | .ref _ _ _ _ | .cite _ _ | .footnote _ _
  | .linebreak _ => found

private def usesContextUnit (xs : Array Inline) : Bool :=
  Ir.foldInlines contextUnitLeaf false xs

/-- One table cell: its column's alignment as inline style (the PDF path
reads the same `ColSpec.align`), the `bt-cmid` class when a `\cmidrule`
spans its column, and — for a header cell — `scope=col`, the one scope a
booktabs head declares (HTML §4.9.10: a `th` heading the cells below it).
A `\multicolumn` head takes its own spec's alignment and `colspan` for the
columns it covers (HTML §4.9.11), the layout's `spanBox`. Plain cells
carry the same `inlines` a `td` carried; a cell whose emitted dimensions
read `cqi` puts those inlines in its content-measure container. -/
def tableCellNode (cfg : Config) (cols : Array Ir.ColSpec) (cmids : Array (Nat × Nat))
    (spans : Array Ir.ColSpan) (headerRows i j : Nat) (cell : Array Inline) : Node :=
  let sp := spans.find? fun s => s.row == i && s.col == j
  let align : Ir.HAlign := match sp with
    | some s => s.spec.align
    | none => (cols[j]?.map (·.align)).getD .left
  let al := match align with
    | .center => #[("style", "text-align: center")]
    | .right => #[("style", "text-align: right")]
    | .left => #[]
  let al := match sp with
    | some s => if 2 ≤ s.n then al.push ("colspan", toString s.n) else al
    | none => al
  -- A natural `l`/`c`/`r` column is left to CSS `auto`; its cells carry
  -- `bt-nowrap` so auto table layout cannot squeeze the column to
  -- min-content (the `:where(... td.bt-nowrap ...)` rule above). `white-space`
  -- on the `<col>` itself would do nothing (CSS Tables §17.3), so the class
  -- lands here, on the cell. Combined with `bt-cmid` into one class value, as
  -- a cell carries at most one `class` attribute.
  let isNatural : Bool := match sp with
    | some s => (s.spec.width matches .natural)
    | none => ((cols[j]?.map (·.width)).getD .natural matches .natural)
  let cmid := cmids.any (fun (a, b) => a ≤ j + 1 && j + 1 ≤ b)
  let classes : Array String :=
    (if cmid then #["bt-cmid"] else #[]) ++ (if isNatural then #["bt-nowrap"] else #[])
  let attrs := if classes.isEmpty then al
    else al.push ("class", " ".intercalate classes.toList)
  let attrs := if i < headerRows then attrs.push ("scope", "col") else attrs
  let width : Ir.ColWidth := match sp with
    | some s => s.spec.width
    | none => (cols[j]?.map (·.width)).getD .natural
  let child := match width with
    | .sized e => cfg.atMeasure
      (e.resolveWidth (MeasureValues.horizontal cfg.measureValues.lineWidth 0))
    | .natural | .flex _ => cfg
  let content := inlines child cell
  -- Chromium does not resolve query units against a table-cell container.
  -- A block inside the cell has the same content measure and works in both
  -- screen and print; emit it only where a descendant actually reads cqi.
  let content := if usesContextUnit cell then
      #[Html.elem "div" content
        #[("class", "cell-measure"), ("style", "container-type: inline-size")]]
    else content
  Html.elem (tableCellTag headerRows i) content attrs

/-- Is cell `(i, j)` covered by a `\multicolumn` head to its left? Such a
cell has no element of its own: the head's `colspan` is its place. -/
def coveredBySpan (spans : Array Ir.ColSpan) (i j : Nat) : Bool :=
  spans.any fun s => s.row == i && s.col < j && j < s.col + s.n

/-- The cells of row `i`, in column order, the span-covered ones left out. -/
def tableRowCells (cfg : Config) (cols : Array Ir.ColSpec) (cmids : Array (Nat × Nat))
    (spans : Array Ir.ColSpan) (headerRows i : Nat) (row : Array (Array Inline)) :
    Array Node :=
  (Array.range row.size).filterMap fun j =>
    if coveredBySpan spans i j then none
    else some (tableCellNode cfg cols cmids spans headerRows i j (row[j]?.getD #[]))

/-- A cell is a `th` exactly when its row lies in the header prefix — the
HTML projection of `Ir.tableHeaderRows`, stated over the typed tree the
table arm builds: every cell element of row `i` is `th` iff
`i < headerRows`, whatever the column, the alignment, the cmid rules, or
the spans. -/
theorem th_iff_header_row (cfg : Config) (cols : Array Ir.ColSpec)
    (cmids : Array (Nat × Nat)) (spans : Array Ir.ColSpan) (headerRows i : Nat)
    (row : Array (Array Inline)) (nd : Node)
    (h : nd ∈ tableRowCells cfg cols cmids spans headerRows i row) :
    nd.tag? = some "th" ↔ i < headerRows := by
  simp only [tableRowCells, Array.mem_filterMap] at h
  obtain ⟨j, _, hj⟩ := h
  split at hj
  · exact absurd hj (by simp)
  · simp only [Option.some.injEq] at hj
    subst hj
    simp only [tableCellNode, Html.elem, Html.Node.tag?, Option.some.injEq]
    exact tableCellTag_th_iff headerRows i

/-- Project a relative track hint to CSS, falling back to the declared affine
width or natural sizing. CSS table layout still measures content and padding. -/
def colElOf (shares : Array (Option Nat)) (j : Nat) (c : Ir.ColSpec) : Node :=
  match shares[j]? with
  | some (some p) => Html.elem "col" #[] #[("style", s!"width: {Ir.percentCss p}")]
  | _ => match c.width with
    | .sized e => Html.elem "col" #[] #[("style", s!"width: {Ir.Track.css (.affine e)}")]
    | .flex _ | .natural => Html.elem "col" #[] #[]

/-- One column node per typed column, preserving order. Relative hints use
`Ir.tableColShares`; tables without a flexible target keep their declared widths. -/
def tableColEls (cols : Array Ir.ColSpec) (target : Option Ir.TableTarget) : Array Node :=
  let shares : Array (Option Nat) := match target with
    | some t => Ir.tableColShares cols t
    | none => cols.map fun _ => none
  cols.mapIdx (colElOf shares)

/-- The CSS width spelling is the projection of the IR's relative hint.
This is a tree-emission fact, not a claim about the browser's measured width. -/
theorem tableColEls_share_projects (shares : Array (Option Nat)) (j : Nat)
    (c : Ir.ColSpec) (p : Nat) (h : shares[j]? = some (some p)) :
    colElOf shares j c = Html.elem "col" #[] #[("style", s!"width: {Ir.percentCss p}")] := by
  simp [colElOf, h]

/-- A natural column is projected to a bare `<col>` with no width — CSS `auto`
— the HTML half of "naturals are excluded from the target split"
(`Ir.tableColShares_natural_exact` gives it the `some none` share; the nowrap that
keeps it from collapsing lands on its cells, `tableCellNode`). -/
theorem tableColEls_natural_projects (shares : Array (Option Nat)) (j : Nat)
    (c : Ir.ColSpec) (hc : c.width = .natural) (h : shares[j]? = some none) :
    colElOf shares j c = Html.elem "col" #[] #[] := by
  simp [colElOf, h, hc]

/-- booktabs' formal table. Rules land as border classes on the row they
precede (`-below` on the last row for a rule written after it), and the
stylesheet draws each class at the sourced weight with its declared
padding — `Ir.heavyRuleWidth` and friends drive both backends from one
site. The rows before the first `\midrule` (`Ir.tableHeaderRows`) are the
head: they ship under `<thead>` as `<th scope=col>`, the rest under
`<tbody>` as `<td>`; a table with no head has no `<thead>`, one that is
all head has no `<tbody>`. The grouping is semantic only — the stylesheet
neutralises the UA's bold, centred `th` so the raster is the `td` one. A
`gap` rule and `\cmidrule` end-trimming have no HTML spelling yet; the
PDF path carries both. -/
def tableNode (cfg : Config) (cols : Array Ir.ColSpec) (padL padR : Bool)
    (rows : Array (Array (Array Inline))) (rules : Array (Nat × Ir.TableRule))
    (spans : Array Ir.ColSpan) : Node :=
  let headerRows := Ir.tableHeaderRows rows rules
  let ruleAt (i : Nat) : Array Ir.TableRule :=
    rules.foldl (fun out (k, r) => if k == i then out.push r else out) #[]
  let drawn (r : Ir.TableRule) : Bool := match r with
    | .gap _ => false
    | .top | .mid | .bottom | .cmid .. => true
  let target := cols.findSome? fun c => match c.width with
    | .flex t => some t
    | .natural | .sized _ => none
  let colEls := tableColEls cols target
  let rowEls := rows.mapIdx fun i row =>
    let cls := Id.run do
      let mut cls : Array String := #[]
      for r in ruleAt i do
        match r with
        | .top | .bottom => cls := cls.push "bt-heavy-above"
        | .mid => cls := cls.push "bt-light-above"
        | .cmid .. | .gap _ => pure ()
      if i + 1 == rows.size then
        for r in ruleAt rows.size do
          match r with
          | .top | .bottom => cls := cls.push "bt-heavy-below"
          | .mid => cls := cls.push "bt-light-below"
          | .cmid .. | .gap _ => pure ()
      else if (ruleAt (i + 1)).any drawn then
        cls := cls.push "bt-pre"
      return String.intercalate " " cls.toList
    let cmids := (ruleAt i).foldl (fun out r => match r with
      | .cmid a b _ _ => out.push (a, b)
      | .top | .mid | .bottom | .gap _ => out) (#[] : Array (Nat × Nat))
    Html.elem "tr" (tableRowCells cfg cols cmids spans headerRows i row)
      (if cls.isEmpty then #[] else #[("class", cls)])
  let cls := "booktabs" ++ (if padL then "" else " nopadl")
    ++ (if padR then "" else " nopadr")
  let kids := Id.run do
    let mut kids := #[Html.elem "colgroup" colEls]
    if 0 < headerRows then
      kids := kids.push (Html.elem "thead" (rowEls.extract 0 headerRows))
    if headerRows < rows.size then
      kids := kids.push (Html.elem "tbody" (rowEls.extract headerRows rowEls.size))
    return kids
  let attrs := match target with
    | some t => #[("class", cls), ("style", "width: " ++ t.css)]
    | none => #[("class", cls)]
  Html.elem "table" kids attrs

/-- A use of a role in the artifact references the role, not only its frozen
value: the emitted span's colour is `var(--n, …)`, resolved against the
`:root` declaration `paletteVar` writes — so the words follow the palette
(and a host page's override of the token), with the elaboration-time colour
only the fallback. Together with `role_use_is_palette_dependent` this is
the contrapositive of "frozen at authoring time"; a colour that arrived
with no palette name (`name = none`) has no variable to follow and really
is frozen. -/
theorem role_use_names_its_token (cfg : Config) (acc : Array Node)
    (c : Ir.Color) (n : String) (body : Array Inline) :
    inlineNodeInto cfg acc (.colored c (some n) body) =
      acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList)
        #[("style", s!"color: var(--{n}, {cssColor c})")]) := by
  simp [inlineNodeInto]

/-- The class hook's emission half: an authored role (not an internal
title-part role) reaches the artifact as an element carrying exactly
`roleClass name`, children the emission of its body. The name enters
attribute position only through the typed tree, so it passes `escapeAttr`
by construction (`escapeAttr_no_quote` closes attribute breakout), and
`roleClass_single_token` keeps the value one class token. -/
theorem role_class_reaches_artifact (cfg : Config) (acc : Array Node)
    (n : String) (body : Array Inline)
    (h : Ir.titlePartOf ((cfg.styles.find? "titlepage").getD {}).slots n = none) :
    inlineNodeInto cfg acc (.role n body) =
      acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList)
        #[("class", roleClass n)]) := by
  simp [inlineNodeInto, h]

/-- A link's URL enters the artifact only as the `href` attribute of the
typed tree — never spliced into markup — so it passes `escapeAttr` by
construction (`escapeAttr_no_quote`). This is what makes `.bib` field
text safe in citations and reference entries: a citation's resolved mark
is a `.link` to `Bib.anchorOf key`, and an entry's URL and DOI fields
become `.link` nodes, so a `"` or `<` a pasted `.bib` value carries can
never break out of the attribute or open a tag. -/
theorem link_url_enters_attribute_position (cfg : Config) (acc : Array Node)
    (url : String) (body : Array Inline) :
    inlineNodeInto cfg acc (.link url body) =
      acc.push (Html.elem "a" (inlineNodesInto cfg #[] body.toList)
        #[("href", url), ("style", "color: inherit")]) := by
  simp [inlineNodeInto]

/-- **The HTML projection of `Ir.Styles.linkLeafAfford_afford`.** A
text-bearing link-body leaf emits as the kind's ink span wrapping a `<u>`
element wrapping the leaf's own emission — the ink CSS and the underline tag
together, the two affordances the inline `.colored`/`.decorated` arms carry
(a named colour becomes a `var(--token, …)` reference, so a host page can
restyle the ink). The HTML half of the one IR value both backends read
(`Ir.Styles.linkBodyAfford`; Layout's `linkLeafAfford_projects` is the
PDF half). -/
theorem linkLeafAfford_projects (cfg : Config) (acc : Array Node)
    (s : Ir.Styles) (kind : String) (x : Inline) (h : x.bearsLinkText = true) :
    inlineNodeInto cfg acc (s.linkLeafAfford kind x)
      = (match (s.find? kind).bind (·.color) with
         | some (c, n) =>
             acc.push (Html.elem "span"
               #[Html.elem "u" (inlineNodesInto cfg #[] [x])]
               #[("style", match n with
                  | some nm => s!"color: var(--{nm}, {cssColor c})"
                  | none => s!"color: {cssColor c}")])
         | none => acc.push (Html.elem "u" (inlineNodesInto cfg #[] [x]))) := by
  rw [Ir.Styles.linkLeafAfford_afford s kind x h]
  cases hc : (s.find? kind).bind (·.color) with
  | none => simp [inlineNodeInto, inlineNodesInto]
  | some p => obtain ⟨c, n⟩ := p; cases n <;> simp [inlineNodeInto, inlineNodesInto]

/-- Does this paragraph use `\hfill`? If so it becomes a flex row, which is
the CSS equivalent of the stretch it asked for. -/
private def hasFill (xs : Array Inline) : Bool :=
  xs.any fun x => match x with
    | .fill => true
    | .hspace e _ => e.hasFil
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
    | .hspace e keep =>
      if e.hasFil then
        let finite := e.withoutFil
        let zero := MeasureValues.horizontal 0 0
        unless !finite.anyRef (fun _ => true) && finite.eval zero.find == {} do
          cur := cur.push (.hspace finite keep)
        out := out.push cur
        cur := #[]
      else cur := cur.push x
    | other => cur := cur.push other
  return out.push cur

/-- The heading tag a section level takes: `h` and the shared rank
(`Ir.headingRank`, which carries the sourcing), so the tag and the
markdown marker cannot drift; `heading_renderings_agree` in Tests states
the agreement over every level. -/
def headingTag (level : Nat) : String :=
  s!"h{Ir.headingRank level}"

private def fillRow (cfg : Config) (tag baseClass : String) (xs : Array Inline) : Node :=
  let groups := splitAtFills xs
  let rowClass := if groups.size == 2 then baseClass ++ " entry-pair" else baseClass
  -- A row holding an image sized by a text-width fraction is the container
  -- that fraction is stated against (`Config.inFillRow`).
  let sized := Ir.foldInlines (fun acc x => acc || match x with
    | .image _ size _ => size.width.any fun l =>
        l.value.anyRef (· != .textHeight) && !l.value.anyRef (· == .textHeight)
    | _ => false) false xs
  let cfg := { cfg with inFillRow := true }
  Html.elem tag (groups.map fun group =>
    Html.elem "span" (inlines cfg group) #[("class", "group")])
    (#[("class", rowClass)] ++
      (if sized then #[("style", "container-type: inline-size")] else #[]))

/-- Grid tracks from the declared widths, through the IR's own reading
(`Ir.BoxWidth.trackOf`, spelled by `Ir.Track.css`): a fraction is a
percentage track, an absolute length a length track, and a widthless box an
`fr` share of the leftover. With every width declared the leftover spreads
between the tracks, which is the PDF path's gutter rule.
`Ir.boxWidth_tracks_agree` is why this and the page's arithmetic cannot
disagree about which boxes declared a width. -/
private def gridTracks (cols : Array (BoxWidth × Array Block)) : String :=
  String.intercalate " " (cols.toList.map fun (w, _) => Ir.Track.css w.trackOf)

/-- Children start their own sibling walk: the parent's accumulated epoch
style already stands on an ancestor element and inherits into it, so it is
never re-applied below. The epoch palette and tokens carry in for the
diffs a nested declaration makes. -/
def Config.into (cfg : Config) : Config :=
  { cfg with epochStyle := "", epochGround := false }

/-- Project the IR frame's numbered extent, including title and body
endpoints, into every part of its HTML frame. -/
def Config.inFrame (cfg : Config) (frame : Block) : Config :=
  { cfg with overlaySteps := Ir.frameSteps frame }

/-- Frame context projects the IR selector without dropping any numbered
step the frame reaches. The same membership holds for title, body and furniture. -/
theorem Config.inFrame_membership_agree (cfg : Config) (frame : Block)
    (spec : Ir.OverlaySpec) (k : Nat) (hk : 1 ≤ k) (hsteps : k ≤ Ir.frameSteps frame) :
    (spec.selectedSteps (cfg.inFrame frame).overlaySteps).contains k = spec.selects k :=
  overlay_membership_agree spec (Ir.frameSteps frame) k hk hsteps

private def joinStyles (a b : String) : String :=
  if a.isEmpty then b else if b.isEmpty then a else a ++ "; " ++ b

/-- A body palette epoch as semantic changes, before CSS serialization. `none`
removes a property. -/
structure PaletteDiff where
  entries : Array (String × Option Ir.Color)

/-- Whether this epoch changes the page ground. -/
def PaletteDiff.groundChanged (diff : PaletteDiff) : Bool :=
  diff.entries.any (·.1 == "bg")

/-- Serialize the semantic palette changes as custom-property declarations. -/
def PaletteDiff.style (diff : PaletteDiff) : String :=
  String.intercalate "; " (diff.entries.toList.map fun
    | (n, some c) => s!"--{n}: {cssColor c}"
    | (n, none) => s!"--{n}: initial")

/-- The custom-property redefinitions a body `\palette` makes, against the
palette in force before it. Equality is explicitly over the HTML projection:
a PDF device rider can change without selecting a different screen value. -/
def epochPaletteDiff (before after : Ir.Palette) : PaletteDiff :=
  let changed := (after.entries.filter fun (n, c) =>
    (before.find? n).map cssColor != some (cssColor c)).map fun (n, c) => (n, some c)
  let removed := (before.entries.filter fun (n, _) =>
    (after.find? n).isNone).map fun (n, _) => (n, none)
  { entries := changed ++ removed }

/-- The redefinitions a body `\tokens` makes, same diff. -/
def epochTokenStyle (before after : Ir.Tokens) : String :=
  String.intercalate "; " ((after.entries.filter fun (n, g) =>
    before.find? n != some g).toList.map fun (n, g) => s!"--{n}: {cssLength g.width}")

/-- Advance the palette epoch while retaining its semantic ground fact.
A body declaration replaces the frame-entry listing pair: like layout's
palette transition, it resets the ground and default ink together. Clearing
the cached foreground lets the listing read the new palette's default ink. -/
def Config.advancePalette (cfg : Config) (p : Ir.Palette) : Config :=
  let diff := epochPaletteDiff cfg.pal p
  { cfg with pal := p
             listingGround := p.find? "bg", listingFg := none
             epochStyle := joinStyles cfg.epochStyle diff.style
             epochGround := cfg.epochGround || diff.groundChanged }

/-- A frame's outgoing palette continues into later frames, as in layout.
The context fold excludes speaker notes: their declarations are side-channel
content, while nested body declarations remain in flow order. -/
private def Config.afterFrame (cfg : Config) : Block → Config
  | .frame _ _ _ _ body =>
    Ir.foldCtxBlocks {
      openBlock := fun visible cfg b => match b with
        | .note _ => (cfg, false)
        | .setPalette p => (if visible then cfg.advancePalette p else cfg, visible)
        | _ => (cfg, visible)
      closeBlock := fun _ cfg _ => cfg
      openInline := fun visible cfg _ => (cfg, visible)
      closeInline := fun _ cfg _ => cfg
    } true cfg body
  | .para .. | .section .. | .list .. | .center .. | .ragged ..
  | .spaced .. | .role .. | .link .. | .quote .. | .abstract .. | .titled ..
  | .equation .. | .verbatim .. | .algorithm .. | .columns .. | .onSteps ..
  | .altSteps .. | .note .. | .only .. | .nav .. | .logo .. | .pagebreak
  | .framefoot .. | .setPalette .. | .setTokens .. | .rule .. | .picture ..
  | .table .. | .float .. | .bibliography .. => cfg

/-- A flow epoch that changes the page ground paints each following
continuous-flow box in that ground. This avoids a wrapper (which would break
sibling rhythm and host selectors); deck stages already paint their own full
page from the same `--bg`. -/
private def epochSurfaceStyle (style : String) (groundChanged : Bool) : String :=
  if groundChanged then
    joinStyles style "background: var(--bg, var(--surface, #fafaf9))"
  else style

/-- The epoch's redefinitions onto one emitted sibling node. The epoch
comes first, so an element's own style declarations win (CSS style
attribute: last declaration of a property applies). A text node carries no
attributes and needs none. -/
def withEpoch (style : String) (groundChanged : Bool) : Node → Node
  | .elem t attrs kids =>
    let style := epochSurfaceStyle style groundChanged
    if style.isEmpty then .elem t attrs kids
    else if attrs.any (·.1 == "style") then
      .elem t (attrs.map fun kv =>
        if kv.1 == "style" then (kv.1, style ++ "; " ++ kv.2) else kv) kids
    else .elem t (attrs.push ("style", style)) kids
  | .text s => .text s
  | .style css => .style css
  | .script attrs code => .script attrs code

/-- The node with one more class token, appended to an element's `class` or
added as it: how an engine role that only spaces or styles reaches the
element it governs without becoming an element of its own. -/
def withClass (c : String) : Node → Node
  | .elem t attrs kids =>
    if attrs.any (·.1 == "class") then
      .elem t (attrs.map fun kv => if kv.1 == "class" then (kv.1, kv.2 ++ " " ++ c) else kv) kids
    else .elem t (attrs.push ("class", c)) kids
  | .text s => .text s
  | .style css => .style css
  | .script attrs code => .script attrs code

/-- One reference-list entry: the style's marker, the formatted content,
and the anchor its citations link to. A numbered entry's content is one
element beside its label, so the list's grid can hang the labels in one
column (`bibCss`); an author-year entry is its content alone. -/
private def bibItemNode (cfg : Config) (item : Ir.BibItem) : Node :=
  let kids : Array Node := match item.marker with
    | some m => #[Html.elem "span" #[Html.text s!"[{m}]"] #[("class", "bib-marker")],
        Html.text " ", Html.elem "span" (inlines cfg item.content) #[("class", "bib-entry")]]
    | none => inlines cfg item.content
  Html.elem "li" kids #[("id", Ir.bibAnchor item.key)]

/-- An entry's key enters the artifact only as the `id` attribute of the
typed tree — the anchor `Bib.anchorOf` links to — so it passes
`escapeAttr` by construction (`escapeAttr_no_quote`): a `.bib` key is
author text, and no spelling of one can break out of the attribute. -/
private theorem bibItemNode_key_enters_attribute_position (cfg : Config)
    (item : Ir.BibItem) :
    ∃ kids, bibItemNode cfg item =
      Html.elem "li" kids #[("id", Ir.bibAnchor item.key)] :=
  ⟨_, rfl⟩

/-- Where one algorithm line stands in the nesting its declared depths
imply: a node carrying the line, or a group standing in for a level no
line declared (a depth that skips one). The forest is what `algNest`
builds from `Ir.Block.algorithm`'s line array and what
`algorithm_lines_agree` ranges over; the screen backend renders it as
nested `<ol>`s. -/
inductive AlgTree where
  | node (line : Option Ir.AlgLine) (kids : Array AlgTree)

mutual

/-- The lines one nesting node carries, in document order: its own line
first, then its kids' — the order the rendered `<li>`s stand in, since a
nested list follows the text of the item it hangs under. Read by
`algorithm_lines_agree` only; no emission path walks it. -/
def algLinesOne (acc : Array Ir.AlgLine) : AlgTree → Array Ir.AlgLine
  | .node none kids => algLinesList acc kids.toList
  | .node (some l) kids => algLinesList (acc.push l) kids.toList

/-- `algLinesOne` over one level's forest, threading the accumulator. -/
def algLinesList (acc : Array Ir.AlgLine) : List AlgTree → Array Ir.AlgLine
  | [] => acc
  | t :: rest => algLinesList (algLinesOne acc t) rest

end

/-- One finished level attached to the level below it: the level's forest
becomes the kids of the node it stood under, or of a group where no node
declared that level. A node takes kids at most once — the close that
attaches them is either followed by a new last node on that level (the
line whose shallower depth triggered it) or by the level's own close. -/
def algAttach (inner top : Array AlgTree) : Array AlgTree :=
  match top.back? with
  | some (.node l kids) => top.pop.push (.node l (kids ++ inner))
  | none => top.push (.node none inner)

/-- The nesting stack, innermost level first: close the open level into
the one beneath it. -/
def algClose : List (Array AlgTree) → List (Array AlgTree)
  | inner :: top :: rest => algAttach inner top :: rest
  | [lvl] => [lvl]
  | [] => []

/-- `algClose` iterated — the unwind, counted rather than conditioned, so
it is total by structure. -/
def algCloseN : Nat → List (Array AlgTree) → List (Array AlgTree)
  | 0, s => s
  | n + 1, s => algCloseN n (algClose s)

/-- Levels opened under the current one, counted the same way. -/
def algOpenN : Nat → List (Array AlgTree) → List (Array AlgTree)
  | 0, s => s
  | n + 1, s => algOpenN n (#[] :: s)

/-- One line onto the stack, at the depth it declares: close back to that
depth, open down to it, then stand the line on the level it names. -/
def algStep (s : List (Array AlgTree)) (l : Ir.AlgLine) : List (Array AlgTree) :=
  let closed := algCloseN (s.length - (l.depth + 1)) s
  let opened := algOpenN (l.depth + 1 - closed.length) closed
  (opened.headD #[]).push (.node (some l) #[]) :: opened.tail

/-- The nesting an algorithm's lines declare, as a forest: each line's own
depth drives it — the parse's truth — so an else standing at its if's
level nests exactly once. The final unwind leaves one level, the document
order `algorithm_lines_agree` reads back. -/
def algNest (lines : Array Ir.AlgLine) : Array AlgTree :=
  let s := lines.foldl algStep [#[]]
  (algCloseN (s.length - 1) s).headD #[]

/-- Every line the stack holds, bottom level first: a level's lines stand
before the lines of the levels nested under its last node, which is the
document order the finished forest reads in. -/
def algStackLines (s : List (Array AlgTree)) : Array Ir.AlgLine :=
  s.foldl (fun acc lvl => algLinesList #[] lvl.toList ++ acc) #[]

mutual

private theorem algLinesOne_acc (acc : Array Ir.AlgLine) (t : AlgTree) :
    algLinesOne acc t = acc ++ algLinesOne #[] t := by
  match t with
  | .node none kids =>
    rw [algLinesOne, algLinesOne, algLinesList_acc acc kids.toList]
  | .node (some l) kids =>
    rw [algLinesOne, algLinesOne, algLinesList_acc (acc.push l) kids.toList,
      algLinesList_acc ((#[] : Array Ir.AlgLine).push l) kids.toList,
      Array.push_eq_append, Array.push_eq_append, Array.empty_append,
      Array.append_assoc]

private theorem algLinesList_acc (acc : Array Ir.AlgLine) (xs : List AlgTree) :
    algLinesList acc xs = acc ++ algLinesList #[] xs := by
  match xs with
  | [] => rw [algLinesList, algLinesList, Array.append_empty]
  | t :: rest =>
    rw [algLinesList, algLinesList, algLinesList_acc (algLinesOne acc t) rest,
      algLinesList_acc (algLinesOne #[] t) rest, algLinesOne_acc acc t,
      Array.append_assoc]

end

private theorem algLinesList_append (xs ys : List AlgTree) :
    algLinesList #[] (xs ++ ys)
      = algLinesList #[] xs ++ algLinesList #[] ys := by
  induction xs with
  | nil => rw [List.nil_append, algLinesList, Array.empty_append]
  | cons t rest ih =>
    rw [List.cons_append, algLinesList, algLinesList,
      algLinesList_acc (algLinesOne #[] t) (rest ++ ys), ih,
      algLinesList_acc (algLinesOne #[] t) rest, Array.append_assoc]

private theorem algLinesList_acc_append (acc : Array Ir.AlgLine)
    (xs ys : List AlgTree) :
    algLinesList acc (xs ++ ys)
      = acc ++ algLinesList #[] xs ++ algLinesList #[] ys := by
  rw [algLinesList_acc, algLinesList_append, Array.append_assoc]

private theorem algLinesList_push (xs : Array AlgTree) (t : AlgTree) :
    algLinesList #[] (xs.push t).toList
      = algLinesList #[] xs.toList ++ algLinesOne #[] t := by
  rw [Array.toList_push, algLinesList_append, algLinesList, algLinesList]

private theorem algAttach_lines (inner top : Array AlgTree) :
    algLinesList #[] (algAttach inner top).toList
      = algLinesList #[] top.toList ++ algLinesList #[] inner.toList := by
  rw [algAttach]
  split
  · next l kids h =>
    obtain ⟨ys, hy⟩ := Array.back?_eq_some_iff.1 h
    subst hy
    rw [Array.pop_push, algLinesList_push, algLinesList_push]
    cases l with
    | none =>
      rw [algLinesOne, algLinesOne, Array.toList_append,
        algLinesList_acc_append, Array.empty_append, Array.append_assoc]
    | some l =>
      rw [algLinesOne, algLinesOne, Array.toList_append,
        algLinesList_acc_append,
        algLinesList_acc ((#[] : Array Ir.AlgLine).push l) kids.toList]
      simp [Array.append_assoc]
  · next h =>
    rw [Array.back?_eq_none_iff.1 h, algLinesList_push, algLinesOne,
      algLinesList, algLinesList_acc #[] inner.toList, Array.empty_append,
      Array.empty_append]

private theorem algLevelsFoldl (s : List (Array AlgTree))
    (acc : Array Ir.AlgLine) :
    s.foldl (fun acc lvl => algLinesList #[] lvl.toList ++ acc) acc
      = s.foldl (fun acc lvl => algLinesList #[] lvl.toList ++ acc) #[] ++ acc := by
  induction s generalizing acc with
  | nil => rw [List.foldl_nil, List.foldl_nil, Array.empty_append]
  | cons b bs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih,
      ih (algLinesList #[] b.toList ++ #[]), Array.append_empty,
      Array.append_assoc]

private theorem algStackLines_cons (a : Array AlgTree)
    (rest : List (Array AlgTree)) :
    algStackLines (a :: rest)
      = algStackLines rest ++ algLinesList #[] a.toList := by
  unfold algStackLines
  rw [List.foldl_cons, algLevelsFoldl, Array.append_empty]

private theorem algStackLines_nil :
    algStackLines [] = (#[] : Array Ir.AlgLine) := rfl

private theorem algClose_lines (s : List (Array AlgTree)) :
    algStackLines (algClose s) = algStackLines s := by
  match s with
  | [] => rfl
  | [_] => rfl
  | inner :: top :: rest =>
    rw [algClose, algStackLines_cons, algStackLines_cons, algStackLines_cons,
      algAttach_lines, Array.append_assoc]

private theorem algCloseN_lines (n : Nat) (s : List (Array AlgTree)) :
    algStackLines (algCloseN n s) = algStackLines s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [algCloseN, ih, algClose_lines]

private theorem algOpenN_lines (n : Nat) (s : List (Array AlgTree)) :
    algStackLines (algOpenN n s) = algStackLines s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [algOpenN, ih, algStackLines_cons, Array.toList_empty, algLinesList,
      Array.append_empty]

private theorem algStackLines_headD (t : List (Array AlgTree)) :
    algStackLines t.tail ++ algLinesList #[] (t.headD #[]).toList
      = algStackLines t := by
  match t with
  | [] =>
    rw [List.tail_nil, algStackLines_nil, List.headD_nil, Array.toList_empty,
      algLinesList, Array.append_empty]
  | _ :: _ => rw [algStackLines_cons]; rfl

private theorem algStep_lines (s : List (Array AlgTree)) (l : Ir.AlgLine) :
    algStackLines (algStep s l) = algStackLines s ++ #[l] := by
  rw [algStep, algStackLines_cons, algLinesList_push, algLinesOne,
    Array.toList_empty, algLinesList, Array.push_eq_append, Array.empty_append,
    ← Array.append_assoc, algStackLines_headD, algOpenN_lines, algCloseN_lines]

private theorem algStep_ne_nil (s : List (Array AlgTree)) (l : Ir.AlgLine) :
    algStep s l ≠ [] := by rw [algStep]; exact List.cons_ne_nil _ _

private theorem algFold_lines (xs : List Ir.AlgLine)
    (init : List (Array AlgTree)) :
    algStackLines (xs.foldl algStep init)
      = algStackLines init ++ xs.toArray := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    rw [List.foldl_cons, ih, algStep_lines, Array.append_assoc]
    congr 1
    apply Array.toList_inj.1
    simp

private theorem algFold_ne_nil (xs : List Ir.AlgLine)
    (init : List (Array AlgTree)) (h : init ≠ []) :
    xs.foldl algStep init ≠ [] := by
  induction xs generalizing init with
  | nil => rwa [List.foldl_nil]
  | cons x rest ih =>
    rw [List.foldl_cons]
    exact ih (algStep init x) (algStep_ne_nil init x)

private theorem algCloseN_length (n : Nat) (s : List (Array AlgTree))
    (h : s.length = n + 1) : (algCloseN n s).length = 1 := by
  induction n generalizing s with
  | zero => rw [algCloseN]; omega
  | succ n ih =>
    rw [algCloseN]
    refine ih (algClose s) ?_
    match s with
    | [] => simp at h
    | [_] => simp at h
    | _ :: _ :: rest =>
      rw [algClose, List.length_cons]
      simp only [List.length_cons] at h
      omega

/-- The two artifacts read one algorithm's lines in one order. The fact is
of the IR, not of either artifact: the nesting a line's declared depth
implies (`algNest`) loses no line and reorders none, so reading the forest
back in document order returns the declared array itself. Print's
projection is that array read straight through — `Layout`'s `.algorithm`
arm folds it in order, one display paragraph per element — and screen's is
this forest, one `<li>` per node. Equality here is therefore the
agreement: a line cannot reach one artifact and miss the other, nor reach
the two in different places. The defect it refuses is the one an `\eIf`
produced before the depths drove the build, where the else nested a second
time and so stood a level deeper on screen than in print. -/
theorem algorithm_lines_agree (lines : Array Ir.AlgLine) :
    algLinesList #[] (algNest lines).toList = lines := by
  rw [algNest]
  have hne : lines.foldl algStep [#[]] ≠ [] := by
    rw [← Array.foldl_toList]
    exact algFold_ne_nil lines.toList [#[]] (List.cons_ne_nil _ _)
  have hlen : (lines.foldl algStep [#[]]).length
      = ((lines.foldl algStep [#[]]).length - 1) + 1 := by
    have := List.length_pos_iff.2 hne; omega
  have h1 := algCloseN_length _ _ hlen
  have hfold : algStackLines (lines.foldl algStep [#[]]) = lines := by
    rw [← Array.foldl_toList, algFold_lines, algStackLines_cons,
      algStackLines_nil, Array.toList_empty, algLinesList, Array.empty_append,
      Array.empty_append]
  have hpres := algCloseN_lines ((lines.foldl algStep [#[]]).length - 1)
    (lines.foldl algStep [#[]])
  rw [hfold] at hpres
  match hm : algCloseN ((lines.foldl algStep [#[]]).length - 1)
      (lines.foldl algStep [#[]]) with
  | [] => rw [hm] at h1; simp at h1
  | _ :: _ :: _ => rw [hm] at h1; simp at h1
  | [a] =>
    rw [hm] at hpres
    rw [List.headD_cons, ← hpres, algStackLines_cons, algStackLines_nil,
      Array.empty_append]

mutual

/-- One nesting node as a list item: the line's own inlines, then the
nested list its kids form. The payload is a parameter so the nesting and
the rendering stay separable — `algorithm_lines_agree` ranges over the
nesting alone. -/
def algRenderOne (payload : Ir.AlgLine → Array Node) : AlgTree → Node
  | .node l kids =>
    let pay := match l with
      | some l => payload l
      | none => #[]
    Html.elem "li" (if kids.isEmpty then pay
      else pay.push (Html.elem "ol" (algRenderList payload #[] kids.toList) #[])) #[]

/-- `algRenderOne` over one level's forest, threading the accumulator. -/
def algRenderList (payload : Ir.AlgLine → Array Node) (acc : Array Node) :
    List AlgTree → Array Node
  | [] => acc
  | t :: rest => algRenderList payload (acc.push (algRenderOne payload t)) rest

end

/-- One piece of a picture label as its SVG `<text>` sets it: math as its
floor — the formula's content, never its markup, the recovery policy this
backend applies in prose (native MathML inside SVG is what M6 still owes
there) — and every other inline its plain text. -/
def labelPiece : Inline → String
  | .math _ src => Ir.mathFloor src
  | .formula _ _ body => Ir.formulaFloor body
  | inl => Ir.plainTextOne inl

/-- The face a picture label's run is set in, on the axes the PDF resolves
for it (`Layout.applyStyle`): the weight, the slant, the family slot, small
caps, and the size and language switches. A label starts at `{}`, where
the PDF starts it (`Layout.labelInk` sets a label from the default text
style under the label's colour). -/
structure LabelFace where
  weight : Ir.Weight := .m
  italic : Bool := false
  slot : Nat := 0
  smallcaps : Bool := false
  size : Option String := none
  lang : Option String := none
  deriving BEq, Inhabited

/-- One style's step on a label's face, as the PDF takes it: the weight
through `Style.weight?`, the one map `Layout.weight_agree` holds the PDF
to; `\emph` toggles the slant, so emphasis inside italic sets upright; NFSS
shapes are exclusive, so upright clears italic and small caps both; and
`\textnormal` resets every axis. A backend may not read another backend,
so the slant and the family are the PDF's step restated here, and the
per-glyph agreement check (`pictureNodeStyleChecks`) is what holds the
two to each other. -/
def LabelFace.step (f : LabelFace) (s : Style) : LabelFace :=
  let f := { f with weight := (s.weight?).getD f.weight }
  match s with
  | .italic => { f with italic := true }
  | .emph => { f with italic := !f.italic }
  | .upright => { f with italic := false, smallcaps := false }
  | .smallcaps => { f with smallcaps := true }
  | .mono => { f with slot := 2 }
  | .sans => { f with slot := 1 }
  | .roman => { f with slot := 0 }
  | .normal => {}
  | .lang tag => { f with lang := some tag }
  | .size n => { f with size := some n }
  | .fontSize _ _ => f
  | .bold | .medium | .series _ => f

/-- A face as the attributes of the `<tspan>` its run sets in, relative to
the label's own `<text>`, which inherits the body's regular weight and
upright shape: the bold series is `font-weight: bolder`, the rendering the
prose `<strong>` gets (HTML §15.3.4), which over a regular of 400 asks for
the 700 the PDF's bold series names (`Weight.css`); any other series is
its numeric weight, italic is `font-style`, the mono slot its family, and
the sans slot, small caps and a size are the classes the prose `<span>`
carries (`styleClass`), a language its `lang`. The regular face is no
attribute at all, so a run the PDF sets regular inherits the regular. -/
def LabelFace.attrs (f : LabelFace) : Array (String × String) :=
  let weight : Array (String × String) :=
    if f.weight == .m then #[]
    else if f.weight == .b then #[("font-weight", "bolder")]
    else #[("font-weight", toString f.weight.css)]
  let slant : Array (String × String) := if f.italic then #[("font-style", "italic")] else #[]
  let classes := (if f.slot == 1 then [styleClass .sans] else []) ++
    (if f.smallcaps then [styleClass .smallcaps] else []) ++
    (match f.size with
     | some n => [styleClass (.size n)]
     | none => [])
  let cls : Array (String × String) :=
    if classes.isEmpty then #[] else #[("class", " ".intercalate classes)]
  let family : Array (String × String) :=
    if f.slot == 2 then #[("style", "font-family: var(--font-mono)")] else #[]
  let lang : Array (String × String) := match f.lang with
    | some tag => #[("lang", tag)]
    | none => #[]
  weight ++ slant ++ cls ++ family ++ lang

/-- One run of text in a face: character data where the face is the
label's own, else a `<tspan>` carrying it. -/
def LabelFace.run (f : LabelFace) (s : String) : Node :=
  let a := f.attrs
  if a.isEmpty then Html.text s else Html.elem "tspan" #[Html.text s] a

mutual

/-- One inline of a picture label as SVG `<text>` children, onto `acc`: the
same runs the PDF sets, each text run in the face the PDF resolves for it
(`LabelFace`). A style is no element of its own: it steps the face, and
every run it covers carries the face in full on its own `<tspan>`
(`LabelFace.run`), so no weight or slant is ever relative to an enclosing
run's — which is what lets a reset (`\textnormal`) and a toggle (`\emph`
inside italic) set what the PDF sets, where nested `bolder` and `italic`
tspans could only add. A colour is a `<tspan>` of SVG's `fill`, through the
palette role's custom property as prose's `color` is, and a role its
class; neither touches the face. Math is an italic `<tspan>` of its floor
under no weight at all: the PDF sets a formula in the math face, which no
text weight reaches, so the floor keeps the label's regular weight
whatever style surrounds it. Every other inline is its plain text in the
face in force — the node salvage produces none of them. Every string goes
through the escaper by construction. -/
def labelNodesOne (f : LabelFace) (acc : Array Node) (x : Inline) : Array Node :=
  match x with
  | .text s => acc.push (f.run s)
  | .math _ _ | .formula _ _ _ =>
    acc.push (Html.elem "tspan" #[Html.text (labelPiece x)] #[("font-style", "italic")])
  | .styled st body => labelNodesList (f.step st) acc body.toList
  | .colored c name body =>
    let paint := match name with
      | some n => ("style", s!"fill: var(--{n}, {cssColor c})")
      | none => ("fill", cssColor c)
    acc.push (Html.elem "tspan" (labelNodesList f #[] body.toList) #[paint])
  | .role n body =>
    acc.push (Html.elem "tspan" (labelNodesList f #[] body.toList) #[("class", roleClass n)])
  | .located _ body => labelNodesList f acc body.toList
  | .italicCorr _ => acc
  | .link _ _ | .decorated _ _ | .onSteps _ _ | .altSteps _ _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _
  | .pageNumber | .pageCount | .linebreak _ | .image _ _ _ | .icon _ _ | .label _
  | .ref _ _ _ _ | .cite _ _ | .footnote _ _ => acc.push (f.run (labelPiece x))

/-- `labelNodesOne` over a label's inlines, threading the accumulator. -/
def labelNodesList (f : LabelFace) (acc : Array Node) : List Inline → Array Node
  | [] => acc
  | x :: rest => labelNodesList f (labelNodesOne f acc x) rest

end

/-- The shapes of a picture as SVG children, in the box `((px0, py0), (px1,
py1))` the viewBox declares: the same evaluated shapes the PDF paints,
through the typed tree so every label passes the escaper. SVG's y grows
downward, so the transform is the PDF path's: flip against the box's top.
Labels use the same metric as that box. Without a font environment the
zero metric leaves the source anchor as the alphabetic baseline. -/
def pictureKids (pic : Ir.Pic.Picture) (px0 py1 : Dim.Sp)
    (metric : Ir.Pic.LabelMetric := fun _ _ => {}) : Array Node :=
  pic.shapes.map fun shape =>
    -- The paint attributes of a stroked/filled shape: fill (or none —
    -- SVG's default is black, not TikZ's), then stroke colour, width,
    -- and pgf's dash rhythms (§15.3.2: dashed on 3pt off 3pt, dotted
    -- on the line width off 1pt).
    let paint := fun (st : Option Ir.Pic.Stroke) (fl : Option Ir.Color) =>
      let fillA := #[("fill", (fl.map cssColor).getD "none")]
      match st with
      | none => fillA
      | some k =>
        let dashA : Array (String × String) := match k.dash with
          | .solid => #[]
          | .dashed => #[("stroke-dasharray", "3 3")]
          | .dotted => #[("stroke-dasharray", s!"{k.width.toPtString} 1")]
        fillA ++ #[("stroke", cssColor k.color),
          ("stroke-width", k.width.toPtString)] ++ dashA
    match shape with
    | .rect rx ry rw rh color =>
      Html.elem "rect" #[] #[
        ("x", (min rx (rx + rw) - px0).toPtString),
        ("y", (py1 - max ry (ry + rh)).toPtString),
        ("width", (max rw (-rw)).toPtString),
        ("height", (max rh (-rh)).toPtString),
        ("fill", cssColor color)]
    | .label lx ly content color scale align =>
      -- The label's inline content inside SVG's <text>: the runs the PDF
      -- sets, each in its face and colour (`labelNodesList`), math an
      -- italic <tspan> of its floor, every string through the escaper by
      -- construction.
      let nodes := labelNodesList {} #[] content.toList
      let anchor := match align with
        | .center | .south | .north => "middle"
        | .west => "start"
        | .east => "end"
      let baseline := Ir.Pic.labelBaseline ly align (metric content scale)
      Html.elem "text" nodes #[
        ("x", (lx - px0).toPtString),
        ("y", (py1 - baseline).toPtString),
        ("fill", cssColor color),
        ("font-size", (Ir.baseFontSize * (scale : Int) / 1000).toPtString),
        ("text-anchor", anchor),
        ("dominant-baseline", "alphabetic")]
    | .circle sx sy r st fl =>
      Html.elem "circle" #[] (#[
        ("cx", (sx - px0).toPtString),
        ("cy", (py1 - sy).toPtString),
        ("r", (max r (-r)).toPtString)] ++ paint st fl)
    | .frame fx fy fw fh st fl =>
      Html.elem "rect" #[] (#[
        ("x", (min fx (fx + fw) - px0).toPtString),
        ("y", (py1 - max fy (fy + fh)).toPtString),
        ("width", (max fw (-fw)).toPtString),
        ("height", (max fh (-fh)).toPtString)] ++ paint st fl)
    | .edge segs st tip =>
      let px (v : Dim.Sp) : String := (v - px0).toPtString
      let py (v : Dim.Sp) : String := (py1 - v).toPtString
      let d := String.join (segs.toList.map fun sg => match sg with
        | .line x1 y1 x2 y2 =>
          s!"M {px x1} {py y1} L {px x2} {py y2} "
        | .cubic x1 y1 c1x c1y c2x c2y x2 y2 =>
          s!"M {px x1} {py y1} C {px c1x} {py c1y}, {px c2x} {py c2y}, \
{px x2} {py y2} ")
      let tipNodes : Array Node := match tip with
        | some t => #[Html.elem "path" #[] #[
            ("d", s!"M {px t.x1} {py t.y1} L {px t.x2} {py t.y2} \
L {px t.x3} {py t.y3} Z"),
            ("fill", cssColor st.color)]]
        | none => #[]
      Html.elem "g" (#[Html.elem "path" #[] ((#[("d", d)] : Array (String × String))
        ++ paint (some st) none)] ++ tipNodes) #[]

/-- **Every emitted label baseline projects the IR's measured band**
(`_projects`): SVG declares the alphabetic baseline at `labelBaseline`,
whose `Ir.Pic.labelBaseline_box_exact` also identifies the native page's
box-top-plus-height placement after its y flip. This holds at every label
index, independent of alignment, font, scale and the surrounding shapes. -/
theorem pictureLabelBaseline_projects (pic : Ir.Pic.Picture) (px0 py1 : Dim.Sp)
    (metric : Ir.Pic.LabelMetric) (i : Nat) (x y : Dim.Sp)
    (content : Array Inline) (color : Ir.Color) (scale : Nat) (align : Ir.Pic.LabelAlign)
    (h : pic.shapes[i]? = some (.label x y content color scale align)) :
    (match (pictureKids pic px0 py1 metric)[i]? with
      | some (.elem _ attrs _) =>
        (attrOf? attrs "y", attrOf? attrs "dominant-baseline")
      | _ => (none, none)) =
      (some (py1 - Ir.Pic.labelBaseline y align (metric content scale)).toPtString,
        some "alphabetic") := by
  simp [pictureKids, h, Html.elem, attrOf?]

/-- The picture's box as the element's own size. Lengths are pt, the unit
the viewBox declares — and in flow classes the element's own size too:
paper is paper. On the paged deck the stage is the viewport, so the box
ships as its share of the stage instead (`deckStageMilli`, as images do): a
pt box against CSS's 96 dpi ruler was the same "very small picture" defect.
Both shares are stated and the viewBox's own ratio letterboxes inside them
(SVG 2 §8.7, `meet`), so a viewport of another ratio never distorts the
ink. -/
def pictureBox (cfg : Config) (w h : Dim.Sp) (rise : Dim.Sp := 0) : Array (String × String) :=
  #[("viewBox", s!"0 0 {w.toPtString} {h.toPtString}")] ++
    (if cfg.deck then
      #[("style", s!"width: {decMilli (deckStageMilli w cfg.page.width)}vw; \
height: {decMilli (deckStageMilli h cfg.page.height)}dvh" ++
        (if rise == 0 then "" else
          s!"; vertical-align: -{decMilli (deckStageMilli rise cfg.page.height)}dvh"))]
     else
      #[("width", s!"{w.toPtString}pt"), ("height", s!"{h.toPtString}pt")] ++
        (if rise == 0 then #[] else #[("style", s!"vertical-align: -{rise.toPtString}pt")]))

/-- The words a picture's labels set, as the SVG sets them: the IR's one
reading (`Ir.Pic.Picture.said`), which the image of a picture drawn at the
boundary carries as its text alternative too. -/
def pictureSaid (pic : Ir.Pic.Picture) : String := pic.said

/-- What a picture says in words to a reader of the page: the alternative it
resolves to (`Ir.Pic.Picture.alternative` — the author's words, else its
labels'), and with none, what it is (`figureWord`), so the name is never
blank (`pictureName_contract`). -/
def pictureName (loc : Locale) (pic : Ir.Pic.Picture) : String :=
  firstNonBlank pic.alternative.text (figureWord loc)

theorem pictureName_contract (loc : Locale) (pic : Ir.Pic.Picture) :
    nonBlank (pictureName loc pic) = true :=
  firstNonBlank_contract _ _ (figureWord_contract loc)

/-- A string's words, one space apart: what a name built from prose reads
once its line breaks and indentation are gone. -/
def squashSpace (s : String) : String :=
  String.intercalate " "
    (((s.map fun c => if c.isWhitespace then ' ' else c).splitOn " ").filter (!·.isEmpty))

mutual

/-- The words a subtree shows a sighted reader, onto `acc`: its text, each
element closed by a space so adjacent blocks keep their words apart, with
every `hidden` or `aria-hidden="true"` subtree, stylesheet and script left
out — a speaker note (`hidden`), an alternation's other group, a
decorative strip. A hand-rolled walk because `Html.Node` has no generic
fold; the list companion keeps it structural. -/
def shownWordsOne (acc : String) : Node → String
  | .text s => acc ++ s
  | .style _ => acc
  | .script _ _ => acc
  | .elem _ attrs kids =>
    if attrs.any (fun kv => kv.1 == "hidden" || (kv.1 == "aria-hidden" && kv.2 == "true"))
    then acc
    else shownWordsList acc kids.toList ++ " "

def shownWordsList (acc : String) : List Node → String
  | [] => acc
  | k :: rest => shownWordsList (shownWordsOne acc k) rest

end

/-- A deck stage's name: its title, or — untitled, as a title page or a
standout statement is — the words it shows (`shownWordsList` over its
emitted children: a speaker note or a hidden alternative never leaks into
the name), or at the last the engine's word the untitled frame's anchor
already starts from (`slide`). -/
def frameName (title : Array Inline) (kids : Array Node) : String :=
  firstNonBlank (squashSpace (Ir.plainText title))
    (firstNonBlank (squashSpace (shownWordsList "" kids.toList)) "slide")

theorem frameName_contract (title : Array Inline) (kids : Array Node) :
    nonBlank (frameName title kids) = true :=
  firstNonBlank_contract _ _ (firstNonBlank_contract _ _ (by decide))

/-- A themed section page's name: its title, else the engine's word its
anchor would start from (`section`). -/
def sectionPageName (title : Array Inline) : String :=
  firstNonBlank (squashSpace (Ir.plainText title)) "section"

theorem sectionPageName_contract (title : Array Inline) :
    nonBlank (sectionPageName title) = true :=
  firstNonBlank_contract _ _ (by decide)

/-- A deck stage's keyboard door. On the paged deck every stage is a scroll
container — content past the stage scrolls inside it (`deckStageRule`,
`overflow-y: auto`) — and the constant script binds its keys on the
document, so a reader whose focus has no way into the stage cannot scroll
what spills (WCAG 2.2 SC 2.1.1; axe `scrollable-region-focusable`).
`tabindex="0"` puts the stage in the tab order and the name makes it a
named region (HTML-AAM: a `section` with an accessible name is a
`region`), so each stop announces which slide it is. Markup only: the
script is untouched (`deck_script_constant`). Outside the deck a stage is a
handout card that never scrolls, and carries neither. -/
def stageAttrs (deck : Bool) (name : String) : Array (String × String) :=
  if deck then #[("tabindex", "0"), ("aria-label", name)] else #[]

/-- The picture's role and name (`pictureAltAttrs` over its resolved
alternative) and its class hook. -/
def pictureRole (loc : Locale) (pic : Ir.Pic.Picture) : Array (String × String) :=
  pictureAltAttrs (figureWord loc) pic.alternative ++ #[("class", "picture")]

/-- **The svg's role and name project the one IR value** (`_projects`):
`Ir.Pic.Picture.alternative`, the value the PDF's picture leaf carries too
(`Struct.picture_leaf_projects`). -/
theorem html_picture_name_projects (loc : Locale) (pic : Ir.Pic.Picture) :
    pictureRole loc pic =
      pictureAltAttrs (figureWord loc) pic.alternative ++ #[("class", "picture")] := rfl

/-- The box a picture's SVG declares: the IR's one box under the driver's
label measurement (`Ir.Pic.Picture.box`) — the declared box exactly, else
every mark's ink and every node's border — so the `viewBox` is the box the
PDF reserves, never the hull of label anchors. -/
def pictureBoxOf (cfg : Config) (pic : Ir.Pic.Picture) : Ir.Pic.Box :=
  pic.box cfg.labelMetric

/-- The picture as inline SVG. The declared box is a size, never a clip
(`Ir.Pic.Picture.declared`): the SVG declares `overflow` visible as its
own presentation attribute, so ink placed past the box paints as the PDF
paints it, whatever stylesheet mode the page ships under — an inline
SVG's user-agent default is `overflow: hidden`. -/
def pictureSvg (cfg : Config) (pic : Ir.Pic.Picture) : Node :=
  let ((px0, py0), (px1, py1)) := pictureBoxOf cfg pic
  -- The declared baseline is where the line stands (`Ir.Pic.Picture.rise`),
  -- the value the PDF sets the picture's depth by.
  Html.elem "svg" (pictureKids pic px0 py1 cfg.labelMetric)
    (pictureBox cfg (px1 - px0) (py1 - py0) (pic.rise cfg.labelMetric) ++
      pictureRole cfg.locale pic ++ #[("overflow", "visible")])

/-- **A picture's SVG never clips its ink** (`_contract`): every picture
ships `overflow="visible"`, the HTML half of the IR's "ink may stand
outside it, and nothing is clipped". -/
theorem pictureSvg_overflow_contract (cfg : Config) (pic : Ir.Pic.Picture) :
    (match pictureSvg cfg pic with
      | .elem _ attrs _ => attrOf? attrs "overflow"
      | _ => none) = some "visible" := by
  rcases h : pic.box cfg.labelMetric with ⟨⟨x0, y0⟩, ⟨x1, y1⟩⟩
  rcases ha : pic.alternative with _ | _ | t <;>
    simp [pictureSvg, pictureBoxOf, h, ha, Html.elem, pictureBox, pictureRole, pictureAltAttrs,
      attrOf?] <;>
    split <;> (try split) <;> simp

/-- **The SVG's box is the IR's box** (`_projects`): the `viewBox` a
picture's SVG declares spans `Ir.Pic.Picture.box` under the configured
measurement, width by height — the value the PDF reserves
(`Layout.pictureBox`), never a second hull. The HTML half of
`Pdf.picture_box_agree`. -/
theorem pictureViewBox_projects (cfg : Config) (pic : Ir.Pic.Picture) :
    (match pictureSvg cfg pic with
      | .elem _ attrs _ => attrOf? attrs "viewBox"
      | _ => none) =
      some s!"0 0 {((pic.box cfg.labelMetric).2.1 - (pic.box cfg.labelMetric).1.1).toPtString} \
{((pic.box cfg.labelMetric).2.2 - (pic.box cfg.labelMetric).1.2).toPtString}" := by
  rcases h : pic.box cfg.labelMetric with ⟨⟨x0, y0⟩, ⟨x1, y1⟩⟩
  simp [pictureSvg, pictureBoxOf, h, Html.elem, pictureBox, attrOf?]

/-- The abstract region's classes: the engine's own hook, and the size
step its body sets at, read from the one resolving site the PDF's body
reads (`Ir.abstractBodySize`, `Layout`'s `.abstract` arm). -/
def abstractClass (styles : Ir.Styles) : String :=
  let step := Ir.abstractBodySize styles
  "abstract size-" ++ step

mutual

def blockNode (cfg : Config) (b : Block) : Node :=
  match b with
  | .para content =>
    -- A paragraph holding only label anchors is not prose: its anchors
    -- ship as an inline span, never a <p> whose rhythm margin would open
    -- a blank line.
    if !content.isEmpty && content.all (fun x => x matches .label _) then
      Html.elem "span" (inlines cfg content)
    else
    if hasFill content then
      let rows := splitAtBreaks content
      if rows.size == 1 then
        fillRow cfg "p" "entry" content
      else
        Html.elem "p" (rows.map fun row => fillRow cfg "span" "entry-row" row)
          #[("class", "entry-rows")]
    else
      Html.elem "p" (inlines cfg content)
  | .section level _ num title =>
    let element := match level with
      | 0 => "titlepage"
      | 1 => "section"
      | 2 => "subsection"
      | _ => "subsubsection"
    let tag := headingTag level
    let st := (cfg.styles.find? element).getD {}
    let st := if level == 0 then Ir.titleHeadingStyle st else st
    let title := match st.font, cfg.slotTitle && level == 0 with
      | some tpl, false => fillTemplate tpl title
      | _, _ => title
    -- The number is a structural piece of the heading, never text glued
    -- into the title: the anchor slug reads the title alone, and a
    -- stylesheet can address the number (`pandoc` sets the same span).
    let kids := inlines cfg title
    let kids := match num with
      | some n => #[Html.elem "span" #[Html.text n]
          #[("class", "section-number")], Html.text "\u2003"] ++ kids
      | none => kids
    let attrs := if st.rule.isSome then #[("class", "ruled")] else #[]
    let attrs := if cfg.deck && level == 1 then
      attrs.push ("style", "color: var(--sectiontitlefg, var(--fg))") else attrs
    Html.elem tag kids attrs
  | .list ordered items =>
    -- A description list (every item run in by its label) is HTML's own
    -- `<dl>`; the label reading is the page's (`Ir.descLabel?`).
    let desc := !ordered && !items.isEmpty && items.all fun it => match it[0]? with
      | some (Block.para c) => (Ir.descLabel? c).isSome
      | _ => false
    if desc then Html.elem "dl" (descItemsInto cfg.into #[] items.toList) else
    let tag := if ordered then "ol" else "ul"
    Html.elem tag (listItemsInto cfg.into #[] items.toList)
  | .center body =>
    -- A display formula's block is the `.display` paragraph the base
    -- sheet's display rules address — the same shape the PDF walk reads
    -- (`Ir.displayContent?`); a `<p>`, as a display formula is phrasing
    -- content standing in one, and its display rule outranks the peer
    -- rule by standing later at equal specificity. Any other centred
    -- scope is a `.centered` div.
    match Ir.displayContent? body with
    | some content => Html.elem "p" (inlines cfg content) #[("class", "display")]
    | none =>
      Html.elem "div" (blockNodesInto cfg.into #[] body.toList) #[("class", "centered")]
  -- The declared side as a class, resolved through the IR's own reader
  -- (`Ir.FlushSide.align`) so the stylesheet's `text-align` and the page's
  -- line origin cannot name different edges (`ragged_sides_agree`). Flush
  -- left is HTML text's resting state and the class still re-declares it,
  -- so the setting survives a centred ancestor (text-align inherits).
  | .ragged flush body =>
    Html.elem "div" (blockNodesInto cfg.into #[] body.toList)
      #[("class", raggedClass flush)]
  -- The block half of the class hook: the authored name as a class on a
  -- generic flow container, through the typed tree and the escaper. The
  -- trivlist and in-paragraph roles only space, so each is a class on the
  -- environment's own element and never an element: a consumer sheet's
  -- child combinators (`main > .centered`) were written against the tree
  -- without it, and the list levels read the in-paragraph one to spend
  -- `\topsep` without `\partopsep` (`listLevelRules`).
  | .role n body =>
    -- A title slot's role marks its content as the slot's own: set under
    -- the slot's template alone (`Config.slotTitle`), placed by the rule
    -- `titleSlotCss` writes for this class hook.
    let cfg := if (Ir.titleSlotOf ((cfg.styles.find? "titlepage").getD {}).slots n).isSome
      then { cfg with slotTitle := true } else cfg
    let kids := blockNodesInto cfg.into #[] body.toList
    -- A page-model mark (`Ir.pageMarkerRole`) is a fact of the page alone:
    -- a continuous medium has no page top, interline glue, or running folio.
    if Ir.pageMarkerRole n then Html.text "" else
    match n == Ir.trivlistRole || n == Ir.inParagraphRole || (Ir.thmSpaceOf? n).isSome,
        kids.toList with
    | true, [k] => withClass (roleClass n) k
    -- A display's context (`Ir.DisplayCtx`) is the PDF's placement fact:
    -- the page's element tree is the display's own.
    | false, [k] =>
      if (Ir.DisplayCtx.ofRole? n).isSome then k
      else Html.elem "div" kids #[("class", roleClass n)]
    | _, _ => Html.elem "div" kids #[("class", roleClass n)]
  -- HTML anchors have a transparent content model, so one anchor may own
  -- arbitrary flow children; elaboration rejects every anchor-bearing
  -- descendant before this node is built.
  | .link target body =>
    Html.elem "a" (blockNodesInto cfg.into #[] body.toList)
      #[("href", target), ("style", "display: block; color: inherit")]
  -- A quotation is HTML's own construct: `<blockquote>` carries the
  -- set-off semantics that the PDF path expresses as margins.
  | .quote body =>
    Html.elem "blockquote" (blockNodesInto cfg.into #[] body.toList)
  -- beamer's titled block: a <section> with its header, through the typed
  -- tree and the escaper; the kind rides as a class so the stylesheet (a
  -- reader's own included) can address each. An untitled block keeps its
  -- section and drops the header, as the PDF drops the bar.
  | .titled kind title body =>
    let head : Array Html.Node := if title.isEmpty then #[] else
      #[Html.elem "header" (inlines cfg title) #[]]
    Html.elem "section" (head ++ blockNodesInto cfg.into #[] body.toList)
      #[("class", s!"block block-{kind.name}")]
  -- The equation's number is a structural element beside the formula,
  -- never text glued into it: a flex row whose math child takes the
  -- measure and whose tag sits right, the amsmath shape. `display` puts
  -- it inside the display skips, as the PDF's `.equation` arm does.
  | .equation num content =>
    let kids := inlines cfg content
    Html.elem "div"
      (kids.push (Html.elem "span" (inlines cfg num) #[("class", "eqnum")]))
      #[("class", "equation display")]
  -- The abstract is HTML's own titled region: a <section> with a heading,
  -- exactly the thing a reader's tooling looks for. The heading word is
  -- class furniture (article.cls's \abstractname), generated here as the
  -- PDF generates its centred bold line.
  | .abstract body =>
    -- The heading is an <h2>, so a declared `\style{section}` reaches it
    -- through the h2 selector — the abstract follows the section heading
    -- by construction (`Ir.abstract_heading_follows_section`); centred, as
    -- the class centres it (article.cls §abstract). The body's size is the
    -- one the PDF sets (`Ir.abstractBodySize`), on the region, where the
    -- rem-sized heading does not inherit it.
    Html.elem "section"
      (#[Html.elem "h2" #[Html.text cfg.locale.abstract] #[("style", "text-align: center")]] ++
        blockNodesInto cfg.into #[] body.toList)
      #[("class", abstractClass cfg.styles)]
  | .columns cols =>
    -- Side-by-side columns as a grid: the declared fractions become
    -- percentage tracks, so the HTML column really is as wide as the PDF's.
    -- A lone box takes its scope's side (`alignScopeRule`), as the page
    -- gives it the side's share of its slack; a row spreads.
    let justify := if cols.size == 1 then "var(--ltx-box-justify, start)" else "space-between"
    let total := cfg.measureValues.lineWidth
    let declared := cols.foldl (fun s c => s + (c.1.resolve total).getD 0) 0
    let unspecified := cols.foldl (fun n c => if c.1.declared then n else n + 1) 0
    let share := if unspecified > 0 then max 0 (total - declared) / unspecified else 0
    Html.elem "div" (columnNodesInto cfg.into total share #[] cols.toList)
      #[("class", "columns"),
        ("style", s!"display: grid; grid-template-columns: {gridTracks cols}; " ++
          s!"justify-content: {justify}")]
  | .onSteps spec body =>
    -- The block form of the inline step arm: visible — the handout floor —
    -- with its `--step` index for the class-gated uncover, range as data,
    -- and the declared end on its own nested carrier.
    overlayNode "div" cfg.overlaySteps spec (blockNodesInto cfg.into #[] body.toList)
  | .altSteps spec firstPage otherPage =>
    -- The block form of the inline alternation arm. The groups need one
    -- carrier each so a selector can reach each range (`alt_backend_agree`);
    -- the pair rides a container of its own because a block arm ships one
    -- node, and the container carries nothing — no range, no side, no rule.
    Html.elem "div"
      (overlayAlternatives "div" cfg.overlaySteps spec
        (blockNodesInto cfg.into #[] firstPage.toList) (blockNodesInto cfg.into #[] otherPage.toList))
      #[("class", "alt-pair")]
  | .note body =>
    -- Inert and hidden: available to a speaker view, invisible in the deck
    -- and in print.
    Html.elem "aside" (blockNodesInto cfg.into #[] body.toList)
      #[("class", "note"), ("hidden", "hidden")]
  | .pagebreak =>
    -- A continuous medium has no page to break; the boundary leaves no
    -- element behind.
    Html.text ""
  | .spaced before body =>
    -- A token-declared gap defers to its own custom property, so a reader
    -- overriding `--subtitlegap` moves this margin; a computed gap prints
    -- the length it was handed (`cssSourced`).
    let style := s!"margin-top: {cssSourced before}"
    Html.elem "div" (blockNodesInto cfg.into #[] body.toList)
      #[("class", "spaced"), ("style", style)]
  | .verbatim covered s spec =>
    -- `<pre>` preserves the raw lines; the escaper makes the content inert.
    -- The covered shade never reaches HTML (dimming is the PDF handout's;
    -- the HTML deck keeps every step visible), but honesty if it ever does.
    -- Declared line numbers are a CSS counter on per-line elements — the
    -- numbers are generated furniture the stylesheet draws, so a reader's
    -- copy takes the code alone; nothing is scripted. A declared caption
    -- wraps the block in the figure-caption shape, the caption above
    -- (listings.sty: `\lst@Key{captionpos}{t}` — above is the default),
    -- numbered from the one site both backends read (`Ir.listingCaption`).
    -- A declared language is the `code` element's class, read from the one
    -- IR projection the markdown fence reads too (`listing_language_agree`);
    -- the attribute value goes through the escaper as every attribute does.
    let lines := spec.tokenLines s
    let codeAttrs : Array (String × String) := match spec.htmlClass with
      | some c => #[("class", c)]
      | none => #[]
    let codeKids := Id.run do
      let mut kids := #[]
      for i in [:lines.size] do
        if i > 0 then kids := kids.push (Html.text "\n")
        let line := inlines cfg
          (lines[i]!.map (Listing.tokenInline cfg.pal cfg.listingGround covered
            (style := spec.style)))
        kids := if spec.numbers then
          kids.push (Html.elem "span" line #[("class", "line")])
          else kids ++ line
      return kids
    let code := Html.elem "code" codeKids codeAttrs
    let design := Ir.Design.ofPalette cfg.pal
    let paint := if spec.highlight.isEmpty then
        (covered.map fun c => s!"color: {cssColor c};").getD ""
      else
        s!"background: {cssColor (cfg.listingGround.getD design.bg)}; " ++
        s!"color: {cssColor (covered.getD (cfg.listingFg.getD design.fg))};"
    let style := String.intercalate " "
      (((fontStyleDecls cfg.page.scale spec.fontSize (fontLengthCss cfg)).getD #[]).toList) ++
      (match spec.fontSize with
        | .fontSize .. => ""
        | _ => s!" line-height: {decMilli (Ir.leadingMilli * cfg.page.leading / 1000)};") ++
      s!" tab-size: {spec.tabSize};" ++
      (if spec.breakLines then " white-space: pre-wrap;" else "") ++
      (if paint.isEmpty then "" else " " ++ paint)
    let pre := Html.elem "pre" #[code]
      ((if spec.numbers then #[("class", "numbered")] else #[]) ++
       #[("style", style)] ++
       -- A code block scrolls sideways (`overflow-x: auto` in `baseCss`),
       -- so it is a tab stop: a keyboard reaches what a long line spills
       -- (WCAG 2.2 SC 2.1.1). Its role takes no name, so it carries none.
       #[("tabindex", "0")])
    match spec.caption with
    | some (n, cap) =>
      Html.elem "figure"
        #[Html.elem "figcaption" (inlines cfg (Ir.listingCaption cfg.locale n cap)),
          pre]
        #[("class", "listing")]
    | none => pre
  | .algorithm numbered semis lines =>
    -- Pseudocode as nested ordered lists: one <ol> per block, depth from
    -- nesting, line numbers by a CSS counter when declared (declarative,
    -- no script). Every line — openers, closers, statements — is one
    -- <li>, through the shared rendering `Ir.AlgLine.rendered`, the site
    -- the PDF paragraphs read too. The nesting is `algNest`'s, and
    -- `algorithm_lines_agree` states what it conserves: no line lost, none
    -- reordered, so an else standing at its if's level nests exactly once.
    -- Native list semantics carry the structure; no role attribute is
    -- needed.
    let words := Ir.algWords cfg.locale.tag
    let muted := Ir.mutedOf cfg.pal
    Html.elem "ol"
      (algRenderList (fun l => inlines cfg (Ir.AlgLine.rendered words semis muted l))
        #[] (algNest lines).toList)
      #[("class", if numbered then "algorithm numbered" else "algorithm")]
  | .rule color name thickness =>
    -- The title page's separator: an <hr> carrying the palette variable for
    -- its colour and the token variable for its thickness, so a host page
    -- can override either. The thickness deferred to nothing until the IR
    -- carried its token name beside the resolved length.
    let c := match name with
      | some n => s!"var(--{n}, {cssColor color})"
      | none => cssColor color
    Html.elem "hr" #[] #[("class", "separator"),
      ("style", s!"border: none; height: {cssSourced thickness}; background: {c}")]
  | .frame title standout valign _ body =>
    -- One slide of the deck: a linear readable section in every class. On
    -- the paged deck (`cfg.deck`) the slide is a flex column the height of
    -- the viewport, and its declared vertical distribution is realized as
    -- two spacers whose flex-grow carries the declared ratio
    -- (`vdistShares`) — glue, exactly as the PDF page distributes its
    -- leftover; in block flow (the print handout, every other class) an
    -- empty div has no height and the declaration rides along inert.
    let cfg := cfg.inFrame b
    let header := if title.isEmpty then #[]
      else #[Html.elem "header" #[Html.elem "h2" (inlines cfg title)]]
    let cls := if standout then "slide standout"
      else if valign matches .golden then "slide title-page" else "slide"
    let design := Ir.Design.ofPalette cfg.pal
    let listingFg := if standout then some design.standout.fg
      else if valign matches .golden then design.titlepage.map (·.fg) else none
    let bodyCfg := { cfg.into with
      listingGround := Ir.frameGroundOf cfg.pal standout valign, listingFg }
    let kids := blockNodesInto bodyCfg #[] body.toList
    let kids := if cfg.deck then
        let (above, below) := vdistShares valign
        let spacer (n : Nat) : Array Html.Node :=
          if n == 0 then #[] else
            #[Html.elem "div" #[] #[("class", "fill"), ("style", s!"flex-grow: {n}")]]
        let up := spacer above
        let down := spacer below
        up ++ kids ++ down
      else kids
    Html.elem "section" (header ++ kids)
      (#[("class", cls)] ++ stageAttrs cfg.deck (frameName title kids))
  | .framefoot _ =>
    -- A state change for the deck walk in `emit`, not content: nothing to
    -- render where one stands alone.
    Html.text ""
  | .setPalette _ =>
    -- A state change the sibling walks replay (`blockNodesInto`, the
    -- article and deck walks): nothing to render where one stands alone.
    Html.text ""
  | .setTokens _ =>
    Html.text ""
  | .only targets body =>
    -- `emit` already kept this node for HTML (`Ir.keepFor "html"`): by here
    -- it is a transparent group. The target set rides as data, so a reader
    -- of the page can see the provenance of single-surface content.
    Html.elem "div" (blockNodesInto cfg.into #[] body.toList)
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
    Html.elem "nav" (blockNodesInto cfg.into #[] body.toList) (labelAttrs ++ pinAttrs)
  | .logo _ =>
    -- A state change, not content: the deck's top-level walk reads it
    -- (`attachLogo` ships the state as frame furniture), `blockNodesInto`
    -- skips it, and `emitTree` names the drop in the classes that keep it
    -- paged-media furniture (W0007). This arm only closes the match.
    Html.text ""
  | .picture pic => pictureSvg cfg pic
  -- booktabs' formal table: `tableNode` above, where the header projection
  -- theorem (`th_iff_header_row`) can read the row builder.
  | .table cols padL padR rows rules spans => tableNode cfg cols padL padR rows rules spans
  -- `<figure>`/`<figcaption>` is HTML's own construct for a captioned
  -- object; the caption keeps its source-order side. The gaps are the
  -- same tokens the PDF path reads (`--floatsep`, `--captionsep`), with
  -- the rhythm defaults from `Ir.caption_gaps_rhythm` as fallbacks.
  | .float kind num capAbove body caption =>
    let capNode : Array Node :=
      if caption.isEmpty then #[]
      else #[Html.elem "figcaption"
        (inlines cfg (Ir.numberedCaption cfg.locale kind num caption))]
    let kids := blockNodesInto cfg.into #[] body.toList
    let kindCls := floatKindClass kind
    let cls := if kind == .figure then "float" else "float " ++ kindCls
    Html.elem "figure" (if capAbove then capNode ++ kids else kids ++ capNode)
      #[("class", cls)]
  -- The reference list: one item per resolved entry, carrying the anchor
  -- its citations link to. The key is author text from the `.bib` and
  -- enters the id through the typed tree, so it passes the attribute
  -- escaper by construction — no spelling of a key breaks out of the
  -- attribute. The style's marker leads the item; an author-year list
  -- marks nothing and the class carries that.
  | .bibliography _ _ items =>
    let marked := items.any (·.marker.isSome)
    -- `role="list"`: the list's markers are drawn by its own grid, and a
    -- list styled without them loses its list semantics in WebKit.
    Html.elem "ul" (items.map (bibItemNode cfg))
      #[("class", if marked then "bibliography" else "bibliography unmarked"),
        ("role", "list")]

/-- The accumulator threads through the sibling walk, as in
`inlineNodesInto` — and so does the epoch: a `.setPalette`/`.setTokens`
updates the state in force, and every following sibling carries the
accumulated redefinitions on its style attribute (flow scope realized
sibling-wise; past the enclosing element's close the properties no longer
reach, except a frame's outgoing palette, which continues into later
frames as on the PDF path). -/
private def blockNodesInto (cfg : Config) (acc : Array Node) : List Block → Array Node
  | [] => acc
  | .logo _ :: rest => blockNodesInto cfg acc rest
  | .setPalette p :: rest =>
    blockNodesInto (cfg.advancePalette p) acc rest
  | .setTokens tk :: rest =>
    let style := joinStyles cfg.epochStyle (epochTokenStyle cfg.tokens tk)
    blockNodesInto { cfg with tokens := tk, epochStyle := style } acc rest
  -- A page-model mark (`Ir.pageMarkerBlock`) ships no node: a continuous
  -- medium has no page top and no interline glue.
  | b :: rest =>
    if Ir.pageMarkerBlock b then blockNodesInto cfg acc rest
    else blockNodesInto (cfg.afterFrame b)
      (acc.push (withEpoch cfg.epochStyle cfg.epochGround (blockNode cfg b))) rest

private def columnNodesInto (cfg : Config) (total share : Sp) (acc : Array Node) :
    List (BoxWidth × Array Block) → Array Node
  | [] => acc
  | (w, body) :: rest =>
    -- The point the box stands on the row's baseline by (`Ir.BoxPos`), as
    -- the grid's own baseline alignment says it; a top box keeps the
    -- grid's default. Every box is also the query container for affine
    -- local measures in its content: `cqi` reads this column's actual
    -- inline size, never the outer page's.
    let align := match w.pos with
      | .top => ""
      | .first => "align-self: baseline"
      | .center => "align-self: center"
      | .last => "align-self: last baseline"
    let style := if align.isEmpty then "container-type: inline-size"
      else "container-type: inline-size; " ++ align
    let child := cfg.atMeasure ((w.resolve total).getD share)
    columnNodesInto cfg total share
      (acc.push (Html.elem "div" (blockNodesInto child #[] body.toList)
        #[("class", "column"), ("style", style)])) rest

private def listItemsInto (cfg : Config) (acc : Array Node) : List (Array Block) → Array Node
  | [] => acc
  | item :: rest =>
    listItemsInto cfg (acc.push (Html.elem "li" (listItem cfg item.toList))) rest

/-- A description list's items as HTML's own description list: each label a
`<dt>` (the inlines the page runs in, `Ir.descLabel?`), the text after it
and the item's further blocks a `<dd>` — one paragraph's text bare, as a
list item's is (`listItem`). -/
private def descItemsInto (cfg : Config) (acc : Array Node) : List (Array Block) → Array Node
  | [] => acc
  | ⟨Block.para c :: bs⟩ :: rest =>
    let (label, after) := (Ir.descLabel? c).getD (#[], c)
    let dd := match bs with
      | [] => inlines cfg after
      | _ => blockNodesInto cfg #[Html.elem "p" (inlines cfg after) #[]] bs
    descItemsInto cfg ((acc.push (Html.elem "dt" (inlines cfg label) #[])).push
      (Html.elem "dd" dd #[])) rest
  | item :: rest =>
    descItemsInto cfg ((acc.push (Html.elem "dt" #[] #[])).push
      (Html.elem "dd" (listItem cfg item.toList) #[])) rest

-- A one-paragraph item carries its content directly: wrapping it in <p> is
-- what makes generated lists render with extra vertical space.
def listItem (cfg : Config) : List Block → Array Node
  | [.para content] => inlines cfg content
  | [] => #[]
  | .setPalette p :: rest =>
    listItem (cfg.advancePalette p) rest
  | .setTokens tk :: rest =>
    let style := joinStyles cfg.epochStyle (epochTokenStyle cfg.tokens tk)
    listItem { cfg with tokens := tk, epochStyle := style } rest
  | b :: rest =>
    if Ir.pageMarkerBlock b then listItem cfg rest
    else blockNodesInto cfg #[withEpoch cfg.epochStyle cfg.epochGround (blockNode cfg b)] rest

end

/-- Continuous HTML projects the IR opening's content-free marker fact:
it creates no wrapper, counter text, or page boundary in the typed tree.
The titlepage's body remains the ordinary sibling flow. -/
private theorem pageOpening_projects (cfg : Config) (acc : Array Node)
    (n : String) (opening : Ir.PageOpening) (rest : List Block)
    (h : Ir.pageOpeningOfRole? n = some opening) :
    blockNodesInto cfg acc (.role n #[] :: rest) = blockNodesInto cfg acc rest := by
  simp only [blockNodesInto, Ir.pageMarkerBlock, Array.isEmpty_empty,
    Ir.pageOpening_marker_exact n opening h, Bool.true_and, ite_true]

/-- Facts of the emitted tree that the landmark and anchor checks judge:
the `<nav>` landmarks, the `id` anchors, and the in-page link targets
(`href="#..."`), collected in one walk over the typed tree. The artifact is
judged, never the IR — a backend conditional may have dropped a nav or an
anchor on the way here, and only the tree knows what this page carries. -/
private structure PageFacts where
  /-- DOM anchors with the canonical snap that contains them, when any. -/
  ids : Array (String × Option String) := #[]
  fragmentRefs : Array String := #[]
  /-- Canonical labels read by the deck's script, in snap order. -/
  slideLabels : Array String := #[]
  deck : Bool := false
  /-- Unlabeled `<nav>` landmarks: a labeled one is distinguishable, so
  only these count toward W0325 (ARIA Landmark Regions). -/
  navs : Nat := 0
  /-- Elements carrying the `reveal-scroll` class: the page-level reveal
  CSS and script ship exactly when one is here — judged over the tree, so
  a reveal a conditional dropped ships nothing. -/
  reveals : Nat := 0

mutual

private def pageFactsOne (stage : Option String) (acc : PageFacts) : Node → PageFacts
  | .text _ => acc
  | .style _ => acc
  | .script _ text => { acc with deck := acc.deck || text == deckScript }
  | .elem tag attrs kids =>
    let stage := (attrOf? attrs "data-slide-label").orElse (fun _ => stage)
    let acc := if attrs.any (·.1 == "data-snap") then
        { acc with slideLabels := acc.slideLabels ++ stage.toArray } else acc
    let acc := if tag == "nav" && attrs.all (·.1 != "aria-label") then
        { acc with navs := acc.navs + 1 } else acc
    let acc := if attrs.any (fun kv => kv.1 == "class" && kv.2 == "reveal-scroll") then
        { acc with reveals := acc.reveals + 1 } else acc
    let acc := attrs.foldl (init := acc) fun a kv =>
      if kv.1 == "id" then { a with ids := a.ids.push (kv.2, stage) }
      else if kv.1 == "href" && kv.2.startsWith "#" then
        { a with fragmentRefs := a.fragmentRefs.push kv.2 }
      else a
    pageFactsList stage acc kids.toList

private def pageFactsList (stage : Option String) (acc : PageFacts) : List Node → PageFacts
  | [] => acc
  | k :: rest => pageFactsList stage (pageFactsOne stage acc k) rest

end

/-- The first free anchor among `taken` (`base`, `base-2`, `base-3`, …),
plus the holder's title when a *different* title collides — the W0327
case. k assigned ids can block at most k candidates, so the first free
one is always found among the k+1 checked. One uniqueness rule for every
id this backend assigns: the article's sections and the deck's frames
claim through the same door, which `getElementById` semantics require.

`taken` is keyed, not ordered: every id in it was put there by this
function after finding it free, so the keys are distinct and the only
question ever asked of the store is "who holds this id" — an answer no
ordering changes. Scanning for it made a shared slug cost a cube. -/
private def claimId (taken : Std.HashMap String String) (base text : String) :
    String × Option String := Id.run do
  let mut id := base
  let mut clash : Option String := none
  for n in [2 : taken.size + 3] do
    match taken[id]? with
    | some holder =>
      if holder != text && clash.isNone then
        clash := some holder
      id := s!"{base}-{n}"
    | none => break
  return (id, clash)

/-- The first stage name no earlier stage on the page carries: `name`,
then `name (2)`, `name (3)`, … Two regions named alike are one landmark to
a reader moving by landmark (axe `landmark-unique`), so a repeated title
takes its occurrence number, as its repeated anchor does (`claimId`); k
names taken block at most k candidates, so the first free one is always
found among the k+1 checked. -/
private def claimName (taken : Std.HashSet String) (name : String) : String := Id.run do
  let mut out := name
  for n in [2 : taken.size + 3] do
    if taken.contains out then out := s!"{name} ({n})" else break
  return out

/-- A stage with its accessible name claimed (`claimName`) against the
names the page's earlier stages carry, and the claim recorded. -/
private def claimStageName (taken : Std.HashSet String) : Node → Node × Std.HashSet String
  | .elem tag attrs kids =>
    match attrOf? attrs "aria-label" with
    | some name =>
      let got := claimName taken name
      (.elem tag (attrs.map fun kv => if kv.1 == "aria-label" then (kv.1, got) else kv) kids,
        taken.insert got)
    | none => (.elem tag attrs kids, taken)
  | .text s => (.text s, taken)
  | .style s => (.style s, taken)
  | .script attrs s => (.script attrs s, taken)

/-- The snap spacers of a stepped frame's track, one per overlay step:
each carries the canonical fragment `<label>.k` and claims its title-slug
alias `<frame>-k` through the same door as
every id this backend assigns (`claimId`), a clash named exactly as a
frame title's is. Recursion over the step list with threaded
accumulators, so the spacer count is a statement
(`track_snaps_exact`), not a reading of a loop. -/
private def snapWalk (id text label : String) (kids : Array Node)
    (taken : Std.HashMap String String) (diags : Array Diag) :
    List Nat → Array Node × Std.HashMap String String × Array Diag
  | [] => (kids, taken, diags)
  | k :: rest =>
    let (sid, sclash) := claimId taken s!"{id}-{k}" text
    let diags := match sclash with
      | some holder => diags.push (Diag.of .W0327
          s!"frames {holder.quote} and {text.quote} share the \
anchor '{id}-{k}'; the step anchor becomes '{sid}'"
          (help := some s!"an in-page link '#{id}-{k}' reaches only \
the first; retitle one frame, or link to '#{sid}'"))
      | none => diags
    snapWalk id text label
      (kids.push (Html.elem "div" #[]
        #[("class", "snap"), ("id", sid), ("data-snap", ""),
          ("data-slide-label", s!"{label}.{k}")]))
      (taken.insert sid text) diags rest

/-- The steps a frame with `steps` overlay steps snaps through: 1 to
`steps`, the range both the spacer walk and the PDF handout's per-step
pages traverse. -/
private def stepList (steps : Nat) : List Nat :=
  (List.range steps).map (· + 1)

@[simp] private theorem stepList_length (steps : Nat) :
    (stepList steps).length = steps := by
  simp [stepList]

private theorem snapWalk_count (id text label : String) :
    ∀ (ks : List Nat) (kids : Array Node) (taken : Std.HashMap String String)
      (diags : Array Diag),
      (snapWalk id text label kids taken diags ks).1.size = kids.size + ks.length
  | [], _, _, _ => rfl
  | k :: rest, kids, taken, diags => by
    unfold snapWalk
    rw [snapWalk_count id text label rest]
    simp only [Array.size_push, List.length_cons]
    omega

/-- The step count the two backends agree on, HTML half, stated over
`Ir.frameSteps`: a stepped frame's track carries exactly
`frameSteps frame` snap spacers beside its one sticky stage — the count
`deckStepCss` reads back as `--steps` and the very count the PDF handout
paginates the frame by (that half is the owed `pages_partition_frames`;
there is no umbrella theorem over the two, one half being owed). -/
private theorem track_snaps_exact (id text label : String)
    (taken : Std.HashMap String String) (diags : Array Diag)
    (frame : Ir.Block) :
    (snapWalk id text label #[] taken diags
        (stepList (Ir.frameSteps frame))).1.size
      = Ir.frameSteps frame := by
  rw [snapWalk_count, stepList_length]
  simp

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
  let mut taken : Std.HashMap String String := {}
  let mut diags : Array Diag := #[]
  -- The epoch state threads through the article's top level exactly as
  -- through `blockNodesInto`: each node after a body declaration carries
  -- the redefinitions, whichever section it closes into.
  let mut cfg := cfg
  for b in blocks do
    match b with
    | .setPalette p =>
      cfg := cfg.advancePalette p
    | .setTokens tk =>
      let style := joinStyles cfg.epochStyle (epochTokenStyle cfg.tokens tk)
      cfg := { cfg with tokens := tk, epochStyle := style }
    | .section 1 _ _ title =>
      out := close out cur openId
      let text := Ir.plainText title
      let base := slug title
      let base := if base.isEmpty then "section" else base
      let (id, clash) := claimId taken base text
      if let some holder := clash then
        diags := diags.push (Diag.of .W0327
          s!"sections {holder.quote} and {text.quote} share the \
anchor '{base}'; the second becomes '{id}'"
          (help := some s!"an in-page link '#{base}' reaches only the first; \
retitle one section, or link to '#{id}'"))
      taken := taken.insert id text
      openId := some id
      cur := #[withEpoch cfg.epochStyle cfg.epochGround (blockNode cfg b)]
    | _ =>
      unless Ir.pageMarkerBlock b do cur := cur.push (withEpoch cfg.epochStyle cfg.epochGround (blockNode cfg b))
      cfg := cfg.afterFrame b
  return (close out cur openId, diags)

/-- Does an element take keyboard focus in sequential navigation — a tab
stop (HTML §6.6.3)? A `tabindex` that parses decides: zero or more is a
stop, a negative one takes focus from script only. With none, the elements
that take focus by default: a link (`a`/`area` with an `href`), an enabled
form control, `iframe`, `summary`, and media with `controls`. -/
def tabbable (tag : String) (attrs : Array (String × String)) : Bool :=
  match (attrOf? attrs "tabindex").bind String.toInt? with
  | some i => decide (0 ≤ i)
  | none =>
    ((tag == "a" || tag == "area") && (attrOf? attrs "href").isSome) ||
    (["button", "input", "select", "textarea"].contains tag &&
      (attrOf? attrs "disabled").isNone && attrOf? attrs "type" != some "hidden") ||
    tag == "iframe" || tag == "summary" ||
    ((tag == "audio" || tag == "video") && (attrOf? attrs "controls").isSome)

mutual

/-- Does a subtree hold a tab stop (`tabbable`) outside a `hidden` subtree —
which is not rendered, so nothing in it takes focus? A hand-rolled walk
because `Html.Node` has no generic fold; the list companion keeps it
structural. -/
def tabbableOne : Node → Bool
  | .elem tag attrs kids =>
    (attrOf? attrs "hidden").isNone && (tabbable tag attrs || tabbableList kids.toList)
  | .text _ => false
  | .style _ => false
  | .script _ _ => false

def tabbableList : List Node → Bool
  | [] => false
  | k :: rest => tabbableOne k || tabbableList rest

end

/-- Does an element stand `aria-hidden` over a tab stop, itself or below:
a keyboard lands on a control assistive technology is told is not there,
and it has no name to announce (WAI-ARIA 1.2, `aria-hidden`; axe
`aria-hidden-focus`). The judge counts such stops over a page
(`A11yFacts.hiddenTabStops`). -/
def hidesTabStop : Node → Bool
  | .elem tag attrs kids =>
    attrOf? attrs "aria-hidden" == some "true" && tabbableOne (.elem tag attrs kids)
  | .text _ => false
  | .style _ => false
  | .script _ _ => false

/-- A logo's content as decoration: every image's `alt` blank. -/
private def logoDecoration (content : Array Inline) : Array Inline :=
  Ir.mapInlines (fun x => match x with
    | .image src size _ => .image src size .undeclared
    | x => x) content

/-- A logo's box. A logo is decorative furniture by role
(`Ir.logoImageSrcs`), so its images ship `alt=""` (`deco`) and the box
leaves the accessibility tree (`role="presentation"`, `aria-hidden`) — WCAG
2.2 SC 1.1.1: pure decoration is implemented so assistive technology can
ignore it. Unless something in it takes focus — a linked logo: then hiding
the box would leave a keyboard stop with no name, so it ships as authored
(`authored`), the image's own `alt` naming its link. The box is hidden only
when nothing in it is a tab stop (`logoBox_hidden_contract`). -/
def logoBox (cls : String) (style : Option String) (deco authored : Array Node) : Node :=
  let styled := match style with
    | some s => #[("style", s)]
    | none => #[]
  if tabbableList deco.toList then
    Html.elem "div" authored (#[("class", cls)] ++ styled)
  else
    Html.elem "div" deco
      (#[("class", cls), ("role", "presentation"), ("aria-hidden", "true")] ++ styled)

/-- **A logo's box never hides a tab stop** (`_contract`): whatever the
logo holds, `aria-hidden` never stands over something a keyboard reaches. A
fact of the artifact: which elements take focus is HTML's, not the IR's. -/
theorem logoBox_hidden_contract (cls : String) (style : Option String)
    (deco authored : Array Node) :
    hidesTabStop (logoBox cls style deco authored) = false := by
  cases style <;> simp only [logoBox] <;> split <;>
    simp_all [hidesTabStop, tabbableOne, tabbable, attrOf?, Html.elem]

/-- A frame's (or section page's) logo, attached as the section's own
furniture: the logo in force at the deck position (`Ir.logoInForce`, the
same resolving site the PDF's furniture pass reads per page) renders into
the `.slide-logo` strip `deckLogoRule` pins to the stage's bottom band, as
decoration unless it holds a tab stop (`logoBox`) — the same judgement the
alt census makes (`Ir.logoImageSrcs`). The declared
alignment (`Ir.logoAlign`) rides as the strip's flex distribution, the
projection of the PDF's x placement from the one declared value. -/
private def attachLogo (cfg : Config) (node : Node)
    (logo : Option (Array Inline)) : Node :=
  match logo with
  | none => node
  | some content =>
    if content.isEmpty then node else
    match node with
    | .elem tag attrs kids =>
      let justify := match Ir.logoAlign cfg.styles with
        | "left" => "flex-start"
        | "center" => "center"
        | _ => "flex-end"
      Node.elem tag attrs (kids.push (logoBox "slide-logo"
        (some s!"justify-content: {justify}")
        (inlines cfg (logoDecoration content)) (inlines cfg content)))
    | .text s => .text s
    | .style s => .style s
    | .script attrs s => .script attrs s

mutual

/-- Read an image-use attribute in tree order, including hidden uses.
With no override, an `<img>` contributes `src` and a conversion placeholder
contributes `data-image-src`. The request census selects `data-image-index`
through the same walk. `Html.Node` has no generic fold; the list companion
keeps this walk structural. -/
private def imageAttrsOne (name : Option String) (acc : Array String) : Node → Array String
  | .elem tag attrs kids =>
    let acc :=
        match attrOf? attrs (name.getD (if tag == "img" then "src" else "data-image-src")) with
        | some s => acc.push s
        | none => acc
    imageAttrsList name acc kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

private def imageAttrsList (name : Option String) (acc : Array String) : List Node → Array String
  | [] => acc
  | k :: rest => imageAttrsList name (imageAttrsOne name acc k) rest

end

/-- Every image source a node carries, including failed conversion
placeholders whose source is evidence rather than a fetch URL. -/
def imgSrcsOne (acc : Array String) (node : Node) : Array String :=
  imageAttrsOne none acc node

/-- Every image source a tree carries, hidden or not, in page order. -/
def imgSrcsList (acc : Array String) (nodes : List Node) : Array String :=
  imageAttrsList none acc nodes

/-- Emit a document as its typed tree — head and body nodes — plus any
diagnostics the backend itself raises; `emit` renders it. The tree is the
page before serialization: what the cross-backend agreement census judges
against the PDF's `Layout.Out`, so a divergence is caught on structure, not
by parsing the rendering back. -/
private def emitTreeCore (cfg : Config) (doc : Doc) :
    Array Node × Array Node × Array Diag := Id.run do
  -- The page's view of the document: backend conditionals resolve here, at
  -- the backend's entry (`Ir.keepFor_covers` is why dropping cannot lose
  -- content), so every walk below — sectioning, the deck chrome, the
  -- landmark and anchor checks — sees only what this page carries.
  let doc := { doc with body := Ir.keepFor "html" doc.body }
  -- The locale resolves here, once, from the document: the furniture the
  -- walks below generate is worded in the document's language.
  let cfg := { cfg with locale := doc.info.locale }
  let mut diags : Array Diag := #[]
  if doc.head.isSome || doc.foot.isSome then
    diags := diags.push (Diag.of .W0007
      "running head/foot is paged-media furniture; omitted from HTML"
      (help := "body content reaches both backends: move the masthead there"))
  -- In the frame model a frame is a page and its logo is the frame's own
  -- furniture, shipped below (`attachLogo`), exactly as the footer is. In
  -- every other class the logo stays paged-media furniture with no HTML
  -- analogue, and the drop is named.
  if doc.docClass.record.model != .frame &&
      (doc.logo.isSome || doc.body.any (fun b => match b with
        | .logo c => !c.isEmpty
        | _ => false)) then
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
    let href := match cfg.favicon with
      | some (source, r) => if source == icon then r.uri else icon
      | none => icon
    head := head.push (Html.elem "link" #[] #[("rel", "icon"), ("href", href)])
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
  -- The shipped faces' rules ride exactly where the slot variables ride:
  -- a mode that emits no variables ships no rules, and the driver writes
  -- the captured programs only when it passed the set.
  let faceRules := match cfg.fonts with
    | some fs => fontCss fs
    | none => ""
  match cfg.css with
  | .own => head := head.push (Node.style (faceRules ++ baseCss cfg doc ++ "\n" ++ themeCss doc ++ styled))
  | .bulma =>
    -- Bind our tokens onto Bulma's own custom properties so a host page's
    -- theme and ours agree instead of fighting.
    head := head.push (Node.style (faceRules ++ ":root {\n" ++ tokenVars cfg doc ++ "\n" ++
      "    --bulma-primary: var(--primary, var(--accent, #1d4ed8));\n" ++
      "    --bulma-body-family: var(--font-body, inherit);\n" ++
      "}\n" ++ styled))
  | .none => unless styled.isEmpty do head := head.push (Node.style styled)
  -- The declared sheet comes after the inline styles: at equal specificity
  -- the later rule wins, so the document's own stylesheet can restyle the
  -- defaults instead of fighting them.
  if let some href := doc.output.stylesheet then
    head := head.push (match cfg.stylesheet with
      | some (source, css) => if source == href then Node.style css else
          Html.elem "link" #[] #[("rel", "stylesheet"), ("href", href)]
      | none => Html.elem "link" #[] #[("rel", "stylesheet"), ("href", href)])
  let bodyClass := match cfg.css with
    | .bulma => "content"
    | _ => ""
  let cfg := { cfg with styles := doc.styles
                        pal := doc.palette
                        tokens := doc.tokens
                        deck := doc.docClass.record.model == .frame
                        page := doc.page }
  -- The chrome footer: every frame section closes with the section in
  -- force and its own frame number, in the muted key at the scale's small
  -- step — the same declarations the PDF path reads. A `\framefoot` note
  -- takes the left slot for the frames that follow.
  let hasFrameFoot := doc.body.any fun b => match b with
    | .framefoot xs => !xs.isEmpty
    | _ => false
  let chromeFoot := doc.docClass.record.chrome && doc.foot.isNone &&
    (doc.chrome.hasFooter || hasFrameFoot)
  let (inner, sectionDiags) := if doc.docClass.record.model == .flow then
      sectionize cfg doc.body
    else if doc.docClass.record.model != .frame then
      (blockNodesInto cfg #[] doc.body.toList, #[])
    else Id.run do
      -- The one numbering: the same array the PDF path threads
      -- (`Ir.frameNumbers`, T2–T4). Content numbers come only from it;
      -- the local front-matter ordinals name HTML fragment addresses.
      let nums := doc.frameNumbers
      let mut total := doc.frameCount
      let mut done := 0
      let mut titlePages := 0
      let mut sectionPages := 0
      let mut curSection : Array Inline := #[]
      let mut frameFoot : Option (Array Inline) := none
      -- The body's `\logo` declarations, keyed by their position: the
      -- HTML half of the one logo-state sequence, resolved per frame
      -- through the same fold the PDF's furniture pass reads per page
      -- (`Ir.logoInForce`; `logo_frames_agree` is why the two keyings
      -- cannot disagree).
      let mut logoSpans : Array (Nat × Array Inline) := #[]
      let mut acc : Array Node := #[]
      let mut walkDiags : Array Diag := #[]
      -- Each assigned frame id with the plain title that holds it: the
      -- same uniqueness door the article's sections claim through.
      let mut taken : Std.HashMap String String := {}
      -- Each stage name claimed so far (`claimName`).
      let mut named : Std.HashSet String := {}
      -- The epoch state threads through the deck's top level exactly as
      -- through `blockNodesInto`.
      let mut cfg := cfg
      for h : i in [0:doc.body.size] do
        let b := doc.body[i]
        -- The part this block stands in, as the PDF walk reads it.
        total := doc.frameCountAt i
        if doc.frameRestart == some i then done := 0
        match b with
        | .setPalette p =>
          cfg := cfg.advancePalette p
        | .setTokens tk =>
          let style := joinStyles cfg.epochStyle (epochTokenStyle cfg.tokens tk)
          cfg := { cfg with tokens := tk, epochStyle := style }
        | .logo c =>
          -- A state change for this walk, not content (the PDF's
          -- `.setLogo` twin): the frames from here on carry `c`, an
          -- empty `c` clears.
          logoSpans := logoSpans.push (i, c)
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
        | .frame title standout _ _ _ =>
          let frameCfg := cfg.inFrame b
          let num := nums[i]?.getD none
          let numberAttrs := num.toArray.map fun n => ("data-frame-number", toString n)
          let label := match num with
            | some n =>
              if doc.frameRestart.any (· ≤ i) then s!"appendix-{n}" else toString n
            | none =>
              if titlePages == 0 then "titlepage" else s!"titlepage-{titlePages + 1}"
          if num.isNone then titlePages := titlePages + 1
          done := num.getD done
          -- One `section` per frame: the deck's steps reveal *in place*
          -- under the class-gated uncover rules (`deckStepCss`), so the
          -- HTML section count is the frame count — the PDF's page count
          -- less its per-step duplicates (`frames_sections` in Tests;
          -- both counts are projections of `Ir.frameSteps`).
          let (node, named2) := claimStageName named (blockNode frameCfg b)
          named := named2
          -- The frame's anchor: its title slug, unique among the deck's
          -- ids (`claimId`), so every slide is fragment-addressable — a
          -- deep link into the paged deck is `#its-title`. A repeated
          -- identical title numbers itself quietly; two different titles
          -- folding to one slug are named as W0327, as in the article.
          -- A stepless frame carries the anchor on its own section; a
          -- stepped frame's rides its *track*, not the sticky stage: a
          -- stage pinned at the scrollport edge reads as already in
          -- view, so a backward fragment jump onto it would not scroll,
          -- while the track's flow box always names the frame's place in
          -- the deck (CSS Scroll Snap 1 §6.2: fragment navigation snaps
          -- to the target's snap positions where it has them).
          let text := Ir.plainText title
          let base := slug title
          let base := if base.isEmpty then "slide" else base
          let (id, clash) := claimId taken base text
          if let some holder := clash then
            walkDiags := walkDiags.push (Diag.of .W0327
              s!"frames {holder.quote} and {text.quote} share the \
anchor '{base}'; the second becomes '{id}'"
              (help := some s!"an in-page link '#{base}' reaches only the \
first; retitle one frame, or link to '#{id}'"))
          taken := taken.insert id text
          -- The spacer anchors `<frame>-k`, claimed and built by the one
          -- walk whose count is a statement (`track_snaps_exact`); each
          -- spacer carries the `[data-snap]` door, so deep links and the
          -- script's snap list name the same boxes. A stepless frame has
          -- no spacer: its section is its own snap page.
          let steps := frameCfg.overlaySteps
          let (spacers, taken2, diags2) :=
            if steps > 1 then
              snapWalk id text label #[] taken walkDiags (stepList steps)
            else
              (#[], taken, walkDiags)
          taken := taken2
          walkDiags := diags2
          -- The frame's footer: the chrome band slots (`Ir.Chrome.frameFootBand`,
          -- the same function the PDF's final pass consumes, so the two
          -- backends resolve the same slots and can only diverge by
          -- rendering them; fixed positions from the declared side, paint
          -- order the declared priority, `z-index` carrying `rank`).
          let node := if chromeFoot then
              match doc.chrome.frameFootBand frameFoot curSection num total standout, node with
              | some band, .elem tag attrs kids =>
                let design := Design.ofPalette cfg.pal
                let look := design.frameFootLook standout
                let paint := if standout then
                    [s!"color: {cssColor look.fg};", s!"background: {cssColor design.standout.bg};"]
                  else []
                Node.elem tag attrs (kids.push (Html.elem "footer"
                  (band.map fun s => Html.elem "span" (inlines frameCfg s.content)
                    #[("class", match s.side with
                        | .left => "band-left"
                        | .right => "band-right"),
                      ("style", s!"z-index: {s.rank}")])
                  #[("class", "slide-foot size-" ++ Ir.footline.step),
                    ("style", String.intercalate " "
                      (paint ++ (look.bar.map fun ground =>
                        inkDecls design ground).getD []))]))
              | _, other => other
            else node
          -- The frame's logo: the state in force at this position, from
          -- the shared fold — one strip inside the section, so a stepped
          -- frame's sticky stage carries it on every snap page, as the
          -- PDF's furniture pass repeats it on every page of the frame.
          let node := attachLogo frameCfg node (Ir.logoInForce doc.logo logoSpans i)
          -- A stepped frame rides a `.slide-track`: the sticky stage
          -- over its snap spacers (`track_snaps_exact` counts them). The
          -- spacers — static boxes, never the sticky stage — carry the
          -- deck's snap areas through the `[data-snap]` door
          -- (`deckSnapDoor` says why no two areas share an offset), and
          -- the wrapper carries the frame's anchor and `--steps` for the
          -- uncover ranges. A stepless frame is its own snap page: the
          -- section carries the anchor, door and its only reveal state.
          let node := if steps > 1 then
              Html.elem "div" (#[node] ++ spacers)
                (#[("class", "slide-track"), ("style", s!"--steps: {steps}"),
                  ("id", id), ("data-slide-label", s!"{label}.1")] ++ numberAttrs)
            else match node with
              | .elem tag attrs kids =>
                Node.elem tag (attrs ++ #[("id", id), ("data-snap", ""), ("data-snapped", "1"),
                  ("data-slide-label", label)] ++ numberAttrs) kids
              | .text s => Node.text s
              | .style s => Node.style s
              | .script attrs s => Node.script attrs s
          acc := acc.push (withEpoch cfg.epochStyle cfg.epochGround node)
          cfg := cfg.afterFrame b
        | .section 1 starred num title =>
          curSection := title
          if (Design.ofPalette cfg.pal).sectionProgress.isSome then
            -- No clamp, as on the PDF path: `done ≤ total` by theorem
            -- over the numbering both walks read; a deck with no
            -- countable frame draws no bar.
            let kids := #[Html.elem "h2" (inlines cfg title)]
            let kids := if total == 0 then kids else
              kids.push (Html.elem "div"
                #[Html.elem "div" #[] #[("style", s!"width: {done * 100 / total}%")]]
                #[("class", "progress")])
            -- A section page is one snap page of the deck like any
            -- stepless frame: the section itself carries the
            -- `[data-snap]` door — and, being a page, the logo state in
            -- force, as the PDF furnishes every page.
            let name := claimName named (sectionPageName title)
            named := named.insert name
            acc := acc.push (withEpoch cfg.epochStyle cfg.epochGround
              (attachLogo cfg
                (Html.elem "section" kids
                  (#[("class", "section-page")] ++
                    stageAttrs cfg.deck name ++ #[("data-snap", ""),
                      ("data-slide-label", s!"section-{sectionPages}")]))
                (Ir.logoInForce doc.logo logoSpans i)))
            sectionPages := sectionPages + 1
          else
            acc := acc.push (withEpoch cfg.epochStyle cfg.epochGround
              (blockNode cfg (.section 1 starred num title)))
        | _ =>
          unless Ir.pageMarkerBlock b do acc := acc.push (withEpoch cfg.epochStyle cfg.epochGround (blockNode cfg b))
      return (acc, walkDiags)
  diags := diags ++ sectionDiags
  -- The endnotes: one section before the article end (W3C DPUB-ARIA 1.1
  -- doc-endnotes), one list item per note in flow order — the same
  -- `Ir.footnotesOf` flow the marks were numbered in — each carrying its
  -- body and a back-link to its mark (doc-backlink). No script: the
  -- mark/note pairing is two plain anchors, and W0326's target check
  -- holds both directions on the emitted tree.
  let notes := Ir.footnotesOf doc.body
  let inner := if notes.isEmpty then inner else
    inner.push (Html.elem "section"
      #[Html.elem "ol" (notes.map fun (num, content) =>
          let n := num.getD 0
          Html.elem "li"
            ((inlineNodesInto cfg #[] content.toList).push (Html.text " ")
              |>.push (Html.elem "a" #[Html.text "\u21a9"]
                #[("href", s!"#fnref{n}"), ("role", "doc-backlink"),
                  ("aria-label", "back to the text"), ("style", "color: inherit")]))
            #[("id", s!"fn{n}")]) #[]]
      #[("role", "doc-endnotes")])
  let mainAttrs := (if bodyClass.isEmpty then #[] else #[("class", bodyClass)]) ++
    #[("style", "container-type: inline-size")]
  let main := Html.elem "main" inner mainAttrs
  -- The headline band: the page's own <header> before <main> (the banner
  -- landmark — the HTML poster is a page, and the band is its header),
  -- title as the one h1, authors and institute as their own lines, the
  -- corner logos in the slots the stylesheet lays around the matter.
  let headerNode : Array Node := match doc.headline with
    | some hl =>
      let slot (c : Option (Array Ir.Inline)) : Array Html.Node :=
        match c with
        | some xs =>
          -- Decoration unless it holds a tab stop (`logoBox`), as the
          -- deck's logo strip is (`attachLogo`).
          #[logoBox "headline-logo" none (inlines cfg (logoDecoration xs)) (inlines cfg xs)]
        | none => #[]
      let line (cls : String) (xs : Array Ir.Inline) : Array Html.Node :=
        if xs.isEmpty then #[] else
          #[Html.elem "p" (inlineNodesInto cfg #[] xs.toList) #[("class", cls)]]
      let matter := #[Html.elem "h1" (inlineNodesInto cfg #[] hl.title.toList)] ++
        line "headline-author" hl.author ++
        line "headline-institute" hl.institute
      #[Html.elem "header"
        (slot doc.logoLeft ++
          #[Html.elem "div" matter #[("class", "headline-matter")]] ++
          slot doc.logoRight)
        #[("class", "headline")]]
    | none => #[]
  let mut body : Array Node := headerNode ++ #[main]
  -- The deck's own progress hairline uses the base bar. A section-only
  -- override cannot enable or recolour this separate indicator.
  if doc.docClass == .slides && (Design.ofDoc doc).progress.isSome then
    body := body.push (Html.elem "div" #[]
      #[("class", "deck-progress"), ("aria-hidden", "true")])
  -- The slides class's constant keyboard/uncover script: one raw-text
  -- node through the typed tree, gated on the class
  -- (`deck_script_gated`), its text the pinned constant
  -- (`deck_script_constant`).
  body := body ++ deckScriptNodes (doc.docClass == .slides)
  if let some tool := cfg.mathBoundary then
    body := body.push (Html.elem "script" #[]
      #[("data-math-boundary", tool), ("src", tool)])
  -- The landmark and anchor contracts, judged over the emitted tree.
  let facts := pageFactsList none {} body.toList
  -- premise: slideLabelChecks — these routes ship with the constant script;
  -- without it only DOM anchors are promised. A bare frame label aliases
  -- its first reveal, exactly as `deckScript` reads the emitted attributes.
  let routes := if facts.deck then
      facts.slideLabels.foldl (init := ({} : Std.HashMap String String)) fun a label =>
        let a := a.insert label label
        if label.endsWith ".1" then a.insert (label.dropEnd 2).toString label else a
    else {}
  for (id, stage) in facts.ids do
    if let some target := routes[id]? then
      if stage != some target then
        diags := diags.push (Diag.of .W0327
          s!"fragment '#{id}' names both a slide and an element anchor; \
slide navigation uses '#{target}'"
          (subject := some id)
          (help := some (match stage with
            | some label => s!"use '#{label}' to reach the slide holding that anchor"
            | none => "rename the anchor so it differs from a slide label")))
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
    unless isTop || facts.ids.any (·.1 == frag) || routes.contains frag ||
        checked.contains fref do
      checked := checked.push fref
      diags := diags.push (Diag.of .W0326
        s!"in-page link '{fref}' has no target anchor on this page"
        (help := some (if facts.ids.isEmpty then
            "this page has no anchors: a level-1 \\section title becomes \
one in the article class"
          else s!"anchors on this page: \
{String.intercalate ", " (facts.ids.toList.map (fun kv => "#" ++ kv.1))}")))
  -- Every <img> this page ships is one a browser decodes, or its loss is
  -- named: judged over the emitted tree, so an image the page never links
  -- is never named, and one under a hidden strip still is.
  for k in undecodableIndices cfg.imgs
      (imageAttrsList (some "data-image-index") #[] body.toList) do
    if let some en := cfg.imgs.get? k then
      diags := diags.push (undecodableDiag (resolvedSrc en) en.webError (some k))
  return (head, body, diags)

/-- Normalize the shared IR at the public entry, before any backend walk. -/
def emitTree (cfg : Config) (doc : Doc) :
    Array Node × Array Node × Array Diag :=
  let coverage := cfg.fonts.map (·.mathAlphabets) |>.getD {}
  let family := cfg.fonts.bind (fun fs => fs.math.bind (fs.fonts[·]?))
    |>.map (·.family) |>.getD "math face"
  let (doc, diags) := Ir.resolveMathAlphas coverage family doc
  -- Rendering reads the canonical source-free shape: locations must not
  -- hide a display formula, a description label, or a flex-row separator
  -- from the backend's structural classifiers. The caller's spanned IR
  -- remains available for diagnostics.
  let (head, body, backendDiags) := emitTreeCore cfg (Ir.eraseLocations doc)
  (head, body, diags ++ backendDiags)

/-- Both tree projections read the IR resolver's one fixed point. -/
theorem emitTree_resolve_agree (cfg : Config) (doc : Doc) :
    let coverage := cfg.fonts.map (·.mathAlphabets) |>.getD {}
    let family := cfg.fonts.bind (fun fs => fs.math.bind (fs.fonts[·]?))
      |>.map (·.family) |>.getD "math face"
    let resolved := (Ir.resolveMathAlphas coverage family doc).1
    (emitTree cfg resolved).1 = (emitTree cfg doc).1 ∧
      (emitTree cfg resolved).2.1 = (emitTree cfg doc).2.1 := by
  dsimp only
  simp [emitTree, Ir.resolveMathAlphas_fixed_point]

/-- Emit a document. Returns the file and any diagnostics the backend itself
raises — running content is the notable one: page furniture cannot be honoured
in a continuous document, and dropping it silently would be the kind of quiet
failure this engine exists to avoid. -/
def emit (cfg : Config) (doc : Doc) : String × Array Diag :=
  let (head, body, diags) := emitTree cfg doc
  -- <html lang> is the document's declared language (WCAG 2.2 SC 3.1.1;
  -- a hard-coded "en" on a French page is worse than absent — an
  -- actively wrong declaration). The tag ships as declared even when no
  -- locale record backs it: the artifact's declaration and the engine's
  -- data are different questions.
  (Html.document (doc.info.language.getD "en") head body, diags)

/-- Exact captured resource projection available to this artifact. -/
def resources (cfg : Config) : Array HtmlResource.Embedded :=
  (cfg.fonts.map fontResources).getD #[] ++ imageResources cfg.imgs ++
    (cfg.favicon.map fun (_, r) => #[r]).getD #[]

abbrev ClosedPage := HtmlResource.ClosedPage deckScript

/-- The publication entry checks the actual emitted tree. SVG evidence
must come from the driver's parsed-XML validator on these exact bytes. -/
def emitClosed (cfg : Config) (doc : Doc) (svgChecked : Array ByteArray) :
    Except String ClosedPage × Array Diag :=
  let (head, body, diags) := emitTree cfg doc
  -- premise: Tests.htmlContainedChecks — Bulma requires a captured framework stylesheet.
  let page := if cfg.css == .bulma && doc.output.stylesheet.isNone then
      .error "Bulma HTML requires a captured local framework stylesheet"
    else HtmlResource.close (resources cfg) svgChecked deckScript
      (doc.info.language.getD "en") head body
  (page, diags)

/-- Artifact-specific closure, enforced before a page can be published:
the checked page is the emitter's actual serialization and every projected
rendering reference resolves against its captured resources. -/
theorem emitClosed_covers (cfg : Config) (doc : Doc) (svgChecked : Array ByteArray)
    {page : ClosedPage} (h : (emitClosed cfg doc svgChecked).1 = .ok page) :
    page.render = (emit cfg doc).1 ∧
      ∀ r ∈ HtmlResource.requests (emitTree cfg doc).1 (emitTree cfg doc).2.1,
        HtmlResource.resolves (resources cfg) svgChecked deckScript r = true := by
  dsimp only [emitClosed] at h
  split at h
  · contradiction
  · exact HtmlResource.close_covers (resources cfg) svgChecked deckScript
      (doc.info.language.getD "en") _ _ h

/-- Every emitted page declares a language: the artifact is
`Html.document` over the document's declared tag, the engine's `en`
assumption standing in when it names none — `emit`'s one construction
site, so with `Html.document_declares_lang` the root element always
carries `lang` (WCAG 2.2 SC 3.1.1, technique H57). Whether the tag
matches the text is the document's own truth; the engine judges the
declaration, never the prose. -/
theorem emit_lang_declared (cfg : Config) (doc : Doc) :
    ∃ head body,
      (emit cfg doc).1 = Html.document (doc.info.language.getD "en") head body := by
  rcases h : emitTree cfg doc with ⟨head, body, ds⟩
  exact ⟨head, body, by simp [emit, h]⟩

/-! ## What assistive technology is handed

The static half of the page's accessibility oracle: facts a checker such as
axe reports from a browser, read here off the typed tree the page
serializes, so they can gate with no browser. axe over the rendered corpus
is the cross-check, never the gate. -/

/-- Does an element carry an accessible name in its own markup: a
non-blank `aria-labelledby` or `aria-label` (accname 1.2, steps 2B and 2C),
or — for SVG — a `<title>` child with text (SVG-AAM 1.0, §8.1)? -/
def carriesName : Node → Bool
  | .elem _ attrs kids =>
    attrs.any (fun kv => (kv.1 == "aria-label" || kv.1 == "aria-labelledby") &&
        nonBlank kv.2) ||
      kids.any fun k => match k with
        | .elem "title" _ ts => ts.any fun t => match t with
          | .text s => nonBlank s
          | _ => false
        | _ => false
  | .text _ => false
  | .style _ => false
  | .script _ _ => false

/-- The page facts assistive technology depends on, as counts over the
emitted tree. Each `…Unnamed`/`…Unreachable` count is a deficit: a node
counted in its total that AT cannot name or reach. A subtree under
`aria-hidden="true"` is not handed to AT at all, so nothing in it counts —
except a tab stop, which the keyboard still reaches (`hiddenTabStops`). -/
structure A11yFacts where
  /-- `<h1>` elements: a page's outline has exactly one top (axe's
  `page-has-heading-one` asks for at least one). -/
  h1s : Nat := 0
  /-- Tab stops (`tabbable`) under `aria-hidden="true"`, outside a `hidden`
  subtree: a keyboard stop assistive technology is told is not there —
  axe's `aria-hidden-focus`, SC 4.1.2. -/
  hiddenTabStops : Nat := 0
  imgs : Nat := 0
  /-- `<img>` with no non-blank `alt` and no declared decorative role
  (`presentation`/`none`), or a non-SVG `role="img"` with no accessible
  name: WCAG 2.2 SC 1.1.1. SVG has its own count below. -/
  imgsUnnamed : Nat := 0
  svgs : Nat := 0
  /-- `<svg>` that carries no accessible name (`carriesName`): axe's
  `svg-img-alt`, SC 1.1.1. -/
  svgsUnnamed : Nat := 0
  /-- Elements the engine's own stylesheet makes scroll containers
  (`declaresScroll`). -/
  scrolls : Nat := 0
  /-- Scroll containers a keyboard cannot reach — no `tabindex="0"` — or, for
  a deck stage (a named region once focusable), that carry no name: axe's
  `scrollable-region-focusable`, SC 2.1.1. -/
  scrollsUnreachable : Nat := 0
  deriving Repr, BEq, Inhabited

/-- The class tokens of an attribute list. -/
def classTokens (attrs : Array (String × String)) : List String :=
  ((attrOf? attrs "class").getD "").splitOn " " |>.filter (!·.isEmpty)

/-- The elements the engine's own stylesheet declares scroll containers
(`overflow-x`/`overflow-y: auto`): every `pre` (`baseCss`), and on the paged
deck every stage (`deckStageRule`: `section.slide, section.section-page`).
Only the `own` stylesheet declares either — under `bulma` or `none` the host
sheet decides, and the engine claims nothing. -/
def declaresScroll (own deck : Bool) (tag : String) (attrs : Array (String × String)) :
    Bool :=
  own && (tag == "pre" ||
    (deck && tag == "section" &&
      (classTokens attrs).any (fun c => c == "slide" || c == "section-page")))

/-- Can a keyboard reach a scroll container, and assistive technology say
what it is: `tabindex="0"`, and a name — except on a code block, whose
generic role takes none (WAI-ARIA 1.2 §5.2.8.6, naming prohibited). -/
def scrollReachable : Node → Bool
  | n@(.elem tag attrs _) =>
    attrOf? attrs "tabindex" == some "0" && (tag == "pre" || carriesName n)
  | .text _ => false
  | .style _ => false
  | .script _ _ => false

/-- One element's own contribution to the facts, its children aside. -/
def a11yElem (own deck : Bool) (tag : String) (attrs : Array (String × String))
    (kids : Array Node) (acc : A11yFacts) : A11yFacts :=
  let decorative := match attrOf? attrs "role" with
    | some "presentation" | some "none" => true
    | _ => false
  let acc := if tag == "h1" then { acc with h1s := acc.h1s + 1 } else acc
  let acc := if tag == "img" || (tag != "svg" && attrOf? attrs "role" == some "img") then
      let named := if tag == "img" then nonBlank ((attrOf? attrs "alt").getD "")
        else carriesName (.elem tag attrs kids)
      { acc with imgs := acc.imgs + 1
                 imgsUnnamed := acc.imgsUnnamed + (if named || decorative then 0 else 1) }
    else acc
  let acc := if tag == "svg" then
      { acc with svgs := acc.svgs + 1
                 svgsUnnamed := acc.svgsUnnamed +
                   (if carriesName (.elem tag attrs kids) then 0 else 1) }
    else acc
  if declaresScroll own deck tag attrs then
    { acc with scrolls := acc.scrolls + 1
               scrollsUnreachable := acc.scrollsUnreachable +
                 (if scrollReachable (.elem tag attrs kids) then 0 else 1) }
  else acc

mutual

/-- The facts of one node onto `acc`; `hidden` is whether an ancestor took
the subtree out of the accessibility tree, `inert` whether one took it out
of rendering (the `hidden` attribute), where nothing takes focus. The list
companion keeps the recursion structural. -/
def a11yOne (own deck hidden inert : Bool) (acc : A11yFacts) : Node → A11yFacts
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    let hid := hidden || attrOf? attrs "aria-hidden" == some "true"
    let inert := inert || (attrOf? attrs "hidden").isSome
    let acc := if !hid then a11yElem own deck tag attrs kids acc
      else if !inert && tabbable tag attrs then
        { acc with hiddenTabStops := acc.hiddenTabStops + 1 }
      else acc
    a11yList own deck hid inert acc kids.toList

def a11yList (own deck hidden inert : Bool) (acc : A11yFacts) : List Node → A11yFacts
  | [] => acc
  | k :: rest => a11yList own deck hidden inert (a11yOne own deck hidden inert acc k) rest

end

/-- The facts of a page body, under the stylesheet mode and page model it
was emitted for. -/
def a11yFacts (own deck : Bool) (body : Array Node) : A11yFacts :=
  a11yList own deck false false {} body.toList

/-- The four pairings one variant of the stylesheet creates, as data: body
text on the page, marker text on the page, code text on its tint, the focus
indicator on the page — each with the ratio it owes (SC 1.4.3, SC 1.4.11).
`Contrast.ThemeColors.contractHolds` is exactly their conjunction
(`themePairs_contract`), so a count over this list judges what that
contract judges. -/
def themePairs (t : Contrast.ThemeColors) : List (String × Ir.Color × Ir.Color × Nat) :=
  [("text", t.ink, t.surface, Contrast.aaText), ("muted", t.muted, t.surface, Contrast.aaText),
   ("code", t.ink, t.tint, Contrast.aaText), ("accent", t.accent, t.surface, Contrast.aaNonText)]

theorem themePairs_contract (t : Contrast.ThemeColors) :
    t.contractHolds =
      (themePairs t).all fun p => decide (Contrast.contrastMilli p.2.1 p.2.2.1 ≥ p.2.2.2) := by
  simp [Contrast.ThemeColors.contractHolds, themePairs, Bool.and_assoc]

/-- The colours a page's own stylesheet paints in one colour scheme, read
as the cascade resolves them. A palette entry named after a token (`ink`,
`muted`, …) is emitted after both scheme blocks at the same `:root`
specificity (`tokenVars`), so it holds in both schemes; an undeclared
token keeps the scheme's own. The text is the design's declared ink when it
declares one (`themeCss`: `body { color: var(--fg) }`), and the ground
under it is the declared page (`body { background: var(--bg) }`), both read
off `Design.ofDoc`, their one resolving site. The paged deck's stage paints
the same declared page (`deckStageRule` reads `stageGround`, the declared
`bg` before the scheme's surface), so every class judges one pair: until it
did, the stage painted `var(--surface)` whatever the document declared, and
a theme's declared ink stood on the dark scheme's surface. Under `bulma` or
`none` the engine ships no colour of its own and claims nothing;
`schemeFailures` counts none. -/
def schemeColors (doc : Doc) (base : Contrast.ThemeColors) : Contrast.ThemeColors :=
  let tok (n : String) (d : Ir.Color) : Ir.Color := (doc.palette.find? n).getD d
  let d := Design.ofDoc doc
  let surface := tok "surface" base.surface
  let text := if d.fgDeclared then d.fg else tok "ink" base.ink
  let page := if d.bgDeclared then d.bg else surface
  { ink := text
    surface := page
    muted := tok "muted" base.muted
    accent := tok "accent" base.accent
    tint := tok "tint" base.tint
    rule := tok "rule" base.rule }

/-- The pairings a page fails, in each colour scheme it ships: `themePairs`
over `schemeColors` in light, and in dark where the page ships the dark
variant (`dualScheme`, over the page's own loaded images) — a single-scheme
page shows its light colours to a dark-mode reader, one judgement, never
counted twice. A page under a stylesheet the engine does not own fails
none, because the engine paints none of them. -/
def schemeFailures (own : Bool) (imgs : Image.Store) (doc : Doc) : List (String × String) :=
  if !own then [] else
    ([("light", Contrast.light)] ++
        (if dualScheme imgs doc then [("dark", Contrast.dark)] else [])).flatMap
      fun (scheme, base) =>
      ((themePairs (schemeColors doc base)).filter fun p =>
          Contrast.contrastMilli p.2.1 p.2.2.1 < p.2.2.2).map fun p => (scheme, p.1)

/-- **Every picture the backend emits is named or hidden** (`_contract`):
the `.picture` arm — the one site that builds an `<svg>` — ships an `svg`
element that is out of the accessibility tree exactly when the picture is
decoration, and otherwise carries a non-empty accessible name in its own
markup, whatever the picture and configuration. `htmlA11yChecks` holds the
whole-page form over the shipped corpus. -/
theorem picture_svg_named_contract (cfg : Config) (pic : Ir.Pic.Picture) :
    (blockNode cfg (.picture pic)).tag? = some "svg" ∧
      (pic.alternative ≠ .decorative → carriesName (blockNode cfg (.picture pic)) = true) := by
  rcases h : pictureBoxOf cfg pic with ⟨⟨x0, y0⟩, ⟨x1, y1⟩⟩
  refine ⟨by simp [blockNode, pictureSvg, h, Html.elem, Node.tag?], fun hd => ?_⟩
  cases ha : pic.alternative with
  | decorative => exact absurd ha hd
  | described t =>
    simp [blockNode, pictureSvg, h, Html.elem, carriesName, pictureRole, pictureAltAttrs, ha,
      firstNonBlank_contract _ _ (figureWord_contract cfg.locale)]
  | undeclared =>
    simp [blockNode, pictureSvg, h, Html.elem, carriesName, pictureRole, pictureAltAttrs, ha,
      figureWord_contract]

/-- **Every deck stage the backend emits is reachable** (`_contract`): on
the paged deck the frame arm's `section` — a scroll container by
`deckStageRule` — carries `tabindex="0"` and a non-blank name, whatever the
frame. A fact of the artifact: which boxes scroll is the stylesheet's
decision, not the IR's. `htmlA11yChecks` holds it, with the section pages
and code blocks, over every shipped corpus page. -/
theorem frame_stage_reachable_contract (cfg : Config) (hd : cfg.deck = true)
    (title : Array Inline) (standout : Bool) (valign : VAlign) (br : Bool)
    (body : Array Block) :
    scrollReachable (blockNode cfg (.frame title standout valign br body)) = true := by
  simp [blockNode, Config.inFrame, hd, Html.elem, scrollReachable, carriesName, attrOf?, stageAttrs,
    frameName_contract]

end LeanTex.Core.HtmlDoc
