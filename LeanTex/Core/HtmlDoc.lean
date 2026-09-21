import LeanTex.Core.Html
import LeanTex.Core.MathMl
import LeanTex.Core.Ir
import LeanTex.Core.Dim
import LeanTex.Core.Contrast
import LeanTex.Core.Font

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
  /-- The token state in force, same door (`.setTokens`). -/
  tokens : Ir.Tokens := {}
  /-- Whether the emitted page is the paged deck (the slides class's frame
  model): the frame arm then realizes its declared vertical distribution
  with flex spacers, which every other class's flow has no use for. -/
  deck : Bool := false
  /-- The document's page geometry, from the document at `emitTree`'s
  entry: the deck's image sizing reads the stage and its margins to state
  every dimension as a share of the stage (`deckStageMilli`), never a
  print length on a screen. -/
  page : Ir.PageSpec := {}
  /-- The accumulated custom-property redefinitions the siblings from here
  on carry on their own style attribute. Properties on an element inherit
  into it, so styling each following sibling realizes "from here on"
  without a wrapper element — a wrapper would break the `* + *` sibling
  adjacency the rhythm gap rules key on. -/
  epochStyle : String := ""
  /-- The document's resolved faces, from the driver — the same `FontSet`
  the PDF embeds from — when the artifact ships them: one `@font-face` per
  face, files written beside the page. `none` (a document that declared
  its `css =` story owns fonts itself, and so does a caller with no font
  environment) keeps the name-only stacks. -/
  fonts : Option Font.FontSet := none
  /-- The sibling directory the driver writes the shipped faces into,
  relative to the page — what every `src: url(...)` references. -/
  fontsDir : String := "fonts"

def cssColor (c : Color) : String :=
  let r := Color.hexByte c.r false
  let g := Color.hexByte c.g false
  let b := Color.hexByte c.b false
  "#" ++ r ++ g ++ b

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

/-- Every class value the engine itself puts on an element, as tokens (a
multi-class value like `"slide standout"` is listed split). Maintained by
grep over this file — `("class", "…")` literals, the `rowClass`/`cls`
builders, `styleClass`, and the `size-` names `styleClass` derives from
`Ir.sizeScale`; `roleClass_engine_disjoint` is the reason the list exists. -/
def engineClasses : List String :=
  ["abstract", "b", "i", "mono", "sc", "em", "sans", "normal", "rm", "md", "up",
   "section-number", "equation", "eqnum",
   "band-left", "band-right", "booktabs", "bt-cmid", "bt-heavy-above",
   "bt-light-above", "centered", "ragged", "column", "columns", "content",
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

/-- What one style wrapper says in a `::marker` rule, when it says anything
(CSS Pseudo-Elements 4 §4.1: all font properties apply). The bold weight is
600, the same weight the base stylesheet's level-2 dash carries. An unknown
size name resolves to nothing, which makes the whole marker inexpressible
rather than silently unsized. -/
private def markerStyleDecls (scale : List (String × Nat)) :
    Style → Option (Array String)
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
  -- a language changes no marker styling; the wrapper is expressible as
  -- nothing rather than inexpressible
  | .lang _ => some #[]

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
  | .role _ _ :: _ => none
  | .link _ _ :: _ => none
  | .underline _ :: _ => none
  | .fill :: _ => none
  | .strut _ :: _ => none
  | .pageNumber :: _ => none
  | .pageCount :: _ => none
  | .linebreak _ :: _ => none
  | .step _ _ _ :: _ => none
  | .image _ _ _ :: _ => none
  -- a `content` string cannot carry the icon's accessible name, so an icon
  -- marker is inexpressible here and diagnosed (W0331), never defaulted
  | .icon _ _ :: _ => none
  -- an anchor or a reference in a marker has no ::marker expression
  | .label _ :: _ => none
  | .ref _ _ _ _ :: _ => none
  -- a citation resolves to links, which no ::marker can carry
  | .cite _ _ :: _ => none
  -- a footnote's mark is a link, which no ::marker can carry
  | .footnote _ _ :: _ => none

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
    match markerStyleDecls scale st with
    | some ds => markerCssList scale (decls ++ ds) body.toList
    | _ => none
  | .colored c name body =>
    markerCssList scale (decls.push (markerColorDecl c name)) body.toList
  -- a role's class has no ::marker expression; the content passes through,
  -- as it does on the PDF marker path
  | .role _ body => markerCssList scale decls body.toList
  | .math _ _ => none
  | .formula _ _ _ => none
  | .link _ _ => none
  | .underline _ => none
  | .fill => none
  | .strut _ => none
  | .pageNumber => none
  | .pageCount => none
  | .linebreak _ => none
  | .step _ _ _ => none
  | .image _ _ _ => none
  | .icon _ _ => none
  | .label _ => none
  | .ref _ _ _ _ => none
  | .cite _ _ => none
  | .footnote _ _ => none

def markerCssList (scale : List (String × Nat)) (decls : Array String) :
    List Inline → Option MarkerCss
  | [x] => markerCssOne scale decls x
  | xs => (markerTextInto "" xs).map fun t => { text := t, decls := decls }

end

def markerCss? (m : Array Inline)
    (scale : List (String × Nat) := Ir.sizeScale) : Option MarkerCss :=
  markerCssList scale #[] m.toList

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
  | .math _ _ | .formula _ _ _ | .link _ _ | .underline _ | .fill
  | .strut _ | .pageNumber | .pageCount | .linebreak _ | .step _ _ _
  | .image _ _ _ | .icon _ _ | .label _ | .ref _ _ _ _ =>
    simp [markerCssOne] at h

theorem markerCssList_text (scale : List (String × Nat)) (decls : Array String)
    (xs : List Inline)
    (r : MarkerCss) (h : markerCssList scale decls xs = some r) :
    r.text = Ir.plainTextList xs := by
  match xs with
  | [x] =>
    rw [markerCssList] at h
    simp [Ir.plainTextList, markerCssOne_text scale decls x r h]
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
    (scale : List (String × Nat) := Ir.sizeScale)
    (h : markerCss? m scale = some r) : r.text = Ir.plainText m :=
  Ir.plainText.eq_def m ▸ markerCssList_text scale #[] m.toList r h

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
    let own := if decls.isEmpty then "" else s!"{tag} \{ {String.intercalate " " decls} }\n"
    -- Bound first: appending a call's result directly is the shape the
    -- cost gate rejects; a name makes the one-off append visible as one.
    let liCss := String.join liDecls
    let interCss := String.join interDecls
    css := css ++ own ++ liCss ++ interCss
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
  [("p", "peer"), ("ul", "peer"), ("ol", "peer"), ("pre", "peer"),
   ("blockquote", "peer"), ("table.booktabs", "peer"),
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
`--floatsep` token), so its row is its own conjunct. -/
theorem blockGap_kinds_covers :
    (blockGapKinds.all fun e => 0 < gapK e.2) = true ∧ 0 < gapK "float" ∧
    0 < gapK "caption" := by decide

/-- The gap rules, one adjacent-sibling rule per block element, each inside
`:where()`: the base sheet's defaults carry zero specificity, so any
consumer rule — a declared `\style` (emitted on the bare element selector)
or a reader stylesheet that owns a container's spacing with `gap` — wins
without a specificity fight, which is the HTML backend's override
contract. The float's gaps keep their token (`--floatsep`, the same one
the PDF path reads), and the float adds the one pair rule
(`figure.float + *`): the gap below a float is the float's to declare, as
the PDF walk's `addvspace` takes the larger of the float's gap and the
next element's own — the pair rule stands later in the sheet, its value
winning the boundary while the neighbour's own margin stays zero, so
single ownership holds there too. -/
def blockGapCss : String :=
  String.join (blockGapKinds.map fun (sel, kind) =>
    s!":where(* + {sel}) \{ margin-top: {quantaRem (gapK kind)}; }\n") ++
  s!":where(* + figure.float) \{ margin-top: var(--floatsep, {quantaRem (gapK "float")}); }\n" ++
  s!":where(figure.float + *) \{ margin-top: var(--floatsep, {quantaRem (gapK "float")}); }\n" ++
  -- The heading's band below is the heading's own (`blockGapKinds`): the
  -- follower's default top margin is suppressed, standing last so it wins
  -- every zero-specificity default above, and the heading rule's
  -- margin-bottom is the boundary's one emitter.
  ":where(h1, h2, h3, h4) + * { margin-top: 0; }\n"

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
    -- The bar owns no space below: the frame body's first block pays its
    -- own gap (`blockGapCss`), one emitter per boundary.
    s!"  margin: -{slidePadV} -{slidePadH} 0; padding: {quantaRem 1} {slidePadH};\n" ++
    s!"  border-radius: {slideRadiusPx - slideBorderPx}px {slideRadiusPx - slideBorderPx}px 0 0; }\n" ++
    "section.slide > header h2 { color: inherit; }\n" ++
    -- On the paged deck the slide is the viewport, cornerless: the bar
    -- squares off with it and bleeds through the safe-area padding,
    -- negating exactly the token the slide pads by.
    (if doc.docClass == .slides then
      "@media screen { section.slide > header { border-radius: 0;\n" ++
      s!"  margin: calc(-1 * {safeareaVar}) calc(-1 * {safeareaVar}) 0;\n" ++
      s!"  padding: {quantaRem 1} {safeareaVar}; } }\n"
     else "") else "") ++
  -- The headline band: the poster page's <header>, a flex row of the two
  -- corner-logo slots around the title matter. Colours are the same
  -- frametitle tokens the PDF band resolves (one resolving site per
  -- backend, one declared pair), gated on the pair as the slide bar's
  -- rule is; the matter's alignment is the `titlepage` style's declared
  -- token (undeclared centres, `\@maketitle`'s own rule).
  (match doc.headline with
   | some _ =>
     let tpsAlign := ((doc.styles.find? "titlepage").bind (·.align)).getD "center"
     s!"body > header.headline \{ display: flex; align-items: center;
" ++
     s!"  gap: {quantaRem 2}; padding: {quantaRem 2} {quantaRem 3}; }
" ++
     s!"body > header.headline .headline-matter \{ flex: 1; text-align: " ++
     (if tpsAlign == "left" then "left" else "center") ++ "; }
" ++
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
  -- A role names a hue; the contract chooses its lightness on each ground
  -- (`Contrast.realize`, the same solver `Contrast.realizeDoc` ships the
  -- PDF's runs through): on the frame-title bar and the standout
  -- inversion a content colour that fails re-realizes, and the scope
  -- carries its own value of the token, so a run's var(--alert) resolves
  -- to the bar's realization rather than the page's. Emitted only where
  -- the realized value differs — a bundle whose pairs pass emits nothing
  -- (realizedChecks in Tests.lean pins the backend agreement).
  (String.join ((
    [("section.slide > header", d.frametitle.map (·.bg)),
     ("section.slide.standout", some d.standout.bg)] :
      List (String × Option Ir.Color)).filterMap
    fun (sel, groundOf) => groundOf.bind fun ground =>
      let vars := String.join ((["alert", "example"] : List String).filterMap fun role =>
        (doc.palette.find? role).bind fun c =>
          if doc.palette.decorative.contains role then none
          else (Contrast.realize Contrast.aaText ground c).bind fun c' =>
            if c' == c then none else some s!"  --{role}: {cssColor c'};\n")
      if vars.isEmpty then none else some (sel ++ " {\n" ++ vars ++ "}\n"))) ++
  (if d.progress.isSome then
    s!"section.section-page \{ text-align: center; padding: {quantaRem 3} 0;\n" ++
    "  break-inside: avoid; }\n" ++
    "section.section-page h2 { display: inline-block; text-align: left;\n" ++
    "  min-width: 60%; margin: 0; }\n" ++
    -- The height reads the same token the PDF path reads
    -- (`progressheight`), with the same fallback — moloch's own 1pt
    -- (beamerouterthememoloch.dtx) — one resolving site per backend, one
    -- declared value.
    ".progress { background: var(--progressbg, var(--rule));\n" ++
    "  height: var(--progressheight, 1pt);\n" ++
    s!"  width: 60%; margin: {quantaRem 1} auto 0; }\n" ++
    ".progress > div { background: var(--progressfg); height: 100%; }\n" ++
    -- The paged deck's own progress: a hairline across the viewport top,
    -- scaled by how far the reader has paged through the deck —
    -- declarative where the platform has scroll-driven animations
    -- (`scroll(root x)`, Scroll-driven Animations 1: the axis is the
    -- deck's own), the same tokens as the section-page bar, and the same
    -- floor as `revealCss`: without the feature the rules never apply and
    -- the deck is fully navigable without its bar. Screen only: a printed
    -- handout has no scroll to report.
    (if doc.docClass == .slides then
      "@media screen { @supports (animation-timeline: scroll()) {\n" ++
      ".deck-progress { position: fixed; top: 0; left: 0; width: 100%;\n" ++
      "  height: var(--progressheight, 1pt); background: var(--progressfg);\n" ++
      "  transform-origin: 0 50%;\n" ++
      "  animation: ltx-deck-progress linear both;\n" ++
      "  animation-timeline: scroll(root x); }\n" ++
      "@keyframes ltx-deck-progress { from { transform: scaleX(0) } \
to { transform: scaleX(1) } }\n" ++
      "} }\n"
     else "") else "") ++
  -- The chrome footer: colour from the muted key, size from the shared
  -- scale (`size-small` on the element), positions fixed by the declared
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
    s!"  min-height: 1lh; margin-top: {quantaRem 2}; color: var(--muted); }\n" ++
    "footer.slide-foot > .band-left { position: absolute; left: 0;\n" ++
    "  white-space: nowrap; }\n" ++
    "footer.slide-foot > .band-right { position: absolute; right: 0;\n" ++
    "  white-space: nowrap; }\n" else "")

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
  simp only [cssColor, Color.hexByte, Bool.false_eq_true, ite_false,
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

/-- Every `src:` the styling names is a file the driver is asked to write:
rules and requests are projections of one enumeration, so the page cannot
reference a face whose bytes were never requested. -/
theorem shipFaces_src_shipped (fs : Font.FontSet) :
    ∀ ff ∈ shipFaces fs, ∃ a ∈ fontAssets fs, a.file = ff.file := by
  intro ff hff
  simp only [shipFaces, Array.mem_flatMap] at hff
  obtain ⟨i, hi, hmem⟩ := hff
  simp only [Array.mem_map, List.mem_toArray] at hmem
  obtain ⟨fam, _, rfl⟩ := hmem
  refine ⟨{ file := fontFileName i (fs.get i), data := (fs.get i).data }, ?_, rfl⟩
  simp only [fontAssets, Array.mem_map]
  exact ⟨i, hi, rfl⟩

def fontFaceRule (dir : String) (ff : FontFace) : String :=
  s!"@font-face \{ font-family: \"{ff.family}\"; font-weight: {ff.weight}; " ++
  s!"font-style: {if ff.italic then "italic" else "normal"}; " ++
  s!"src: url(\"{dir}/{ff.file}\") format(\"{ff.format}\"); }\n"

/-- The `@font-face` block, one rule per `shipFaces` entry. -/
def fontFaceCss (dir : String) (fs : Font.FontSet) : String :=
  String.join ((shipFaces fs).toList.map (fontFaceRule dir))

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
def fontCss (dir : String) (fs : Font.FontSet) : String :=
  fontFaceCss dir fs ++
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
`deck_text_path_free` — so a new rule is
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
  list is the data (`fallback_uncovers_every_step` reads it), the
  template renders it. -/
  | stepAlts (js : List Nat)
  deriving Repr, DecidableEq

/-- The literal syntax a chunk renders, ordinals excluded. -/
def SelChunk.lits : SelChunk → List String
  | .lit s => [s]
  | .num _ => []
  | .stepAlts _ => [".step[data-step=\"", "\"], "]

def SelChunk.render : SelChunk → String
  | .lit s => s
  | .num n => toString n
  | .stepAlts js =>
    String.intercalate ", " (js.map fun j => s!".step[data-step=\"{j}\"]")

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
§12.1), or the printed handout. -/
inductive Part where
  | screen
  | reduce
  | print
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

/-- The deck stylesheet from its typed rules: the screen partition with
its gates, then the reduced-motion partition *after* the blocks it
reverts (equal specificity, source order decides — CSS Cascade 5 §6.4),
then the print partition. Every rule is emitted exactly once, in its
declared partition and gate; the Tests deck block pins the declaration
multiset against the typed set. -/
def emitDeckRules (rules : List DeckRule) : String :=
  let part (p : Part) := rules.filter (fun r => r.part == p)
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
      ("left", safeareaVar), ("right", safeareaVar), ("display", "flex")] }

/-- Every frame fills the viewport as one opaque column of the row:
`100vw` wide (exactly the scrollport — the root clips y, so no scrollbar
narrows the viewport under it), one stage tall, `background:
var(--surface)` unconditionally — opaque on every path, the user's own
rule — and content that spills the stage stays reachable through the
frame's own scroll (`overflow-y: auto`; the scrollbar is the visible
control, the honest floor). `position: relative` anchors the stage's own
furniture (`deckLogoRule`); in a stepped track the sticky override
(`stepStageRule`, higher specificity) is a positioned box already. -/
def deckStageRule : DeckRule :=
  { selector := [.lit "section.slide, section.section-page"]
    decls := [("width", "100vw"), ("flex", "0 0 100vw"),
      ("height", "100dvh"), ("overflow-y", "auto"),
      ("background", "var(--surface)"), ("display", "flex"),
      ("flex-direction", "column"), ("padding", safeareaVar),
      ("position", "relative")] }

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
    { selector := [.lit "body"], decls := [("padding", "0")] },
    { selector := [.lit "main"]
      decls := [("max-width", "none"), ("margin", "0"), ("display", "flex"),
        ("align-items", "flex-start"), ("font-size", bodyVh)] },
    deckStageRule,
    deckSnapDoor,
    deckLogoRule,
    { selector := [.lit "section.section-page"]
      decls := [("justify-content", "center"), ("align-items", "center")] },
    { selector := [.lit "h1"], decls := [("font-size", scaleSize "LARGE" "em")] },
    { selector := [.lit "h2"], decls := [("font-size", scaleSize "Large" "em")] },
    { selector := [.lit "h3"], decls := [("font-size", scaleSize "large" "em")] },
    { selector := [.lit "section.slide > header"]
      decls := [("max-height", titlebandVar)] },
    { selector := [.lit "section.slide > header h2"]
      decls := [("font-size", scaleSize "Large" "em")] } ]

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
overlay steps (`Ir.maxStepBlocks`) is one sticky stage over N snap
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
(`:not([data-step="1"])`). -/
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

/-- The floor's snap carrier for a stepped frame: with the spacers
hidden the stage itself is the snap page, through the same alignment the
door rule declares. -/
def stepTrackFloorSnap : DeckRule :=
  { selector := [.lit ".slide-track > section.slide"]
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
track takes one viewport, and the stage keeps the frame's snap. -/
def stepTrackWidthReduce : DeckRule :=
  { selector := [.lit ".slide-track"]
    decls := [("width", "100vw"), ("flex", "0 0 100vw")]
    part := .reduce }

def stepSnapReduceHide : DeckRule :=
  { selector := [.lit ".snap"], decls := [("display", "none")]
    part := .reduce }

def stepTrackSnapReduce : DeckRule :=
  { selector := [.lit ".slide-track > section.slide"]
    decls := [("scroll-snap-align", "start"), ("scroll-snap-stop", "always")]
    part := .reduce }

/-- The step rules with a closed spelling — every one whose value reads
no parameter, checkable in one `decide`. -/
def stepFixed : List DeckRule :=
  [stepTrackRule, stepStageRule, stepSnapSize, stepUncoverRule,
   stepSnapHide, stepTrackFloorSnap, stepGuard, stepCoveredGuard,
   stepTrackWidthReduce, stepSnapReduceHide, stepTrackSnapReduce]

/-- Every rule the steps add, shipped exactly when the deck has steps —
a stepless deck has nothing to reveal and no track to lay out. -/
def stepRules (coveredPct maxSteps : Nat) : List DeckRule :=
  stepKeyframes coveredPct :: stepFloorCovered coveredPct ::
    (stepFixed ++ stepSnapped maxSteps)

/-- The print partition: the handout, one bordered card per frame
(Tufte: the handout is the document) — the logo prints with its card,
absolute in the card's padding box as it is absolute in the stage's safe
area (furniture on paper too, `position: relative` on the card anchors
it) — and for a stepped deck the snap
spacers hide, the wrapper takes the card gap its section can no longer
claim as `* + section.slide` (it is the wrapper's first child), and
every step prints at full colour: paper has no steps to reveal (the
user's own rule, beside the unconditional covered floor it was written
against). -/
def deckPrint (maxSteps : Nat) : List DeckRule :=
  [ { selector := [.lit "section.slide"]
      decls := [("border", s!"{slideBorderPx}px solid var(--rule)"),
        ("border-radius", s!"{slideRadiusPx}px"),
        ("padding", s!"{slidePadV} {slidePadH}"),
        ("margin", "0"), ("break-inside", "avoid"),
        ("position", "relative")]
      part := .print },
    { selector := [.lit ".slide-logo"]
      decls := [("position", "absolute"), ("bottom", slidePadV),
        ("left", slidePadH), ("right", slidePadH), ("display", "flex")]
      part := .print },
    { selector := [.lit "* + section.slide"]
      decls := [("margin-top", slidePadV)]
      part := .print },
    { selector := [.lit "section.slide"]
      decls := [("break-after", "page")]
      part := .print } ] ++
    (if 2 ≤ maxSteps then
      [ { selector := [.lit ".snap"], decls := [("display", "none")]
          part := .print },
        { selector := [.lit "* + .slide-track"]
          decls := [("margin-top", slidePadV)]
          part := .print },
        { selector := [.lit ".step"], decls := [("opacity", "100%")]
          part := .print } ]
     else [])

/-- Every rule of the deck's stylesheet, in emission order. The
parameters are the whole document-dependence: the stage-ratio type size,
the design's covered fraction, and the deck's maximum step count. -/
def deckRules (bodyVh : String) (coveredPct maxSteps : Nat) : List DeckRule :=
  deckBase bodyVh ++ deckReduce ++
    (if 2 ≤ maxSteps then stepRules coveredPct maxSteps else []) ++
    deckPrint maxSteps

/-- The one case split over the deck's rule set: every deck theorem
below quantifies over `deckRules` through this. A new rule family is a
new hypothesis here — the compiler names every theorem it now owes. The
step hypotheses receive the fact that the steps shipped (`2 ≤ ms`), so a
theorem may cite a step rule's membership. -/
private theorem deckRules_forall {P : DeckRule → Prop} {v : String} {cp ms : Nat}
    (hbase : ∀ r ∈ deckBase v, P r)
    (hreduce : ∀ r ∈ deckReduce, P r)
    (hkey : 2 ≤ ms → P (stepKeyframes cp))
    (hcov : 2 ≤ ms → P (stepFloorCovered cp))
    (hfix : 2 ≤ ms → ∀ r ∈ stepFixed, P r)
    (hsnapped : 2 ≤ ms → ∀ k, P (stepSnappedRule k))
    (hprint : ∀ r ∈ deckPrint ms, P r) :
    ∀ r ∈ deckRules v cp ms, P r := by
  intro r hr
  simp only [deckRules, List.mem_append] at hr
  rcases hr with ((h | h) | h) | h
  · exact hbase r h
  · exact hreduce r h
  · split at h
    case isTrue hms =>
      simp only [stepRules, stepSnapped, List.mem_append, List.mem_cons,
        List.mem_map, List.mem_range] at h
      rcases h with rfl | rfl | h | ⟨i, -, rfl⟩
      · exact hkey hms
      · exact hcov hms
      · exact hfix hms r h
      · exact hsnapped hms _
    case isFalse => cases h
  · exact hprint r h

/-- Family memberships, spelled once against the append spine. -/
private theorem mem_deckRules_base {r : DeckRule} {v : String} {cp ms : Nat}
    (h : r ∈ deckBase v) : r ∈ deckRules v cp ms := by
  simp only [deckRules, List.mem_append]
  exact Or.inl (Or.inl (Or.inl h))

private theorem mem_deckRules_reduce {r : DeckRule} {v : String} {cp ms : Nat}
    (h : r ∈ deckReduce) : r ∈ deckRules v cp ms := by
  simp only [deckRules, List.mem_append]
  exact Or.inl (Or.inl (Or.inr h))

private theorem mem_deckRules_step {r : DeckRule} {v : String} {cp ms : Nat}
    (hms : 2 ≤ ms) (h : r ∈ stepRules cp ms) : r ∈ deckRules v cp ms := by
  simp only [deckRules, List.mem_append]
  refine Or.inl (Or.inr ?_)
  split
  · exact h
  · omega

/-- A closed step rule's membership, through the `stepFixed` spine. -/
private theorem mem_stepRules_fixed {r : DeckRule} {cp ms : Nat}
    (h : r ∈ stepFixed) : r ∈ stepRules cp ms := by
  simp only [stepRules, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inl h))

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
private theorem deckRules_check {p : DeckRule → Bool} (v : String) (cp ms : Nat)
    (hbase : ∀ r ∈ deckBase v, p r = true)
    (hreduce : ∀ r ∈ deckReduce, p r = true)
    (hkey : p (stepKeyframes cp) = true)
    (hcov : p (stepFloorCovered cp) = true)
    (hfix : ∀ r ∈ stepFixed, p r = true)
    (hsnapped : ∀ k, p (stepSnappedRule k) = true)
    (hprint : ∀ r ∈ deckPrint 2, p r = true) :
    ∀ r ∈ deckRules v cp ms, p r = true :=
  deckRules_forall hbase hreduce (fun _ => hkey) (fun _ => hcov)
    (fun _ => hfix) (fun _ _ => hsnapped _)
    (fun r hr => hprint r (deckPrint_subset r hr))

/-- Membership in the base family, for the rules with a parametric
value: the check is discharged by `rfl` after the case split. -/
private theorem deckBase_cases {P : DeckRule → Prop} {v : String}
    (h1 : P { selector := [.lit "html"]
              decls := [("scroll-snap-type", "x mandatory"), ("overflow-y", "clip")] })
    (h2 : P deckGlideRule)
    (h3 : P { selector := [.lit "body"], decls := [("padding", "0")] })
    (h4 : P { selector := [.lit "main"]
              decls := [("max-width", "none"), ("margin", "0"), ("display", "flex"),
                ("align-items", "flex-start"), ("font-size", v)] })
    (h5 : P deckStageRule)
    (h6 : P deckSnapDoor)
    (h6a : P deckLogoRule)
    (h7 : P { selector := [.lit "section.section-page"]
              decls := [("justify-content", "center"), ("align-items", "center")] })
    (h8 : P { selector := [.lit "h1"], decls := [("font-size", scaleSize "LARGE" "em")] })
    (h9 : P { selector := [.lit "h2"], decls := [("font-size", scaleSize "Large" "em")] })
    (h10 : P { selector := [.lit "h3"], decls := [("font-size", scaleSize "large" "em")] })
    (h11 : P { selector := [.lit "section.slide > header"]
               decls := [("max-height", titlebandVar)] })
    (h12 : P { selector := [.lit "section.slide > header h2"]
               decls := [("font-size", scaleSize "Large" "em")] }) :
    ∀ r ∈ deckBase v, P r := by
  intro r hr
  simp only [deckBase, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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
theorem deck_css_partition (v : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v cp ms, gateRespects r = true :=
  deckRules_check v cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl (by decide) (fun _ => rfl) (by decide)

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
`left`, `right`) are CSS 2. The selector side of the floor is
`deck_css_partition`; attribute selectors (`[data-snap]`,
`[data-deck-script]`) are CSS 2. -/
def baselineProps : List String :=
  ["scroll-snap-type", "scroll-snap-align", "scroll-snap-stop",
   "scroll-behavior", "padding", "margin", "margin-top", "max-width",
   "width", "flex", "background", "overflow-y",
   "min-height", "max-height", "height", "font-size", "color",
   "text-align", "opacity", "transform", "display", "flex-direction",
   "justify-content", "align-items", "position", "content",
   "animation", "border", "border-radius", "break-inside", "break-after",
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
theorem floor_is_baseline (v : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v cp ms,
      (!(onFloor r) || r.decls.all fun d => baselineProps.contains d.1) = true :=
  deckRules_check v cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl (by decide) (fun _ => rfl) (by decide)

/-- Content, as the floor theorems see it: the frame stages and the
steps — the fragments that address what the deck *shows*. -/
def contentFrags : List String :=
  ["section.slide", "section.section-page", ".step[", ".step:"]

def targetsContent (r : DeckRule) : Bool :=
  contentFrags.any fun frag =>
    (r.selector.flatMap SelChunk.lits).any fun s => hasFrag s frag

/-- The floor is visible by theorem, not by review: no deck rule — in
*any* partition — sets `display: none` or `visibility: hidden` on
content (`contentFrags`). What the guards and the print handout hide is
only the spacers. `floor_opacity_mem` and `floor_covered_script_gated`
are the dimming half. -/
theorem floor_hides_nothing (v : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v cp ms,
      (!(targetsContent r) ||
        (!(r.decls.contains ("display", "none")) &&
         !(r.decls.contains ("visibility", "hidden")))) = true :=
  deckRules_check v cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl (by decide) (fun _ => rfl) (by decide)

/-- The opacity values a rule sets. -/
def opacityValues (r : DeckRule) : List String :=
  r.decls.filterMap fun d => if d.1 == "opacity" then some d.2 else none

/-- The dimming half of the visible floor: every opacity any deck rule
sets is full or the design's own covered fraction — never below it, and
never a hide wearing a dim's clothes. `_mem`'s grade: each value is
drawn from the two the design allows. -/
theorem floor_opacity_mem (v : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v cp ms, ∀ o ∈ opacityValues r,
      o = "100%" ∨ o = s!"{cp}%" := by
  refine deckRules_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact deckBase_cases (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho)
  · intro r hr
    simp only [deckReduce, deckGlideGuard, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl
    exact fun o ho => nomatch ho
  · exact fun _ o ho => Or.inr (List.mem_singleton.mp ho)
  · exact fun _ o ho => Or.inr (List.mem_singleton.mp ho)
  · intro _ r hr
    simp only [stepFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact fun o ho => Or.inl (List.mem_singleton.mp ho)
        | exact fun o ho => nomatch ho
  · exact fun _ k o ho => Or.inl (List.mem_singleton.mp ho)
  · intro r hr
    have hr2 := deckPrint_subset r hr
    simp only [deckPrint, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr2
    rcases hr2 with (rfl | rfl | rfl | rfl) | h2
    · exact fun o ho => nomatch ho
    · exact fun o ho => nomatch ho
    · exact fun o ho => nomatch ho
    · exact fun o ho => nomatch ho
    · split at h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl | rfl
        · exact fun o ho => nomatch ho
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
theorem floor_covered_script_gated (v : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v cp ms,
      (!(onFloor r) || scriptGated r ||
        r.decls.all fun d => d.1 != "opacity" || d.2 == "100%") = true :=
  deckRules_check v cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl (by decide) (fun _ => rfl) (by decide)

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

/-- Is every motion property the rule declares guarded by some rule of
the searched set's reduce partition? -/
def motionGuarded (rules : List DeckRule) (r : DeckRule) : Bool :=
  r.part != Part.screen ||
    r.decls.all fun d =>
      !(motionProps.contains d.1) ||
        rules.any fun g => guardCovers g r && g.decls.contains (d.1, motionOff d.1)

/-- `motionGuarded` from one named witness. -/
private theorem motionGuarded_of_guard {rules : List DeckRule} {r g : DeckRule}
    (hg : g ∈ rules)
    (hchk : ∀ d ∈ r.decls, motionProps.contains d.1 = true →
      (guardCovers g r && g.decls.contains (d.1, motionOff d.1)) = true) :
    motionGuarded rules r = true := by
  unfold motionGuarded
  cases hpart : (r.part != Part.screen)
  · rw [Bool.false_or, List.all_eq_true]
    intro d hd
    cases hmp : motionProps.contains d.1
    · rw [Bool.not_false, Bool.true_or]
    · rw [Bool.not_true, Bool.false_or]
      exact List.any_eq_true.mpr ⟨g, hg, hchk d hd hmp⟩
  · rw [Bool.true_or]

/-- Every rule that sets a motion property (`motionProps`) has a
reduced-motion counterpart *in the same emitted rule set*, covering its
selector and setting the property back to its static value: a guard is
not a suffix a definition happens to end with; it is a rule the reduce
partition must contain, and the partition is emitted after the blocks it
reverts (`emitDeckRules`; CSS Cascade 5 §6.4). `_contract`'s grade. -/
theorem guards_by_construction (v : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v cp ms, motionGuarded (deckRules v cp ms) r = true := by
  refine deckRules_forall ?_ ?_ (fun _ => rfl) (fun _ => rfl) ?_
    (fun _ _ => rfl) ?_
  · exact deckBase_cases rfl
      (motionGuarded_of_guard (g := deckGlideGuard)
        (mem_deckRules_reduce (by decide)) (by decide))
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · intro r hr
    simp only [deckReduce, deckGlideGuard, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl
    rfl
  · intro hms r hr
    have hstep : stepGuard ∈ deckRules v cp ms :=
      mem_deckRules_step hms (mem_stepRules_fixed (by decide))
    simp only [stepFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    case inr.inr.inr.inl =>
      exact motionGuarded_of_guard hstep (by decide)
    all_goals rfl
  · intro r hr
    have hr2 := deckPrint_subset r hr
    simp only [deckPrint, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr2
    rcases hr2 with (rfl | rfl | rfl | rfl) | h2
    · rfl
    · rfl
    · rfl
    · rfl
    · split at h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl | rfl <;> rfl
      · cases h2

/-- Every step of every stepped frame is reachable in the floor: for
each step `n` of a deck whose maximum step count is `ms`
(`Ir.maxStepBlocks`; step 1 is never covered), the emitted rules contain
an uncover rule whose snap is a spacer `k ≥ n` uncovering `n` —
concretely `k = n`, the `data-snapped` value the script writes when the
reader's key lands that snap point. The uncover set `uncoveredBy k` is
the selector's own data: the `:is()` alternatives render from it
(`SelChunk.stepAlts`). `_covers`'s grade. -/
theorem snapped_uncovers_every_step (v : String) (cp ms n : Nat)
    (h2 : 2 ≤ n) (hn : n ≤ ms) :
    ∃ k, n ≤ k ∧ stepSnappedRule k ∈ deckRules v cp ms ∧ n ∈ uncoveredBy k := by
  refine ⟨n, Nat.le_refl n, ?_, ?_⟩
  · refine mem_deckRules_step (Nat.le_trans h2 hn) ?_
    simp only [stepRules, stepSnapped, List.mem_cons, List.mem_append,
      List.mem_map, List.mem_range]
    refine Or.inr (Or.inr (Or.inr ⟨n - 2, by omega, ?_⟩))
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
(`pages_count_frame_steps`, the owed PDF half, is this count's twin).
On the floor the spacers hide (`stepSnapHide`) and the stage takes the
frame's one snap (`stepTrackFloorSnap`): one snap point per frame.
`_covers`'s grade over the partition: each fact is the membership of the
rule that carries it, in the gate that scopes it. -/
theorem snap_pages_partition_frames (v : String) (cp ms : Nat) (hms : 2 ≤ ms) :
    (deckSnapDoor ∈ deckRules v cp ms ∧ deckSnapDoor.requires = .base ∧
      ("scroll-snap-align", "start") ∈ deckSnapDoor.decls) ∧
    (stepSnapHide ∈ deckRules v cp ms ∧
      stepSnapHide.requires = .unsupported .viewTimeline ∧
      ("display", "none") ∈ stepSnapHide.decls) ∧
    (stepTrackFloorSnap ∈ deckRules v cp ms ∧
      stepTrackFloorSnap.requires = .unsupported .viewTimeline ∧
      ("scroll-snap-align", "start") ∈ stepTrackFloorSnap.decls) :=
  ⟨⟨mem_deckRules_base (by simp [deckBase]), rfl, by decide⟩,
   ⟨mem_deckRules_step hms (mem_stepRules_fixed (by decide)), rfl, by decide⟩,
   ⟨mem_deckRules_step hms (mem_stepRules_fixed (by decide)), rfl, by decide⟩⟩

/-- The text census does not depend on which path a browser takes:
trivially, since the stylesheet ships no text — no deck rule sets a
non-empty `content` — and the tree is one, whichever `@supports` branch
an engine parses; its census against the IR is the emission conservation
the census checks pin (`censusTable` in Tests). Stated as the projection
statement the theorem-layers rule asks for; `_text`'s grade, the census
contribution being empty. -/
theorem deck_text_path_free (v : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v cp ms,
      (r.decls.all fun d =>
        d.1 != "content" || (d.2 == "\"\"" || d.2 == "none")) = true :=
  deckRules_check v cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl (by decide) (fun _ => rfl) (by decide)

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

/-- The keyboard and floor-uncover script. It binds, on the deck's snap
points: ArrowRight/ArrowDown/PageDown/Space → next; ArrowLeft/ArrowUp/
PageUp/Shift+Space → previous; Home/End → first/last. It ignores key
events whose target is editable or that carry modifiers other than
Shift, and respects reduced motion (`matchMedia` → instant scroll, and
hidden spacers are skipped so a stepped frame is one press). "Snap
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
declared. -/
def deckScript : String :=
  "(() => {
  document.documentElement.dataset.deckScript = \"\";
  const snaps = Array.from(document.querySelectorAll(\"[data-snap]\"));
  if (snaps.length === 0) return;
  const reduce = matchMedia(\"(prefers-reduced-motion: reduce)\");
  const box = (el) => {
    const r = el.getBoundingClientRect();
    return r.width > 0 ? r : (el.closest(\".slide-track\") || el).getBoundingClientRect();
  };
  let cur = 0;
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
  const go = (i) => {
    cur = Math.min(Math.max(i, 0), snaps.length - 1);
    mark();
    const el = snaps[cur].getBoundingClientRect().width > 0
      ? snaps[cur] : (snaps[cur].closest(\".slide-track\") || snaps[cur]);
    el.scrollIntoView({ behavior: reduce.matches ? \"auto\" : \"smooth\",
      inline: \"start\", block: \"nearest\" });
  };
  const sync = () => {
    let best = cur;
    for (let i = 0; i < snaps.length; i += 1)
      if (Math.abs(box(snaps[i]).left) < Math.abs(box(snaps[best]).left)) best = i;
    if (box(snaps[best]).left !== box(snaps[cur]).left) { cur = best; mark(); }
  };
  addEventListener(\"scroll\", sync, { passive: true });
  sync();
  const skip = (i, dir) => {
    while (reduce.matches && snaps[i] && snaps[i].getBoundingClientRect().width === 0)
      i += dir;
    return i;
  };
  addEventListener(\"keydown\", (e) => {
    if (e.ctrlKey || e.altKey || e.metaKey || e.defaultPrevented) return;
    const t = e.target;
    if (t instanceof Element &&
        (t.isContentEditable || /^(input|textarea|select|button)$/i.test(t.tagName))) return;
    let i = null;
    if (e.key === \"Home\") i = 0;
    else if (e.key === \"End\") i = snaps.length - 1;
    else if ((e.key === \" \" && e.shiftKey) || e.key === \"ArrowLeft\" ||
        e.key === \"ArrowUp\" || e.key === \"PageUp\") i = skip(cur - 1, -1);
    else if ((e.key === \" \" && !e.shiftKey) || e.key === \"ArrowRight\" ||
        e.key === \"ArrowDown\" || e.key === \"PageDown\") i = skip(cur + 1, 1);
    if (i === null) return;
    e.preventDefault();
    go(i);
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
  const box = (el) => {
    const r = el.getBoundingClientRect();
    return r.width > 0 ? r : (el.closest(\".slide-track\") || el).getBoundingClientRect();
  };
  let cur = 0;
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
  const go = (i) => {
    cur = Math.min(Math.max(i, 0), snaps.length - 1);
    mark();
    const el = snaps[cur].getBoundingClientRect().width > 0
      ? snaps[cur] : (snaps[cur].closest(\".slide-track\") || snaps[cur]);
    el.scrollIntoView({ behavior: reduce.matches ? \"auto\" : \"smooth\",
      inline: \"start\", block: \"nearest\" });
  };
  const sync = () => {
    let best = cur;
    for (let i = 0; i < snaps.length; i += 1)
      if (Math.abs(box(snaps[i]).left) < Math.abs(box(snaps[best]).left)) best = i;
    if (box(snaps[best]).left !== box(snaps[cur]).left) { cur = best; mark(); }
  };
  addEventListener(\"scroll\", sync, { passive: true });
  sync();
  const skip = (i, dir) => {
    while (reduce.matches && snaps[i] && snaps[i].getBoundingClientRect().width === 0)
      i += dir;
    return i;
  };
  addEventListener(\"keydown\", (e) => {
    if (e.ctrlKey || e.altKey || e.metaKey || e.defaultPrevented) return;
    const t = e.target;
    if (t instanceof Element &&
        (t.isContentEditable || /^(input|textarea|select|button)$/i.test(t.tagName))) return;
    let i = null;
    if (e.key === \"Home\") i = 0;
    else if (e.key === \"End\") i = snaps.length - 1;
    else if ((e.key === \" \" && e.shiftKey) || e.key === \"ArrowLeft\" ||
        e.key === \"ArrowUp\" || e.key === \"PageUp\") i = skip(cur - 1, -1);
    else if ((e.key === \" \" && !e.shiftKey) || e.key === \"ArrowRight\" ||
        e.key === \"ArrowDown\" || e.key === \"PageDown\") i = skip(cur + 1, 1);
    if (i === null) return;
    e.preventDefault();
    go(i);
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
Scroll Snap 1 §4.1), so the keys need no focus. In print it is the
linear handout, one bordered card per page (Tufte: the handout is the
document). A section page is one snap page like any frame, its content
centred on both axes. Every other class keeps the card rendering on
both media: deck rules and the script are the slides class's own, which
is what keeps the site port's webpage output unchanged. -/
private def slideCss (doc : Doc) : String :=
  -- The handout card, today's rendering, byte for byte: the only-media
  -- form for every non-deck class, the print twin for the deck.
  let handout :=
    s!"section.slide \{ border: {slideBorderPx}px solid var(--rule); border-radius: {slideRadiusPx}px;\n" ++
    s!"  padding: {slidePadV} {slidePadH}; margin: 0; break-inside: avoid; }\n" ++
    s!"* + section.slide \{ margin-top: {slidePadV}; }\n"
  -- The slide header's shared type rule, inside this split so the deck's
  -- screen override below can stand after it and win the cascade.
  let headerH2 :=
    s!"section.slide > header h2 \{ margin: 0; font-size: {scaleSize "Large" "rem"}; }\n"
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
        (Design.ofDoc doc).coveredFraction maxSteps)
  else handout ++ headerH2

/-- Whether the document carries a listing whose apparatus the stylesheet
must draw — a caption or line numbers: the gate on the listing CSS, so a
document without one ships exactly the stylesheet it shipped before. -/
private def docHasListing (doc : Doc) : Bool :=
  Ir.foldBlocks (fun b bl => b || match bl with
      | .verbatim _ _ spec => spec.caption.isSome || spec.numbers
      | _ => false)
    (fun b _ => b) false doc.body

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
  -- The document's own declarations, AFTER the dark variant: a declared
  -- palette key or token is the document's value in BOTH colour schemes,
  -- so a themed deck's --muted in dark mode is the theme's, not the
  -- scheme default's. The scheme blocks above are defaults for what the
  -- document left undeclared; a media query adds no specificity, so at
  -- the shared :root specificity source order is the whole cascade here
  -- — the same equal-specificity, order-decides contract the declared
  -- stylesheet link relies on below.
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
  -- artifacts request kerning from one value, agreement by construction.
  (if Ir.features.kern then "  font-kerning: normal;\n" else "") ++
  "  -webkit-font-smoothing: antialiased;\n" ++
  "}\n" ++
  "main { max-width: var(--measure); margin: 0 auto; }\n" ++
  -- Headings from the IR's own scale — the sizes the PDF sets
  -- (`Layout.sectionSize`, classes.dtx §Sectioning: the title at LARGE, a
  -- section at Large, a subsection at large), so `heading_hierarchy`'s
  -- ordering covers this backend for free; the line height is the
  -- engine's one leading ratio. Hand-picked decimals here once drifted a
  -- rounding step from the scale sixty lines above the rules generated
  -- from it. Margins are zero here and on every block element: a
  -- boundary's gap has exactly one emitter (`blockGapCss`).
  "h1, h2, h3, h4 {\n" ++
  "  font-family: var(--font-sans);\n" ++
  "  font-weight: 600;\n" ++
  s!"  line-height: {milliFactor Ir.leadingMilli};\n" ++
  -- The band below a heading is the heading's own, one peer gap: the PDF
  -- semantics (a heading's declared `after` replaces the peer gap), and
  -- the one bottom-owned boundary — its follower's default top margin is
  -- suppressed in `blockGapCss`, so it still has exactly one emitter.
  s!"  margin: 0 0 {quantaRem (gapK "peer")};\n" ++
  "  text-wrap: balance;\n" ++
  "}\n" ++
  s!"h1 \{ font-size: {scaleSize "LARGE" "rem"}; }\n" ++
  s!"h2 \{ font-size: {scaleSize "Large" "rem"}; }\n" ++
  s!"h3 \{ font-size: {scaleSize "large" "rem"}; }\n" ++
  -- hyphens follows the declared language: the browser's dictionaries on
  -- the same lang= tags the engine's patterns read — one declaration, two
  -- conforming hyphenators (the agreement is about tags, never breaks).
  "p { margin: 0; hyphens: auto; }\n" ++
  "ul, ol { margin: 0; padding-left: 1.35rem; }\n" ++
  -- No per-item gap, as the PDF declares none: a list is one block, and
  -- its leading is its rhythm. A document declares its own through
  -- `\style{itemize}{ gap = ... }`.
  "li { margin: 0; }\n" ++
  -- A quotation moves both edges in, as the PDF sets it (classes.dtx:
  -- `\rightmargin\leftmargin`); the browser's own quote margins would be
  -- a second, unowned vertical emission.
  "blockquote { margin: 0; padding: 0 1.35rem; }\n" ++
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
  "a:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }\n" ++
  "code, pre { font-family: var(--font-mono); font-size: 0.925em; }\n" ++
  s!"pre \{ background: var(--tint); padding: {quantaRem 1} 1rem; overflow-x: auto;\n" ++
  "      border-radius: 4px; }\n" ++
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
  ".centered { text-align: center; }\n" ++
  ".ragged { text-align: left; }\n" ++
  ".fill { flex: 1 1 auto; }\n" ++
  s!".spaced \{ margin-top: var(--sep, {slidePadV}); }\n" ++
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
  -- The other font-axis classes (fntguide §2.2 through `Ir.Style`): roman
  -- family, medium series, upright shape — each resets exactly its axis.
  ".rm { font-family: var(--font-body); }\n" ++
  ".md { font-weight: 400; }\n" ++
  ".up { font-style: normal; font-variant-caps: normal; }\n" ++
  ".ruled::after { content: \"\"; flex: 1; border-top: 1px solid var(--rule-color);\n" ++
  -- Half the x-height up from the baseline, in the rule's own inherited
  -- ex — the heading's face — where the PDF draws it (Layout.paraLineGeom;
  -- Hochuli: a rule relates to the type it cuts).
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
  "ol.algorithm.numbered { padding-left: 2em; position: relative; }\n" ++
  "ol.algorithm.numbered li { counter-increment: algline; }\n" ++
  -- one number column at the block's own left edge, whatever the line's
  -- depth — the PDF's marker column (`markerIndent`), the same shape
  "ol.algorithm.numbered li::before { content: counter(algline);\n" ++
  "  color: var(--muted); font-size: 0.8em; width: 1.5em;\n" ++
  "  position: absolute; left: 0; text-align: right; }\n" ++
  "figure.float { margin: 0 auto; }\n" ++
  "figure.float > table { margin-left: auto; margin-right: auto; }\n" ++
  "figure.float > img { display: block; margin: 0 auto; }\n" ++
  s!"figure.float > figcaption \{ margin-top: var(--captionsep, {quantaRem (gapK "caption")});\n" ++
  "  padding: 0 var(--captionmargin, 0px);\n" ++
  "  text-align: center; text-wrap: balance; }\n" ++
  s!"figure.float > figcaption:first-child \{ margin-top: 0;\n" ++
  s!"  margin-bottom: var(--captionsep, {quantaRem (gapK "caption")}); }\n" ++
  blockGapCss ++
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
  -- Display math opens the page's own block rhythm above and below — the
  -- declared peer multiple, the boundary a paragraph pays — no new
  -- constant.
  s!".math-display \{ margin: {quantaRem (gapK "peer")} 0; }\n" ++
  -- The numbered display: the formula's box takes the measure and centres
  -- its own text; the tag sits on the right edge, vertically centred on
  -- the formula (amsmath's equation shape).
  ".equation { display: flex; align-items: center; }\n" ++
  ".equation > .math { flex: 1 1 auto; text-align: center; }\n" ++
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
  | .roman => "rm"
  | .medium => "md"
  -- unused: the styled arm emits `.series` as a per-run numeric
  -- `font-weight`, the value CSS matches faces by, never a class
  | .series w => s!"w{w.css}"
  | .upright => "up"
  | .size n => "size-" ++ n
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
    let deckDim (l : Image.Len) (vertical : Bool) : Option String :=
      if l.tw != 0 && l.sp == 0 && l.th == 0 then
        some (decMilli (l.tw * 100) ++ "%")
      else if l.tw == 0 then
        let (stage, unit) :=
          if vertical then (cfg.page.height, "dvh") else (cfg.page.width, "vw")
        let textW := cfg.page.width - 2 * cfg.page.hmargin
        let textH := cfg.page.height - 2 * cfg.page.vmargin
        some (decMilli (deckStageMilli (l.resolve textW textH) stage) ++ unit)
      else none
    let dim (l : Image.Len) (vertical : Bool) : Option String :=
      if cfg.deck then deckDim l vertical else cssDim l
    let wCss := size.width.bind (dim · false)
    let hCss := size.height.bind (dim · true)
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
            let scaled := inf.width * size.scaleNum / size.scaleDen
            if cfg.deck then
              s!"width: {decMilli (deckStageMilli scaled cfg.page.width)}vw; height: auto"
            else
              s!"width: {Dim.Sp.toPtString scaled}pt; height: auto"
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
        ("data-tex", src)] body)
  | .styled st body =>
    let kids := inlineNodesInto cfg #[] body.toList
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
    -- The language of a run is a declaration, not a style: the span
    -- carries `lang` (HTML §3.2.6.2; WCAG 2.2 SC 3.1.2), which CSS
    -- `hyphens: auto` and assistive technology both read.
    | .lang tag => acc.push (Html.elem "span" kids #[("lang", tag)])
    | other => acc.push (Html.elem "span" kids #[("class", styleClass other)])
  | .role n body =>
    -- The class hook: the authored name survives as an addressable class,
    -- through the typed tree and the attribute escaper by construction
    -- (role_class_reaches_artifact).
    acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList)
      #[("class", roleClass n)])
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
  | .underline body =>
    -- skip-ink is the browser's native form of the PDF path's invariant: the
    -- rule breaks where a descender crosses it.
    acc.push (Html.elem "u" (inlineNodesInto cfg #[] body.toList))
  | .step n last body =>
    -- Every step is fully visible here — the handout state, the floor the
    -- deck's reveal degrades to. On the paged deck the class-gated
    -- stylesheet uncovers the step in place as the reader's arrow
    -- advances the frame's snap points (`deckStepCss`); the `--step`
    -- index names its snap point, and the range rides as data either way.
    acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList)
      (#[("class", "step"), ("data-step", toString n)] ++
        (match last with
         | some u => #[("data-step-last", toString u)]
         | none => #[]) ++
        #[("style", s!"--step: {n}")]))
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
  -- A strut props its line open in print; a continuous page reads at its
  -- own line-height, so the carrier is empty and adds no box.
  | .strut _ => acc
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

/-- One table cell: its column's alignment as inline style (the PDF path
reads the same `ColSpec.align`), the `bt-cmid` class when a `\cmidrule`
spans its column, and — for a header cell — `scope=col`, the one scope a
booktabs head declares (HTML §4.9.10: a `th` heading the cells below it).
The cell's children are the same `inlines` a `td` carried. -/
def tableCellNode (cfg : Config) (cols : Array Ir.ColSpec) (cmids : Array (Nat × Nat))
    (headerRows i j : Nat) (cell : Array Inline) : Node :=
  let al := match (cols[j]?.map (·.align)).getD .left with
    | .center => #[("style", "text-align: center")]
    | .right => #[("style", "text-align: right")]
    | .left => #[]
  let attrs := if cmids.any (fun (a, b) => a ≤ j + 1 && j + 1 ≤ b)
    then al.push ("class", "bt-cmid") else al
  let attrs := if i < headerRows then attrs.push ("scope", "col") else attrs
  Html.elem (tableCellTag headerRows i) (inlines cfg cell) attrs

/-- The cells of row `i`, in column order. -/
def tableRowCells (cfg : Config) (cols : Array Ir.ColSpec) (cmids : Array (Nat × Nat))
    (headerRows i : Nat) (row : Array (Array Inline)) : Array Node :=
  row.mapIdx fun j cell => tableCellNode cfg cols cmids headerRows i j cell

/-- A cell is a `th` exactly when its row lies in the header prefix — the
HTML projection of `Ir.tableHeaderRows`, stated over the typed tree the
table arm builds: the tag at every cell position of row `i` is `th` iff
`i < headerRows`, whatever the column, the alignment, or the cmid spans. -/
theorem th_iff_header_row (cfg : Config) (cols : Array Ir.ColSpec)
    (cmids : Array (Nat × Nat)) (headerRows i : Nat) (row : Array (Array Inline))
    (j : Nat) (hj : j < row.size) :
    ((tableRowCells cfg cols cmids headerRows i row)[j]'(by
        simp [tableRowCells, hj])).tag? = some "th" ↔ i < headerRows := by
  simp only [tableRowCells, Array.getElem_mapIdx, tableCellNode, Html.elem, Html.Node.tag?,
    Option.some.injEq]
  exact tableCellTag_th_iff headerRows i

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
    (rows : Array (Array (Array Inline))) (rules : Array (Nat × Ir.TableRule)) : Node :=
  let headerRows := Ir.tableHeaderRows rows rules
  let ruleAt (i : Nat) : Array Ir.TableRule :=
    rules.foldl (fun out (k, r) => if k == i then out.push r else out) #[]
  let drawn (r : Ir.TableRule) : Bool := match r with
    | .gap _ => false
    | .top | .mid | .bottom | .cmid .. => true
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
    Html.elem "tr" (tableRowCells cfg cols cmids headerRows i row)
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
  Html.elem "table" kids #[("class", cls)]

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

/-- The class hook's emission half: an authored role reaches the artifact
as an element carrying exactly `roleClass name`, children the emission of
its body. The name enters attribute position only through the typed tree,
so it passes `escapeAttr` by construction (`escapeAttr_no_quote` is what
closes attribute breakout); `roleClass_single_token` is why the value is
one class token. -/
theorem role_class_reaches_artifact (cfg : Config) (acc : Array Node)
    (n : String) (body : Array Inline) :
    inlineNodeInto cfg acc (.role n body) =
      acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList)
        #[("class", roleClass n)]) := by
  simp [inlineNodeInto]

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

/-- The heading tag a section level takes: `h` and the shared rank
(`Ir.headingRank`, which carries the sourcing), so the tag and the
markdown marker cannot drift; `heading_renderings_agree` in Tests states
the agreement over every level. -/
def headingTag (level : Nat) : String :=
  s!"h{Ir.headingRank level}"

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

/-- Children start their own sibling walk: the parent's accumulated epoch
style already stands on an ancestor element and inherits into it, so it is
never re-applied below. The epoch palette and tokens carry in for the
diffs a nested declaration makes. -/
def Config.into (cfg : Config) : Config := { cfg with epochStyle := "" }

private def joinStyles (a b : String) : String :=
  if a.isEmpty then b else if b.isEmpty then a else a ++ "; " ++ b

/-- The custom-property redefinitions a body `\palette` makes, against the
palette in force before it: exactly the changed entries, so an epoch
declares what it changed and nothing else. -/
def epochPaletteStyle (before after : Ir.Palette) : String :=
  String.intercalate "; " ((after.entries.filter fun (n, c) =>
    before.find? n != some c).toList.map fun (n, c) => s!"--{n}: {cssColor c}")

/-- The redefinitions a body `\tokens` makes, same diff. -/
def epochTokenStyle (before after : Ir.Tokens) : String :=
  String.intercalate "; " ((after.entries.filter fun (n, g) =>
    before.find? n != some g).toList.map fun (n, g) => s!"--{n}: {cssLength g.width}")

/-- The epoch's redefinitions onto one emitted sibling node. The epoch
comes first, so an element's own style declarations win (CSS style
attribute: last declaration of a property applies). A text node carries no
attributes and needs none. -/
def withEpoch (style : String) : Node → Node
  | .elem t attrs kids =>
    if style.isEmpty then .elem t attrs kids
    else if attrs.any (·.1 == "style") then
      .elem t (attrs.map fun kv =>
        if kv.1 == "style" then (kv.1, style ++ "; " ++ kv.2) else kv) kids
    else .elem t (attrs.push ("style", style)) kids
  | .text s => .text s
  | .style css => .style css
  | .script attrs code => .script attrs code

/-- One reference-list entry: the style's marker, the formatted content,
and the anchor its citations link to. -/
private def bibItemNode (cfg : Config) (item : Ir.BibItem) : Node :=
  let markerNode : Array Node := match item.marker with
    | some m => #[Html.elem "span" #[Html.text s!"[{m}]"]
        #[("class", "bib-marker")], Html.text " "]
    | none => #[]
  Html.elem "li" (markerNode ++ inlines cfg item.content)
    #[("id", Ir.bibAnchor item.key)]

/-- An entry's key enters the artifact only as the `id` attribute of the
typed tree — the anchor `Bib.anchorOf` links to — so it passes
`escapeAttr` by construction (`escapeAttr_no_quote`): a `.bib` key is
author text, and no spelling of one can break out of the attribute. -/
private theorem bibItemNode_key_enters_attribute_position (cfg : Config)
    (item : Ir.BibItem) :
    ∃ kids, bibItemNode cfg item =
      Html.elem "li" kids #[("id", Ir.bibAnchor item.key)] :=
  ⟨_, rfl⟩

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
    let title := match st.font with
      | some tpl => fillTemplate tpl title
      | none => title
    -- The number is a structural piece of the heading, never text glued
    -- into the title: the anchor slug reads the title alone, and a
    -- stylesheet can address the number (`pandoc` sets the same span).
    let kids := inlines cfg title
    let kids := match num with
      | some n => #[Html.elem "span" #[Html.text n]
          #[("class", "section-number")], Html.text "\u2003"] ++ kids
      | none => kids
    Html.elem tag kids (if st.rule.isSome then #[("class", "ruled")] else #[])
  | .list ordered items =>
    let tag := if ordered then "ol" else "ul"
    Html.elem tag (listItemsInto cfg.into #[] items.toList)
  | .center body =>
    Html.elem "div" (blockNodesInto cfg.into #[] body.toList) #[("class", "centered")]
  -- Ragged-left is HTML text's resting state; the class re-declares it so
  -- the setting survives a centred ancestor (text-align inherits).
  | .ragged body =>
    Html.elem "div" (blockNodesInto cfg.into #[] body.toList) #[("class", "ragged")]
  -- The block half of the class hook: the authored name as a class on a
  -- generic flow container, through the typed tree and the escaper.
  | .role n body =>
    Html.elem "div" (blockNodesInto cfg.into #[] body.toList) #[("class", roleClass n)]
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
  -- measure and whose tag sits right, the amsmath shape.
  | .equation num content =>
    let kids := inlines cfg content
    Html.elem "div"
      (kids.push (Html.elem "span" #[Html.text num] #[("class", "eqnum")]))
      #[("class", "equation")]
  -- The abstract is HTML's own titled region: a <section> with a heading,
  -- exactly the thing a reader's tooling looks for. The heading word is
  -- class furniture (article.cls's \abstractname), generated here as the
  -- PDF generates its centred bold line.
  | .abstract body =>
    -- The heading is an <h2>, so a declared `\style{section}` reaches it
    -- through the h2 selector — the abstract follows the section heading
    -- by construction (`Ir.abstract_heading_follows_section`); centred, as
    -- the class centres it (article.cls §abstract).
    Html.elem "section"
      (#[Html.elem "h2" #[Html.text cfg.locale.abstract] #[("style", "text-align: center")]] ++
        blockNodesInto cfg.into #[] body.toList)
      #[("class", "abstract")]
  | .columns cols =>
    -- Side-by-side columns as a grid: the declared fractions become
    -- percentage tracks, so the HTML column really is as wide as the PDF's.
    Html.elem "div" (columnNodesInto cfg.into #[] cols.toList)
      #[("class", "columns"),
        ("style", s!"display: grid; grid-template-columns: {gridTracks cols}; " ++
          "justify-content: space-between; column-gap: 0.75rem")]
  | .step n last body =>
    -- The block form of the inline step arm: visible — the handout floor —
    -- with its `--step` index for the class-gated uncover, range as data.
    Html.elem "div" (blockNodesInto cfg.into #[] body.toList)
      (#[("class", "step"), ("data-step", toString n)] ++
        (match last with
         | some u => #[("data-step-last", toString u)]
         | none => #[]) ++
        #[("style", s!"--step: {n}")])
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
    let style := s!"margin-top: {cssLength before.width}"
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
    let lines := (verbatimLines s).toList
    let codeAttrs : Array (String × String) := match spec.htmlClass with
      | some c => #[("class", c)]
      | none => #[]
    let code :=
      if spec.numbers then
        Html.elem "code" ((lines.map fun l =>
          Html.elem "span" #[Html.text (l ++ "\n")] #[("class", "line")]).toArray) codeAttrs
      else
        Html.elem "code" #[Html.text (String.intercalate "\n" lines)] codeAttrs
    let pre := Html.elem "pre" #[code]
      ((if spec.numbers then #[("class", "numbered")] else #[]) ++
       (match covered with
        | some c => #[("style", s!"color: {cssColor c}")]
        | none => #[]))
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
    -- the PDF paragraphs read too (`algorithm_lines_agree`): keywords
    -- bold, the comment in the muted role. Native list semantics carry
    -- the structure; no role attribute is needed. The build is driven by
    -- each line's own depth — the parse's truth — so an else standing at
    -- its if's level nests exactly once: a deeper line opens levels under
    -- the last item, a shallower one closes them back into it, and the
    -- final unwind makes the builder total (never a lost line).
    let words := Ir.algWords cfg.locale.tag
    let muted := Ir.mutedOf cfg.pal
    Id.run do
      let mut stack : Array (Array Node) := #[#[]]
      let closeOne (stack : Array (Array Node)) : Array (Array Node) := Id.run do
        let inner := stack.back?.getD #[]
        let stack := stack.pop
        let top := stack.back?.getD #[]
        let ol := Html.elem "ol" inner #[]
        let top := match top.back? with
          | some (.elem "li" attrs kids) =>
            (top.pop).push (.elem "li" attrs (kids.push ol))
          | _ => top.push (Html.elem "li" #[ol] #[])
        return (stack.pop).push top
      for l in lines do
        for _ in [0:stack.size + 1] do
          if stack.size > l.depth + 1 then
            stack := closeOne stack
          else break
        for _ in [0:l.depth + 1] do
          if stack.size < l.depth + 1 then
            stack := stack.push #[]
          else break
        let li := Html.elem "li"
          (inlines cfg (Ir.AlgLine.rendered words semis muted l)) #[]
        stack := (stack.pop).push ((stack.back?.getD #[]).push li)
      for _ in [0:stack.size + 1] do
        if stack.size > 1 then
          stack := closeOne stack
        else break
      return Html.elem "ol" (stack.back?.getD #[])
        #[("class", if numbered then "algorithm numbered" else "algorithm")]
  | .rule color name thickness =>
    -- The title page's separator: an <hr> carrying the palette variable,
    -- so a host page can override it as it can any colour.
    let c := match name with
      | some n => s!"var(--{n}, {cssColor color})"
      | none => cssColor color
    Html.elem "hr" #[] #[("class", "separator"),
      ("style", s!"border: none; height: {cssLength thickness.width}; background: {c}")]
  | .frame title standout valign body =>
    -- One slide of the deck: a linear readable section in every class. On
    -- the paged deck (`cfg.deck`) the slide is a flex column the height of
    -- the viewport, and its declared vertical distribution is realized as
    -- two spacers whose flex-grow carries the declared ratio
    -- (`vdistShares`) — glue, exactly as the PDF page distributes its
    -- leftover; in block flow (the print handout, every other class) an
    -- empty div has no height and the declaration rides along inert.
    let header := if title.isEmpty then #[]
      else #[Html.elem "header" #[Html.elem "h2" (inlines cfg title)]]
    let cls := if standout then "slide standout" else "slide"
    let kids := blockNodesInto cfg.into #[] body.toList
    let kids := if cfg.deck then
        let (above, below) := vdistShares valign
        let spacer (n : Nat) : Array Html.Node :=
          if n == 0 then #[] else
            #[Html.elem "div" #[] #[("class", "fill"), ("style", s!"flex-grow: {n}")]]
        let up := spacer above
        let down := spacer below
        up ++ kids ++ down
      else kids
    Html.elem "section" (header ++ kids) #[("class", cls)]
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
  | .picture pic =>
    -- The picture as inline SVG: the same evaluated shapes the PDF paints,
    -- through the typed tree so every label passes the escaper. SVG's y
    -- grows downward, so the transform is the PDF path's: flip against the
    -- box's top. Lengths are pt, the unit the viewBox declares — and in
    -- flow classes the element's own size too: paper is paper. On the
    -- paged deck the stage is the viewport, so the box ships as its
    -- share of the stage instead (`deckStageMilli`, as images do): a pt
    -- box against CSS's 96 dpi ruler was the same "very small picture"
    -- defect. Both shares are stated and the viewBox's own ratio
    -- letterboxes inside them (SVG 2 §8.7, `meet`), so a viewport of
    -- another ratio never distorts the ink.
    let ((px0, py0), (px1, py1)) := pic.bbox
    let w := px1 - px0
    let h := py1 - py0
    let kids := pic.shapes.map fun shape =>
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
        -- The label's inline content inside SVG's <text>: plain text as
        -- character data, math as an italic <tspan> of its source — the
        -- same source-text math this backend ships in prose (native
        -- MathML is what M6 still owes there too), every string through
        -- the escaper by construction.
        let nodes := content.map fun inl =>
          match inl with
          | .math _ src => Html.elem "tspan" #[Html.text src] #[("font-style", "italic")]
          | .formula _ src _ =>
            Html.elem "tspan" #[Html.text src] #[("font-style", "italic")]
          | inl => Html.text (Ir.plainTextOne inl)
        let anchor := match align with
          | .center | .south | .north => "middle"
          | .west => "start"
          | .east => "end"
        let baseline := match align with
          | .center | .west | .east => "central"
          | .south => "text-after-edge"
          | .north => "hanging"
        Html.elem "text" nodes #[
          ("x", (lx - px0).toPtString),
          ("y", (py1 - ly).toPtString),
          ("fill", cssColor color),
          ("font-size", (Ir.baseFontSize * (scale : Int) / 1000).toPtString),
          ("text-anchor", anchor),
          ("dominant-baseline", baseline)]
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
    Html.elem "svg" kids (#[
      ("viewBox", s!"0 0 {w.toPtString} {h.toPtString}")] ++
      (if cfg.deck then
        #[("style", s!"width: {decMilli (deckStageMilli w cfg.page.width)}vw; \
height: {decMilli (deckStageMilli h cfg.page.height)}dvh")]
       else
        #[("width", s!"{w.toPtString}pt"), ("height", s!"{h.toPtString}pt")]) ++ #[
      ("role", "img"),
      ("class", "picture")])
  -- booktabs' formal table: `tableNode` above, where the header projection
  -- theorem (`th_iff_header_row`) can read the row builder.
  | .table cols padL padR rows rules => tableNode cfg cols padL padR rows rules
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
    let cls := match kind with
      | .table => "float table-float"
      | .figure => "float"
      | .sub => "float subfloat"
      | .algorithm => "float algorithm-float"
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
    Html.elem "ul" (items.map (bibItemNode cfg))
      #[("class", if marked then "bibliography" else "bibliography unmarked")]

/-- The accumulator threads through the sibling walk, as in
`inlineNodesInto` — and so does the epoch: a `.setPalette`/`.setTokens`
updates the state in force, and every following sibling carries the
accumulated redefinitions on its style attribute (flow scope realized
sibling-wise; past the enclosing element's close the properties no longer
reach, the documented divergence from the PDF's whole-flow scope). -/
private def blockNodesInto (cfg : Config) (acc : Array Node) : List Block → Array Node
  | [] => acc
  | .logo _ :: rest => blockNodesInto cfg acc rest
  | .setPalette p :: rest =>
    let style := joinStyles cfg.epochStyle (epochPaletteStyle cfg.pal p)
    blockNodesInto { cfg with pal := p, epochStyle := style } acc rest
  | .setTokens tk :: rest =>
    let style := joinStyles cfg.epochStyle (epochTokenStyle cfg.tokens tk)
    blockNodesInto { cfg with tokens := tk, epochStyle := style } acc rest
  | b :: rest =>
    blockNodesInto cfg (acc.push (withEpoch cfg.epochStyle (blockNode cfg b))) rest

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
  | .setPalette p :: rest =>
    let style := joinStyles cfg.epochStyle (epochPaletteStyle cfg.pal p)
    listItem { cfg with pal := p, epochStyle := style } rest
  | .setTokens tk :: rest =>
    let style := joinStyles cfg.epochStyle (epochTokenStyle cfg.tokens tk)
    listItem { cfg with tokens := tk, epochStyle := style } rest
  | b :: rest =>
    blockNodesInto cfg #[withEpoch cfg.epochStyle (blockNode cfg b)] rest

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

/-- The first free anchor among `taken` (`base`, `base-2`, `base-3`, …),
plus the holder's title when a *different* title collides — the W0327
case. k assigned ids can block at most k candidates, so the first free
one is always found among the k+1 checked. One uniqueness rule for every
id this backend assigns: the article's sections and the deck's frames
claim through the same door, which `getElementById` semantics require. -/
private def claimId (taken : Array (String × String)) (base text : String) :
    String × Option String := Id.run do
  let mut id := base
  let mut clash : Option String := none
  for n in [2 : taken.size + 3] do
    match taken.find? (·.1 == id) with
    | some (_, holder) =>
      if holder != text && clash.isNone then
        clash := some holder
      id := s!"{base}-{n}"
    | none => break
  return (id, clash)

/-- The snap spacers of a stepped frame's track, one per overlay step:
each claims its deep-link anchor `<frame>-k` through the same door as
every id this backend assigns (`claimId`), a clash named exactly as a
frame title's is. Recursion over the step list with threaded
accumulators, so the spacer count is a statement
(`track_snaps_exact`), not a reading of a loop. -/
private def snapWalk (id text : String) (kids : Array Node)
    (taken : Array (String × String)) (diags : Array Diag) :
    List Nat → Array Node × Array (String × String) × Array Diag
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
    snapWalk id text
      (kids.push (Html.elem "div" #[]
        #[("class", "snap"), ("id", sid), ("data-snap", "")]))
      (taken.push (sid, text)) diags rest

/-- The steps a frame with `steps` overlay steps snaps through: 1 to
`steps`, the range both the spacer walk and the PDF handout's per-step
pages traverse. -/
private def stepList (steps : Nat) : List Nat :=
  (List.range steps).map (· + 1)

@[simp] private theorem stepList_length (steps : Nat) :
    (stepList steps).length = steps := by
  simp [stepList]

private theorem snapWalk_count (id text : String) :
    ∀ (ks : List Nat) (kids : Array Node) (taken : Array (String × String))
      (diags : Array Diag),
      (snapWalk id text kids taken diags ks).1.size = kids.size + ks.length
  | [], _, _, _ => rfl
  | k :: rest, kids, taken, diags => by
    unfold snapWalk
    rw [snapWalk_count id text rest]
    simp only [Array.size_push, List.length_cons]
    omega

/-- The HTML half of `steps_agree`, stated over `Ir.maxStepBlocks`: a
stepped frame's track carries exactly `maxStepBlocks fb` snap spacers
beside its one sticky stage — the count `deckStepCss` reads back as
`--steps` and the very count the PDF handout paginates the frame by
(its half is the owed `pages_partition_frames`). -/
private theorem track_snaps_exact (id text : String)
    (taken : Array (String × String)) (diags : Array Diag)
    (fb : Array Ir.Block) :
    (snapWalk id text #[] taken diags
        (stepList (Ir.maxStepBlocks fb))).1.size
      = Ir.maxStepBlocks fb := by
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
  let mut taken : Array (String × String) := #[]
  let mut diags : Array Diag := #[]
  -- The epoch state threads through the article's top level exactly as
  -- through `blockNodesInto`: each node after a body declaration carries
  -- the redefinitions, whichever section it closes into.
  let mut cfg := cfg
  for b in blocks do
    match b with
    | .setPalette p =>
      let style := joinStyles cfg.epochStyle (epochPaletteStyle cfg.pal p)
      cfg := { cfg with pal := p, epochStyle := style }
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
      taken := taken.push (id, text)
      openId := some id
      cur := #[withEpoch cfg.epochStyle (blockNode cfg b)]
    | _ => cur := cur.push (withEpoch cfg.epochStyle (blockNode cfg b))
  return (close out cur openId, diags)

/-- A frame's (or section page's) logo, attached as the section's own
furniture: the logo in force at the deck position (`Ir.logoInForce`, the
same resolving site the PDF's furniture pass reads per page) renders into
the `.slide-logo` strip `deckLogoRule` pins to the stage's bottom band.
The logo is decorative furniture by role, so every image inside ships
`alt=""` and the strip is removed from the accessibility tree
(`role="presentation"`, `aria-hidden`) — WCAG 2.2 SC 1.1.1: pure
decoration is implemented so assistive technology can ignore it — the
same judgement the alt census makes (`Ir.logoImageSrcs`). The declared
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
      let deco := Ir.mapInlines (fun x => match x with
        | .image src size _ => .image src size ""
        | x => x) content
      let justify := match Ir.logoAlign cfg.styles with
        | "left" => "flex-start"
        | "center" => "center"
        | _ => "flex-end"
      Node.elem tag attrs (kids.push (Html.elem "div" (inlines cfg deco)
        #[("class", "slide-logo"), ("role", "presentation"),
          ("aria-hidden", "true"),
          ("style", s!"justify-content: {justify}")]))
    | .text s => .text s
    | .style s => .style s
    | .script attrs s => .script attrs s

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
  -- The shipped faces' rules ride exactly where the slot variables ride:
  -- a mode that emits no variables ships no rules, and the driver writes
  -- the files only when it passed the set.
  let faceRules := match cfg.fonts with
    | some fs => fontCss cfg.fontsDir fs
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
    head := head.push (Html.elem "link" #[] #[("rel", "stylesheet"), ("href", href)])
  let bodyClass := match cfg.css with
    | .bulma => "content"
    | _ => ""
  let cfg := { cfg with styles := doc.styles
                        pal := doc.palette
                        tokens := doc.tokens
                        deck := doc.docClass.record.model == .frame
                        page := doc.page }
  -- The themed section page: in a slides document with progress keys, a
  -- top-level section becomes its own deck section carrying the position.
  let themedSections := doc.docClass.record.model == .frame &&
    (Design.ofDoc doc).progress.isSome
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
      -- (`Ir.frameNumbers`, T2–T4). This walk indexes it and counts
      -- nothing, so the two backends cannot disagree.
      let nums := doc.frameNumbers
      let total := doc.frameCount
      let mut done := 0
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
      let mut taken : Array (String × String) := #[]
      -- The epoch state threads through the deck's top level exactly as
      -- through `blockNodesInto`.
      let mut cfg := cfg
      for h : i in [0:doc.body.size] do
        let b := doc.body[i]
        match b with
        | .setPalette p =>
          let style := joinStyles cfg.epochStyle (epochPaletteStyle cfg.pal p)
          cfg := { cfg with pal := p, epochStyle := style }
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
        | .frame title _ _ fb =>
          let num := nums[i]?.getD none
          done := num.getD done
          -- One `section` per frame: the deck's steps reveal *in place*
          -- under the class-gated uncover rules (`deckStepCss`), so the
          -- HTML section count is the frame count — the PDF's page count
          -- less its per-step duplicates (`frames_sections` in Tests;
          -- both counts are projections of `Ir.maxStepBlocks`).
          let node := blockNode cfg b
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
          taken := taken.push (id, text)
          -- The spacer anchors `<frame>-k`, claimed and built by the one
          -- walk whose count is a statement (`track_snaps_exact`); each
          -- spacer carries the `[data-snap]` door, so deep links and the
          -- script's snap list name the same boxes. A stepless frame has
          -- no spacer: its section is its own snap page.
          let steps := Ir.maxStepBlocks fb
          let (spacers, taken2, diags2) :=
            if steps > 1 then
              snapWalk id text #[] taken walkDiags (stepList steps)
            else
              (#[], taken, walkDiags)
          taken := taken2
          walkDiags := diags2
          -- The frame's footer: the chrome band slots (`Ir.Chrome.footBand`,
          -- the same function the PDF's final pass consumes, so the two
          -- backends resolve the same slots and can only diverge by
          -- rendering them; fixed positions from the declared side, paint
          -- order the declared priority, `z-index` carrying `rank`).
          let node := if chromeFoot then
              match num, node with
              | some n, .elem tag attrs kids =>
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
          -- The frame's logo: the state in force at this position, from
          -- the shared fold — one strip inside the section, so a stepped
          -- frame's sticky stage carries it on every snap page, as the
          -- PDF's furniture pass repeats it on every page of the frame.
          let node := attachLogo cfg node (Ir.logoInForce doc.logo logoSpans i)
          -- A stepped frame rides a `.slide-track`: the sticky stage
          -- over its snap spacers (`track_snaps_exact` counts them). The
          -- spacers — static boxes, never the sticky stage — carry the
          -- deck's snap areas through the `[data-snap]` door
          -- (`deckSnapDoor` says why no two areas share an offset), and
          -- the wrapper carries the frame's anchor and `--steps` for the
          -- uncover ranges. A stepless frame is its own snap page: the
          -- section carries the anchor and the door attribute directly.
          let node := if steps > 1 then
              Html.elem "div" (#[node] ++ spacers)
                #[("class", "slide-track"), ("style", s!"--steps: {steps}"),
                  ("id", id)]
            else match node with
              | .elem tag attrs kids =>
                Node.elem tag (attrs ++ #[("id", id), ("data-snap", "")]) kids
              | .text s => Node.text s
              | .style s => Node.style s
              | .script attrs s => Node.script attrs s
          acc := acc.push (withEpoch cfg.epochStyle node)
        | .section 1 starred num title =>
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
            -- A section page is one snap page of the deck like any
            -- stepless frame: the section itself carries the
            -- `[data-snap]` door — and, being a page, the logo state in
            -- force, as the PDF furnishes every page.
            acc := acc.push (withEpoch cfg.epochStyle
              (attachLogo cfg
                (Html.elem "section" kids
                  #[("class", "section-page"), ("data-snap", "")])
                (Ir.logoInForce doc.logo logoSpans i)))
          else
            acc := acc.push (withEpoch cfg.epochStyle
              (blockNode cfg (.section 1 starred num title)))
        | _ => acc := acc.push (withEpoch cfg.epochStyle (blockNode cfg b))
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
  let main := Html.elem "main" inner (if bodyClass.isEmpty then #[]
    else #[("class", bodyClass)])
  -- The headline band: the page's own <header> before <main> (the banner
  -- landmark — the HTML poster is a page, and the band is its header),
  -- title as the one h1, authors and institute as their own lines, the
  -- corner logos in the flex slots the stylesheet lays around the matter.
  let headerNode : Array Node := match doc.headline with
    | some hl =>
      let slot (c : Option (Array Ir.Inline)) : Array Html.Node :=
        match c with
        | some xs =>
          #[Html.elem "div" (inlineNodesInto cfg #[] xs.toList)
            #[("class", "headline-logo")]]
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
  -- The deck's progress hairline, emitted exactly when the deck draws
  -- progress at all (`themedSections`, the section-page gate): an inert
  -- marker div the class-gated stylesheet scales by scroll position.
  if themedSections then
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
  -- <html lang> is the document's declared language (WCAG 2.2 SC 3.1.1;
  -- a hard-coded "en" on a French page is worse than absent — an
  -- actively wrong declaration). The tag ships as declared even when no
  -- locale record backs it: the artifact's declaration and the engine's
  -- data are different questions.
  (Html.document (doc.info.language.getD "en") head body, diags)

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

end LeanTex.Core.HtmlDoc
