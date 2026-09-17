import LeanTex.Core.Diag
import LeanTex.Core.Dim
import LeanTex.Core.Image
import LeanTex.Core.Math

namespace LeanTex.Core.Ir

open LeanTex.Core LeanTex.Core.Dim

/-- The base font size every relative measure hangs off. It lives in the IR
because both backends read it: layout sets body text at this size, and HTML
derives its content measure from the page's text width in these units. -/
def baseFontSize : Sp := Dim.pt 10

/-- Page geometry, as declared by `\page`. -/
structure PageSpec where
  width : Sp := pt 612
  height : Sp := pt 792
  vmargin : Sp := inch 1
  hmargin : Sp := inch 1
  /-- The body size, `\page{ fontsize = 11pt }` or the class option. The
  `slides` class defaults to `slidesFontSize`; everything else to
  `baseFontSize`. -/
  fontSize : Sp := baseFontSize
  /-- Line spacing as a factor over the default 1.2, in thousandths, so
  `\linespread{1.04}` has a home. -/
  leading : Nat := 1000
  /-- The gap between peer paragraphs, with its rubber; `none` is the
  engine's default. LaTeX classes declare `0pt`, `\parskip` and the parskip
  package their own. -/
  parskip : Option SymGlue := none
  /-- Whether the measure is checked against the readable band (W0201).
  `\page{ measure = free }` declares that the document takes responsibility
  for its line length and silences the diagnostic. -/
  measureChecked : Bool := true
  /-- Bleed: how far past the trim edge the physical PDF page extends on
  every side, for print finishing. The page keeps its declared trim size
  here; only the PDF writer grows the medium and records the trim box.
  The print convention is 3 mm per edge (0.125 in at US shops). -/
  bleed : Sp := 0
  /-- Whether paragraphs may hyphenate; `none` takes the class default —
  on for `article` and `slides`, off for `card`, where a two-line name
  broken with a hyphen is never what anyone means. -/
  hyphenate : Option Bool := none
  /-- Whether paragraphs justify; `none` takes the class default. Off for
  `card`: below the 40-character working minimum for justified text
  (Bringhurst), a measure must be set ragged — at card width no line has
  the stretch justification needs, and forcing it gives the breaker only
  overfull answers. -/
  justify : Option Bool := none
  deriving Repr, BEq, Inhabited

/-- The text block of an undeclared letter page: 26 picas (312 pt).
Bringhurst's copy-fitting table sets a text face whose lowercase alphabet
runs 130 pt — the middle of the 10 pt text-face range — on a measure of
about 26 picas for a single column (Elements of Typographic Style §2.1.2
and its table, as abridged in the memoir manual, Table 2.2). The
word-processor inch this replaces gave a 468 pt line, roughly a hundred
characters at 10 pt — the measure the band diagnostic exists to catch. A
document that declares any `\page` geometry keeps every value it named. -/
def articleTextBlock : Sp := pt 312

/-- The slides stage and its defaults, beamer's own where beamer names one:
128×96 mm (the guide's "slides are by default only 128mm by 96mm large"),
160×90 mm at `aspectratio=169`, side text margins of 1 cm ("the left and
right margins, which default to 1 cm"), and an 11 pt base — beamer's
documented default font size, chosen so that "between 10 and 20 lines
should fit on each slide" and it is "difficult to fit too much onto a
slide" (beamer user guide §5.6.1, §18.2.1). The vertical margin is the
engine's own: beamer spends that band on headline and footline templates
the engine does not render. The lines-per-slide theorem in Layout is what
holds these numbers together. -/
def slidesStage43 : Sp × Sp := (Dim.mm 128, Dim.mm 96)
def slidesStage169 : Sp × Sp := (Dim.mm 160, Dim.mm 90)
def slidesHMargin : Sp := Dim.mm 10
def slidesVMargin : Sp := Dim.mm 9
def slidesFontSize : Sp := Dim.pt 11

/-- The card class's legibility floor: an angular x-height of 0.2° at the
40 cm hand-held distance is 1.4 mm, the bound of the fluent-reading range
in Legge & Bigelow 2011. The class implies `text.xheight >=` this;
`card_floor_within_scale` ties it to the size scale. -/
def cardXHeightFloor : Sp := Dim.mm100 140

/-- An sRGB colour. -/
structure Color where
  r : UInt8
  g : UInt8
  b : UInt8
  deriving Repr, BEq, Inhabited

def Color.black : Color := { r := 0, g := 0, b := 0 }

/-- PDF wants components in 0–1; three decimals is finer than 8-bit input. -/
def Color.pdfComponents (c : Color) : String :=
  let f (v : UInt8) : String :=
    let milli := (v.toNat * 1000 + 127) / 255
    if milli == 0 then "0" else if milli == 1000 then "1"
    else
      let frac := toString milli
      let frac := ("".pushn '0' (3 - frac.length)) ++ frac
      "0." ++ (frac.dropEndWhile (· == '0')).toString
  s!"{f c.r} {f c.g} {f c.b}"

/-- Named lengths declared by `\tokens`, in declaration order so a later
token may be defined in terms of an earlier one. -/
structure Tokens where
  entries : Array (String × SymGlue) := #[]
  deriving Repr, BEq, Inhabited

def Tokens.find? (t : Tokens) (name : String) : Option SymGlue :=
  (t.entries.find? (·.1 == name)).map (·.2)

/-- Replace-on-redeclare: a later declaration overrides, keeping one entry
per name. The one install mechanism — a document's `\tokens` and a theme's
bundle go through the same door. -/
def Tokens.declare (t : Tokens) (key : String) (g : SymGlue) : Tokens :=
  { entries := (t.entries.filter (·.1 != key)).push (key, g) }

/-- Named colours declared by `\palette`. -/
structure Palette where
  entries : Array (String × Color) := #[]
  /-- `covered = <n>%`: the fraction of each covered run's own ink over
  the surface — beamer's `\setbeamercovered{transparent=<n>}`, and the
  per-bundle knob the covered contract ranges over. `none` takes
  `coveredFractionDefault`. -/
  coveredFraction : Option Nat := none
  /-- Entries declared under `\palette[decorative]{...}`: deliberately
  low-contrast — a watermark, a dimmed aside — and exempt from the pairing
  diagnostic, the way WCAG 2.2 SC 1.4.3 exempts pure decoration. -/
  decorative : Array String := #[]
  deriving Repr, BEq, Inhabited

def Palette.find? (p : Palette) (name : String) : Option Color :=
  (p.entries.find? (·.1 == name)).map (·.2)

/-- Replace-on-redeclare: a later declaration overrides, keeping one entry
per name. The one install mechanism — a document's `\palette` and a theme's
bundle go through the same door. -/
def Palette.declare (p : Palette) (key : String) (c : Color)
    (decorative : Bool := false) : Palette :=
  { p with
    entries := (p.entries.filter (·.1 != key)).push (key, c)
    decorative := if decorative && !p.decorative.contains key then
        p.decorative.push key
      else p.decorative }

def Color.white : Color := { r := 255, g := 255, b := 255 }

/-- One step of xcolor's `!` mix: `pct`% of `a` over the rest of `b`,
per sRGB channel, rounded. -/
def Color.mix (a : Color) (pct : Nat) (b : Color) : Color :=
  let ch (x y : UInt8) : UInt8 :=
    UInt8.ofNat ((x.toNat * pct + y.toNat * (100 - pct) + 50) / 100)
  { r := ch a.r b.r, g := ch a.g b.g, b := ch a.b b.b }

/-- A palette expression: a name, or xcolor's `!` mix folding left —
`a!30!b` is 30% of `a` over `b`, and a trailing `a!30` mixes toward white,
so `black!2` is a near-white. `black` and `white` are always available;
every other atom resolves against this palette, so `fg!50!bg` names the
document's current foreground and background. -/
def Palette.resolve (p : Palette) (expr : String) : Option Color :=
  let atom (s : String) : Option Color :=
    if s == "black" then some Color.black
    else if s == "white" then some Color.white
    else p.find? s
  let rec go (c : Color) : List String → Option Color
    | [] => some c
    | pctS :: rest =>
      match pctS.toNat? with
      | none => none
      | some pct =>
        if pct > 100 then none
        else match rest with
          | [] => some (c.mix pct Color.white)
          | name :: rest' =>
            match atom name with
            | some b => go (c.mix pct b) rest'
            | none => none
  match (expr.splitOn "!").map (·.trimAscii.toString) with
  | [] => none
  | first :: rest =>
    match atom first with
    | some c => go c rest
    | none => none

/-- Font families a document asks for, as declared by `\fonts`. `dirs` are
directories of font files the document ships, relative to the document, so a
document that carries its fonts renders the same on every host. Every `dir`
declared is kept: fontspec's `Path=` may name a different one per face. -/
structure FontSpec where
  body : Option String := none
  sans : Option String := none
  mono : Option String := none
  /-- The math face (`\fonts{ math = ... }`, fontspec's `\setmathfont`):
  resolved like any named face, and required to carry an OpenType MATH
  table to be used. -/
  math : Option String := none
  dirs : Array String := #[]
  /-- Per-variant faces the document named (fontspec's `UprightFont=`,
  `BoldFont=`, `ItalicFont=`, `BoldItalicFont=`): `(slot, bold, italic)` →
  the face name, resolved like any other named face and winning over the
  family's own variant. -/
  faces : Array ((Nat × Bool × Bool) × String) := #[]
  deriving Repr, BEq, Inhabited

/-- The face the document declared for one slot variant, if any. -/
def FontSpec.faceFor (s : FontSpec) (slot : Nat) (bold italic : Bool) : Option String :=
  (s.faces.find? (·.1 == (slot, bold, italic))).map (·.2)

/-- What to build, as declared by `\output`: the document carries its own
build intent, the way `\documentclass` already does. Names stay strings here
so the core does not know the CLI's option types. -/
structure OutputSpec where
  formats : Array String := #[]
  css : Option String := none
  /-- A stylesheet the HTML page links, resolved by the browser relative to
  the page. `css = none` promised "bring your own stylesheet" but gave the
  document no way to name it; this is that way, and it composes with every
  css mode (the link comes after the inline styles, so the named sheet wins
  ties). -/
  stylesheet : Option String := none
  deriving Repr, BEq, Inhabited

/-- Document metadata, as declared by `\pdfmeta` — the one record every
surface derives from. The PDF reads title/author/subject/keywords into its
Info dictionary and XMP, and `url` into XMP `dc:identifier`; the HTML head
reads all of them plus `image` and `favicon`; the markdown twin reads title
and subject as its llms.txt preamble. `image` and `favicon` are web-surface
facts with no PDF meaning; nothing else here is per-backend. -/
structure Meta where
  title : Option String := none
  author : Option String := none
  subject : Option String := none
  keywords : Option String := none
  /-- The document's canonical URL: `<link rel="canonical">` (RFC 6596) and
  the Open Graph `og:url` in HTML, `dc:identifier` in the PDF's XMP. -/
  url : Option String := none
  /-- A representative image for link previews: `og:image`. -/
  image : Option String := none
  /-- The page icon: `<link rel="icon">`. -/
  favicon : Option String := none
  deriving Repr, BEq, Inhabited

inductive CmpOp where
  | eq
  | ne
  | le
  | lt
  | ge
  | gt
  deriving Repr, BEq, Inhabited

def CmpOp.label : CmpOp → String
  | .eq => "=="
  | .ne => "!="
  | .le => "<="
  | .lt => "<"
  | .ge => ">="
  | .gt => ">"

def CmpOp.holds : CmpOp → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .le, a, b => a ≤ b
  | .lt, a, b => a < b
  | .ge, a, b => a ≥ b
  | .gt, a, b => a > b

/-- A layout invariant the engine checks against what it actually shipped. -/
inductive AssertKind where
  | pages (op : CmpOp) (n : Int)
  | fontsAllEmbedded
  /-- Every piece of ink inside the margins. On a card the margins are the
  print safe zone, so this is "nothing risks the trim". -/
  | textInArea
  /-- The smallest x-height set anywhere is at least this, judged from each
  run's font at its size: the legibility floor is an angular x-height, so
  the check reads the metric the source speaks in. -/
  | minXHeight (min : Sp)
  deriving Repr, BEq, Inhabited

def AssertKind.source : AssertKind → String
  | .pages op n => s!"pages {op.label} {n}"
  | .fontsAllEmbedded => "fonts.all_embedded"
  | .textInArea => "text.in_area"
  | .minXHeight m => s!"text.xheight >= {m.toPtString}pt"

structure Assertion where
  kind : AssertKind
  span : Option Span := none
  /-- Failure guidance. A class-implied assertion says which contract fired
  and how declaring intent takes control of it. -/
  help : Option String := none
  deriving Repr, BEq, Inhabited

inductive Style where
  | bold
  | italic
  | mono
  | smallcaps
  | emph
  | sans
  | normal
  | size (name : String)
  deriving Repr, BEq

/-- The LaTeX 10pt size scale, per mille of the surrounding size. It lives in
the IR because both backends read it: they must agree on what `\Huge` means.

The values are LaTeX's own (`size10.clo`: 5, 7, 8, 9, 10, 12, 14.4, 17.28,
20.74, 24.88 pt), which above `normalsize` is a geometric modular scale of
ratio 1.2 — TeX's `\magstep` — to per-mille rounding, and below it takes the
traditional smaller steps down to the fixed footnote and script sizes. The
theorems after the table are what make it a scale rather than a list of
numbers: it is strictly monotone, every step's ratio stays inside a stated
band, and the display steps really are ×1.2. -/
def sizeScale : List (String × Nat) :=
  [("tiny", 500), ("scriptsize", 700), ("footnotesize", 800), ("small", 900),
   ("normalsize", 1000), ("large", 1200), ("Large", 1440), ("LARGE", 1728),
   ("huge", 2074), ("Huge", 2488)]

/-- Adjacent steps of the scale, in order: what the scale theorems below
quantify over. -/
def sizeScaleSteps : List (Nat × Nat) :=
  (sizeScale.map (·.2)).zip (sizeScale.map (·.2)).tail

/-- The scale is strictly monotone: a larger name is a larger size, so a
document can rank two declared sizes by rank alone. -/
theorem sizeScale_monotone : ∀ p ∈ sizeScaleSteps, p.1 < p.2 := by decide

/-- Every step's ratio lies in [10⁄9, 7⁄5]: no two adjacent sizes collapse
into each other (at least a major second apart) and no step jumps more than
`tiny`'s catch-up to `scriptsize` (a ratio band, the modular-scale property,
stated over the integers). -/
theorem sizeScale_ratio_band :
    ∀ p ∈ sizeScaleSteps, 10 * p.1 ≤ 9 * p.2 ∧ 5 * p.2 ≤ 7 * p.1 := by decide

/-- `normalsize` is the identity: the scale is anchored at the body size. -/
theorem sizeScale_normalsize : sizeScale.lookup "normalsize" = some 1000 := by decide

/-- Above `normalsize` the scale is geometric with ratio 1.2 to per-mille
rounding: each step is `\magstep`'s minor-third ratio, |6a − 5b| ≤ 4‰. -/
theorem sizeScale_display_geometric :
    ∀ p ∈ sizeScaleSteps, 1000 ≤ p.1 →
      6 * p.1 ≤ 5 * p.2 + 4 ∧ 5 * p.2 ≤ 6 * p.1 + 4 := by decide

/-- The card's contract and the type scale agree at the card's own base
size: at the conventional x-height ratio (half the nominal size, the
fallback the shipped-ink judge uses for a font that declares none), every
scale step from `footnotesize` up clears the 1.4 mm legibility floor the
class implies — the class never states an assertion its own defaults
violate, and what fails (`scriptsize`, `tiny`) is exactly what the
assertion exists to catch on the shipped pages. -/
theorem card_floor_within_scale :
    ∀ p ∈ sizeScale, 800 ≤ p.2 →
      baseFontSize * (p.2 : Int) / 1000 / 2 ≥ cardXHeightFloor := by decide

def Style.label : Style → String
  | .bold => "bold"
  | .italic => "italic"
  | .mono => "mono"
  | .smallcaps => "smallcaps"
  | .emph => "emph"
  | .sans => "sans"
  | .normal => "normal"
  | .size n => s!"size:{n}"

inductive Inline where
  | text (s : String)
  | math (display : Bool) (src : String)
  /-- An elaborated formula: atoms with TeX's classes and scripts, ready to
  measure against a MATH face. `src` is carried whole so the HTML backend's
  boundary emission and every plain-text reading stay exactly what `.math`
  gives them — a formula's meaning lives in `body`, its spelling in `src`.
  Math the elaborator cannot yet model stays `.math`, warned by name. -/
  | formula (display : Bool) (src : String) (body : Math.MList)
  | styled (style : Style) (body : Array Inline)
  /-- `name` is the palette entry this came from, when it had one, so the
  HTML backend can emit `var(--name)` and let a host page override it. -/
  | colored (color : Color) (name : Option String) (body : Array Inline)
  /-- `\href{url}{body}`: a hyperlink. Becomes an `<a>` in HTML and a Link
  annotation in PDF, so the URL rides the IR rather than a backend. -/
  | link (url : String) (body : Array Inline)
  /-- `\underline{...}`: a drawn decoration, not a face change, so it is not a
  `Style`. Both backends interrupt the rule where a descender crosses it. -/
  | underline (body : Array Inline)
  /-- `\hfill`: stretch that pushes what follows to the far margin. -/
  | fill
  /-- Running-content placeholders, resolved once page count is known. -/
  | pageNumber
  | pageCount
  /-- `\\`, carrying LaTeX's optional extra space: `\\[1ex]`. -/
  | linebreak (extra : SymGlue)
  /-- Overlay content crisp on steps `n` through `last` (`\uncover<2>`,
  `<2->` when `last` is `none`, `<2-3>`): outside its range it dims, never
  hides, so no step reflows the slide (PLAN M5). Zero metric impact — a
  pure grouping both backends may recolor or tag. -/
  | step (n : Nat) (last : Option Nat) (body : Array Inline)
  /-- An external image (`\includegraphics`, and what a `figure` or a deck
  logo reduces to): a box of raster content. `src` is the path as written —
  the file itself is the driver's effect, surfaced through `imageRefs` and
  fulfilled as an `Image.Store` — and `alt` is the accessible text (a
  figure's caption), for the HTML backend. -/
  | image (src : String) (size : Image.SizeSpec) (alt : String)
  deriving Repr, BEq, Inhabited

/-- How a frame distributes its leftover vertical space: beamer's frame
options `[t]`/`[c]`/`[b]` on `\begin{frame}`. `center` is beamer's default
(user guide §8.1: the `c` option "is the default behavior"). `golden` is
the title page's declaration — moloch's golden-ratio glue — and only
`\maketitle` produces it: a golden frame is the title page, whose content
is display furniture. -/
inductive VAlign where
  | top
  | center
  | bottom
  | golden
  deriving Repr, BEq, Inhabited

inductive Block where
  | para (content : Array Inline)
  | section (level : Nat) (starred : Bool) (title : Array Inline)
  | list (ordered : Bool) (items : Array (Array Block))
  | center (body : Array Block)
  /-- `\block[before = <len>]{...}`: content with declared space above. -/
  | spaced (before : SymGlue) (body : Array Block)
  /-- `{quote}`/`{quotation}`: a quotation set off from the text by
  indenting both margins by the list indent — classes.dtx defines both as
  `\list{}{\rightmargin\leftmargin}`, so the right edge moves in exactly as
  far as the left. The two environments differ only in
  `\listparindent` (`quotation` indents each paragraph's first line
  1.5 em); the engine sets no paragraph indent anywhere yet, so that
  distinction has nothing to bind to and one node carries both. HTML sets
  it as `<blockquote>`, markdown as `> ` lines. -/
  | quote (body : Array Block)
  /-- `{verbatim}` content, kept literally: lines, spaces, and all. Both
  backends set it in the mono face and neither reflows it. `covered` is the
  dim colour painted by the overlay shade — code pending its step must read
  as covered like any other text; `none` everywhere else. -/
  | verbatim (covered : Option Color) (content : String)
  /-- Side-by-side columns (`{columns}`/`{column}`): each column carries its
  declared width as per mille of the text width, or `none` to share the
  leftover equally. Columns are top-aligned; the alignment options and
  absolute widths are not modelled (PLAN, M5). -/
  | columns (cols : Array (Option Nat × Array Block))
  /-- Overlay blocks crisp on steps `n` through `last` (`\item<2->`,
  `\pause`): the block form of `Inline.step`, with the same dim-not-hide
  semantics. -/
  | step (n : Nat) (last : Option Nat) (body : Array Block)
  /-- A speaker note (`\note{...}`): a side channel, never slide content.
  The PDF handout omits it; HTML keeps it as an inert hidden aside for the
  coming speaker view (PLAN M5). -/
  | note (body : Array Block)
  /-- `{ifbackend}{html,md}`: content addressed to a subset of the backends
  (`backendNames`). The engine elaborates once and emits several backends
  from one IR, so the conditional cannot resolve at elaboration: the node
  carries its target set and each backend keeps or drops it (`keepFor`,
  applied with the backend's own name at each emitter's entry). Elaboration
  diagnoses a target set that no backend answers along its nesting path
  (W0324), and `keepFor_covers` is the conservation theorem that makes the
  diagnostic sufficient: with every conditional answered, no declared text
  leaf is dropped by every backend. -/
  | only (targets : Array String) (body : Array Block)
  /-- `{nav}`: a navigation landmark — a group of links for page or site
  navigation, not a widget. HTML emits it as the `<nav>` element (the
  `navigation` landmark, W3C ARIA Authoring Practices, Landmark Regions);
  the PDF page and the markdown twin have no landmark to mark, so both keep
  the body as a transparent group. -/
  | nav (body : Array Block)
  /-- beamer's `\logo`, met in the body: a stateful declaration — the pages
  from here on carry this content at their lower-right corner, and an empty
  content clears it (`\logo{}` after a frame is how a deck scopes a logo to
  one frame). The preamble form is `Doc.logo`, the initial state. -/
  | logo (content : Array Inline)
  /-- One slide. First-class and never flattened into article paragraphs:
  HTML makes it a `<section>` of the deck, the PDF handout gives it a page.
  An empty title is a bare frame. `standout` is beamer's `[standout]`: the
  frame inverts (`standoutfg` on `standoutbg`, defaulting to the inverse of
  the page), centres, and sets Large bold. `valign` is the frame's declared
  vertical distribution (`[t]`/`[c]`/`[b]`; `center` unless declared). -/
  | frame (title : Array Inline) (standout : Bool) (valign : VAlign) (body : Array Block)
  /-- `\framefoot{...}` (beamer's `frame footer` template): the footer note
  the frames from here on carry in the chrome footer's left slot, beside
  the frame number. Empty content clears it back to the chrome default. -/
  | framefoot (content : Array Inline)
  /-- A full-measure horizontal rule: the title page's separator. `name` is
  the palette entry the colour came from, when it had one, as `.colored`;
  the thickness is symbolic so a token may state it in em. -/
  | rule (color : Color) (name : Option String) (thickness : SymGlue)
  deriving Repr, BEq, Inhabited

/-- The frames the deck numbers: a `.frame` that is neither standout nor
golden. Only `\maketitle` produces `.golden`, and moloch's `\maketitle` is
`\frame[plain,noframenumbering]{\titlepage}` (beamerinnerthememoloch.dtx:314-320);
its standout frames are likewise `noframenumbering` (:777-778). beamer's
`noframenumbering` does not advance the frame counter (user guide §8.1), so
the k-th countable frame in document order bears number k — the fold below —
and a non-countable frame bears none. -/
def Block.countable : Block → Bool
  | .frame _ standout valign _ => !standout && !(valign matches .golden)
  | _ => false

/-- Count of `true` in a mask: the numbering's denominator. -/
def countTrue : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + countTrue rest

/-- The numbering fold: masked positions take k+1, k+2, …; the rest take
none. One definition site for every frame number the engine ever shows —
both backends read this array, and nothing else counts. -/
def numbersFrom (k : Nat) : List Bool → List (Option Nat)
  | [] => []
  | b :: rest =>
    if b then some (k + 1) :: numbersFrom (k + 1) rest
    else none :: numbersFrom k rest

/-- The somes of the fold are exactly `1..countTrue`: the numbering is
monotone and gapless, whatever the mask. -/
theorem numbers_gapless (k : Nat) (bs : List Bool) :
    (numbersFrom k bs).filterMap id = List.range' (k + 1) (countTrue bs) := by
  induction bs generalizing k with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | false => simp [numbersFrom, countTrue, ih]
    | true =>
      have h1 : countTrue (true :: rest) = countTrue rest + 1 := by
        simp [countTrue, Nat.add_comm]
      rw [h1]
      simp [numbersFrom, ih, List.range'_succ]

/-- Every assigned number is ≤ the total: a progress clamp is dead code. -/
theorem numbers_le_total (bs : List Bool) (n : Nat)
    (h : n ∈ (numbersFrom 0 bs).filterMap id) : n ≤ countTrue bs := by
  rw [numbers_gapless] at h
  have := List.mem_range'.mp h
  omega

/-- The last number is the total: the denominator is reached. -/
theorem last_number_is_total (bs : List Bool) (h : 0 < countTrue bs) :
    ((numbersFrom 0 bs).filterMap id).getLast? = some (countTrue bs) := by
  obtain ⟨m, hm⟩ : ∃ m, countTrue bs = m + 1 :=
    ⟨countTrue bs - 1, (Nat.succ_pred_eq_of_pos h).symm⟩
  rw [numbers_gapless, hm, List.range'_concat, List.getLast?_concat]
  exact congrArg some (by omega)

/-- A position is numbered exactly when its mask bit is set. -/
theorem numbersFrom_isSome (k : Nat) (bs : List Bool) (i : Nat) :
    ((numbersFrom k bs)[i]?.getD none).isSome = (bs[i]?.getD false) := by
  induction bs generalizing k i with
  | nil => rfl
  | cons b rest ih =>
    cases i with
    | zero => cases b <;> simp [numbersFrom]
    | succ n => cases b <;> simp [numbersFrom, ih]

theorem numbersFrom_length (k : Nat) (bs : List Bool) :
    (numbersFrom k bs).length = bs.length := by
  induction bs generalizing k with
  | nil => rfl
  | cons b rest ih => cases b <;> simp [numbersFrom, ih]

/-- The countable mask of a document body: the fold's instantiation. -/
def frameMask (body : Array Block) : List Bool :=
  body.toList.map Block.countable

/-- The frame number each top-level block bears: `some k` for the k-th
countable frame, `none` for everything else. THE numbering — the chrome
footer, the progress bar, and the HTML deck all index this array; a new
count consumer reads it, never counts for itself. -/
def frameNumbers (body : Array Block) : Array (Option Nat) :=
  (numbersFrom 0 (frameMask body)).toArray

/-- The numbering's denominator: how many countable frames the body has. -/
def frameCount (body : Array Block) : Nat :=
  countTrue (frameMask body)

/-- T2, numbered iff countable: position i bears a number exactly when
block i is a countable frame. -/
theorem frameNumbers_numbered_iff_countable (body : Array Block) (i : Nat) :
    ((frameNumbers body)[i]?.getD none).isSome =
      ((body[i]?.map Block.countable).getD false) := by
  have h := numbersFrom_isSome 0 (frameMask body) i
  simpa [frameNumbers, frameMask, List.getElem?_map] using h

/-- T3, monotone and gapless: the numbers assigned, in document order, are
exactly `1, 2, …, frameCount`. -/
theorem frameNumbers_gapless (body : Array Block) :
    (frameNumbers body).toList.filterMap id =
      List.range' 1 (frameCount body) := by
  simpa [frameNumbers, frameCount] using numbers_gapless 0 (frameMask body)

/-- T4a: every number the engine can show is ≤ the denominator — the
`min`/`max` clamps around a progress fraction cannot fire. -/
theorem frameNumbers_le_count (body : Array Block) (n : Nat)
    (h : n ∈ (frameNumbers body).toList.filterMap id) : n ≤ frameCount body := by
  exact numbers_le_total (frameMask body) n (by simpa [frameNumbers] using h)

/-- T4b: the denominator is reached — the last numbered frame bears
`frameCount` itself, so a full deck ends at n/n, never n−1/n. -/
theorem frameNumbers_last_is_count (body : Array Block)
    (h : 0 < frameCount body) :
    ((frameNumbers body).toList.filterMap id).getLast? =
      some (frameCount body) := by
  simpa [frameNumbers, frameCount] using
    last_number_is_total (frameMask body) (by simpa [frameCount] using h)

theorem frameNumbers_size (body : Array Block) :
    (frameNumbers body).size = body.size := by
  simp [frameNumbers, frameMask, numbersFrom_length]

/-- Verbatim content, line-split: the newline after `\begin{verbatim}` and
the blank tail before `\end{verbatim}` delimit — every trailing blank line
goes, not one — and everything between is content, interior blank lines
included. -/
def verbatimLines (s : String) : Array String := Id.run do
  let s := if s.startsWith "\n" then (s.drop 1).toString
    else if s.startsWith "\r\n" then (s.drop 2).toString else s
  let mut lines := ((s.splitOn "\n").map fun l =>
    if l.endsWith "\r" then (l.dropEnd 1).toString else l).toArray
  repeat
    match lines.back? with
    | some last => if last.trimAscii.isEmpty then lines := lines.pop else break
    | none => break
  return lines

/-- Verbatim content as inline text, for a backend that sets lines rather
than reading the string whole: spaces become no-break spaces so indentation
survives layout as fixed kerns, lines join by forced breaks, and a blank line
keeps one no-break space so the break before it still sets a line. -/
def verbatimInlines (s : String) : Array Inline := Id.run do
  let mut out : Array Inline := #[]
  for line in verbatimLines s do
    unless out.isEmpty do
      out := out.push (.linebreak {})
    let kept := line.foldl (fun acc c => acc.push (if c == ' ' then '\u00a0' else c)) ""
    out := out.push (.text (if kept.isEmpty then "\u00a0" else kept))
  return out

/-- How an element kind looks, from `\style{element}{...}`. Every field a
backend used to hard-code is here instead, so a design lives in the document.
`font` is a template: the inline wrappers a declaration like
`{\large\sffamily\bfseries\primary}` elaborates to, with an empty body where
the element's own content goes. -/
structure ElementStyle where
  font : Option (Array Inline) := none
  before : Option SymGlue := none
  after : Option SymGlue := none
  /-- A rule filling the rest of the heading's line, in this palette colour. -/
  rule : Option (Color × Option String) := none
  /-- List marker content, replacing the level's class-default marker. -/
  marker : Option (Array Inline) := none
  indent : Option SymGlue := none
  /-- Space between list items. -/
  gap : Option SymGlue := none
  /-- Horizontal alignment of the element's lines: `left`, `center`, or
  `right`. The title page reads it (moloch sets its title matter ragged
  left; undeclared, a title page centres). -/
  align : Option String := none
  /-- A full-measure rule after the element's leading part, in this palette
  colour: the moloch title separator between the title block and the
  author block. -/
  separator : Option (Color × Option String) := none
  /-- Interaction states, read by the HTML backend only — a printed page
  has no hover or focus, so the PDF path ignores all three keys (said once
  here, not per consumer). `hover` and `focus` colour the element's links
  in that state, the same value shape as `rule`; `motion` is the duration,
  in milliseconds, of the transition between those states, and its CSS
  always ships inside its own `prefers-reduced-motion` guard
  (`HtmlDoc.motionCss`, WCAG 2.2 SC 2.3.3). -/
  hover : Option (Color × Option String) := none
  focus : Option (Color × Option String) := none
  motion : Option Nat := none
  deriving Repr, BEq, Inhabited

/-- Elements a document may style. Section levels are `section`, `subsection`,
`subsubsection`; lists are `itemize` and `enumerate` — those two style every
nesting level, and `itemize2`..`itemize4` / `enumerate2`..`enumerate4`
override one level, the way `\labelitemii` or `\setlist[itemize,2]` does;
`frametitle`, `sectionpage`, `standout`, and `titlepage` are the slides
furniture (their `font` is read; `titlepage` also reads `align` and
`separator`; the other keys have no meaning there yet). -/
def styleableElements : List String :=
  ["section", "subsection", "subsubsection", "itemize", "enumerate",
   "itemize2", "itemize3", "itemize4", "enumerate2", "enumerate3", "enumerate4",
   "frametitle", "sectionpage", "standout", "titlepage", "nav"]

structure Styles where
  entries : Array (String × ElementStyle) := #[]
  deriving Repr, BEq, Inhabited

def Styles.find? (s : Styles) (element : String) : Option ElementStyle :=
  (s.entries.find? (·.1 == element)).map (·.2)

/-- Replace-on-redeclare, one entry per element — the same install mechanism
as `Palette.declare`/`Tokens.declare`. A `\style` block edits keys of the
element's existing entry first; what is declared here is the whole record. -/
def Styles.declare (s : Styles) (element : String) (st : ElementStyle) : Styles :=
  { entries := (s.entries.filter (·.1 != element)).push (element, st) }

/-- What a chrome footer slot shows, resolved per page by the backends: the
title of the current top-level section, or the index of the page's own frame
(one number for all pages of a stepped frame). Data, not content: a theme
names the datum and the engine supplies the value, so a bundle stays a table
and no backend learns a theme's name. -/
inductive ChromeSlot where
  | sectionTitle
  | frameNumber
  /-- The `n / N` form: moloch's `numbering=fraction`, beamer's
  `[totalframenumber]` template (beamerouterthememoloch.dtx:156-188). -/
  | frameFraction
  deriving Repr, BEq, Inhabited

def ChromeSlot.label : ChromeSlot → String
  | .sectionTitle => "sectiontitle"
  | .frameNumber => "framenumber"
  | .frameFraction => "framefraction"

/-- The declared priority of a slot datum, the order that decides which slot
yields when two boxes collide: the frame number is low — it yields to the
section title, never the reverse (the user's design rule for this engine:
positions are fixed, and on a collision the number "can be painted over,
since [the] page number is lower priority"; a printed folio behaves the same
way — fixed position, yielded by, never yielding to, the text). Distinct
values by construction (`priority_injective`), so between two declared data
"which one yields" is a fact of the declaration, never an accident of
evaluation order. -/
def ChromeSlot.priority : ChromeSlot → Nat
  | .frameNumber => 0
  | .frameFraction => 1
  | .sectionTitle => 2

theorem ChromeSlot.priority_injective : ∀ a b : ChromeSlot,
    a.priority = b.priority → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [priority]

/-- A `\framefoot` note is the author's own content: it outranks every
furniture datum. -/
def notePriority : Nat := 3

/-- Which side of a furniture band a slot occupies. The position is the
declaration; a band holds at most one slot per side. -/
inductive BandSide where
  | left
  | right
  deriving Repr, BEq, DecidableEq, Inhabited

def BandSide.idx : BandSide → Nat
  | .left => 0
  | .right => 1

/-- One slot of a furniture band, as both backends consume it: the declared
side, the resolved content, and the declared priority. A band slot always
ships ink — an empty slot is absent from the band, not a case its
neighbours see. -/
structure BandSlot where
  side : BandSide
  content : Array Inline
  priority : Nat
  label : String
  deriving Repr, BEq, Inhabited

/-- The band's paint order: declared priority first, side as the tiebreak.
Over a band's slots this order is total with no ties — a band holds one
slot per side (`rank_ne_of_side_ne`) — so the slot painted under, the one
that yields on a collision, is a fact of the declaration. -/
def BandSlot.rank (s : BandSlot) : Nat := 2 * s.priority + s.side.idx

theorem BandSlot.rank_ne_of_side_ne (a b : BandSlot) (h : a.side ≠ b.side) :
    a.rank ≠ b.rank := by
  cases ha : a.side <;> cases hb : b.side <;>
    simp_all [rank, BandSide.idx] <;> omega

/-- The one place a frame number becomes text: both backends resolve a
footer slot through this function, so the number's format is a datum of the
IR and neither backend carries a format literal. `n` is the frame's own
number off `frameNumbers`, `total` the count. `sectionTitle` is content,
not a number — the caller passes the section in force. The physical
`\pagenumber`/`\pagecount` are the other, deliberately separate sequence,
rendered only by `substPage`. -/
def ChromeSlot.render (s : ChromeSlot) (sectionTitle : Array Inline)
    (n total : Nat) : Array Inline :=
  match s with
  | .sectionTitle => sectionTitle
  | .frameNumber => #[.text (toString n)]
  | .frameFraction => #[.text s!"{n} / {total}"]

/-- Page furniture a theme (or the document, via `\chrome`) declares: the
slide footer's two slots. A document's own `\runningfoot` overrides the
whole footer; a slot left undeclared is empty. Redeclaring `\chrome`
replaces, as `\palette` and `\tokens` do, so a theme stays a default. -/
structure Chrome where
  footerLeft : Option ChromeSlot := none
  footerRight : Option ChromeSlot := none
  deriving Repr, BEq, Inhabited

def Chrome.hasFooter (c : Chrome) : Bool :=
  c.footerLeft.isSome || c.footerRight.isSome

/-- The footline's slot layout, resolved once for both backends: the left
slot — a `\framefoot` note in force, else the declared left datum — and the
right slot. The layout is moloch's own footline template
(beamerouterthememoloch.dtx:216-228, `\defbeamertemplate{footline}{plain}`):
`\usebeamertemplate*{frame footer}` `\hfill` `\usebeamertemplate*{page number
in head/foot}` — left slot, stretch, right slot, and the `\hfill` stands
whether or not the left template is empty, so an empty left slot never moves
the right slot off the right edge. Both backends consume this function and
neither carries its own slot arithmetic; which side a slot renders on is
thereby a function of the declaration alone (`footSlots_right_ignores_left`,
`footSlots_left_ignores_right`). -/
def Chrome.footSlots (c : Chrome) (frameFoot : Option (Array Inline))
    (sectionTitle : Array Inline) (n total : Nat) :
    Array Inline × Array Inline :=
  let slot (s : ChromeSlot) : Array Inline := s.render sectionTitle n total
  let left := match frameFoot with
    | some xs => xs
    | none => (c.footerLeft.map slot).getD #[]
  (left, (c.footerRight.map slot).getD #[])

/-- One band slot when its content ships ink, none when it is empty: an
absent slot is how "the empty left slot" stops being a case at all. -/
def bandSlotIf (side : BandSide) (content : Array Inline)
    (priority : Nat) (label : String) : Array BandSlot :=
  if content.isEmpty then #[] else #[{ side, content, priority, label }]

theorem mem_bandSlotIf {s : BandSlot} {side : BandSide}
    {content : Array Inline} {priority : Nat} {label : String}
    (h : s ∈ bandSlotIf side content priority label) :
    s.side = side ∧ s.content = content := by
  unfold bandSlotIf at h
  split at h
  · simp at h
  · simp only [Array.mem_singleton] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- The footline as a band of slots, the one object both backends consume:
each slot carries its declared side, its content resolved by `footSlots`
(the band never re-resolves), and its declared priority. Positions are the
layout's, fixed per side (`Layout.bandSlotX`) — never derived from content —
and on a collision the lower-rank slot yields by paint order, reported by
name (W0333). -/
def Chrome.footBand (c : Chrome) (frameFoot : Option (Array Inline))
    (sectionTitle : Array Inline) (n total : Nat) : Array BandSlot :=
  let (left, right) := c.footSlots frameFoot sectionTitle n total
  let (lp, ll) := match frameFoot, c.footerLeft with
    | some _, _ => (notePriority, "the \\framefoot note")
    | none, some s => (s.priority, s.label)
    | none, none => (0, "")
  bandSlotIf .left left lp ll ++
    bandSlotIf .right right ((c.footerRight.map (·.priority)).getD 0)
      ((c.footerRight.map (·.label)).getD "")

/-- The band is a projection of the one slot pair: a left band slot's
content is the pair's left component, a right one's the right — so the
backends can only diverge by rendering the same pair, never by resolving
different pairs (the role `footLine_eq_slots` played for the deleted
one-line rendering). -/
theorem Chrome.footBand_projects (c : Chrome) (ff : Option (Array Inline))
    (sec : Array Inline) (n total : Nat) {s : BandSlot}
    (h : s ∈ c.footBand ff sec n total) :
    (s.side = .left ∧ s.content = (c.footSlots ff sec n total).1) ∨
    (s.side = .right ∧ s.content = (c.footSlots ff sec n total).2) := by
  unfold footBand at h
  rw [Array.mem_append] at h
  rcases h with h | h
  · exact .inl (mem_bandSlotIf h)
  · exact .inr (mem_bandSlotIf h)

/-- A band's inline content read left to right — the reading order, as
distinct from the paint order (`BandSlot.rank`). -/
def bandInlines (b : Array BandSlot) : Array Inline :=
  (b.filter (·.side == .left) ++ b.filter (·.side == .right)).flatMap
    (·.content)

/-- The right slot is a function of its own declaration: neither the left
slot's declaration nor a `\framefoot` note in force can move or change it —
the empty-left case cannot move the number. -/
theorem Chrome.footSlots_right_ignores_left (c c' : Chrome)
    (ff ff' : Option (Array Inline)) (sec : Array Inline) (n total : Nat)
    (h : c.footerRight = c'.footerRight) :
    (c.footSlots ff sec n total).2 = (c'.footSlots ff' sec n total).2 := by
  simp [footSlots, h]

/-- And the left slot of its own: the right slot's declaration never reaches
it. -/
theorem Chrome.footSlots_left_ignores_right (c c' : Chrome)
    (ff : Option (Array Inline)) (sec : Array Inline) (n total : Nat)
    (h : c.footerLeft = c'.footerLeft) :
    (c.footSlots ff sec n total).1 = (c'.footSlots ff sec n total).1 := by
  simp [footSlots, h]

mutual

/-- The walk of `fillTemplate`. Exhaustive over `Inline` by design: any
body-carrying wrapper may hold the template's hole, and a leaf carries no
body to fill. A new constructor must answer here or the build breaks —
never add a wildcard arm (AGENTS.md, the obligation table). -/
def fillOne (content : Array Inline) : Inline → Inline
  | .styled st body =>
    .styled st (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .colored c n body =>
    .colored c n (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .underline body =>
    .underline (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .link u body =>
    .link u (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .step n last body =>
    .step n last (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .text s => .text s
  | .math d src => .math d src
  -- a formula's body is math atoms, an image carries no inline body:
  -- neither can hold the template's hole
  | .formula d src body => .formula d src body
  | .image src size alt => .image src size alt
  | .fill => .fill
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak e => .linebreak e

def fillList (content : Array Inline) : List Inline → List Inline
  | [] => []
  | x :: rest => fillOne content x :: fillList content rest

end

/-- Fill a font template's hole with content. The hole is the innermost empty
body; a template with no hole (plain content) is returned unchanged, which
is what a marker is. -/
def fillTemplate (template content : Array Inline) : Array Inline :=
  if template.isEmpty then content else (fillList content template.toList).toArray

structure Doc where
  docClass : String := "article"
  classOptions : String := ""
  page : PageSpec := {}
  fonts : FontSpec := {}
  palette : Palette := {}
  tokens : Tokens := {}
  /-- `\runninghead` / `\runningfoot`: one line of inline content each, laid
  out in the margin after the body, when the page count is known. -/
  head : Option (Array Inline) := none
  foot : Option (Array Inline) := none
  /-- beamer's `\logo`: one piece of inline content — normally an image —
  placed at the lower-right corner of every page carrying running content,
  the way the head and foot are placed. -/
  logo : Option (Array Inline) := none
  /-- First page that carries running content; `\thispagestyle{empty}` on the
  opening page is `2`. -/
  runningFrom : Nat := 1
  /-- Slide chrome: the themed default footer's slots. `foot` wins over it. -/
  chrome : Chrome := {}
  /-- Whether the document itself declared `\chrome` (not a theme installing
  its default): the author who names the footer's slots has declared what
  the band holds, so mixing the frame sequence with the physical one there
  is said, not silent (`footerSequenceDiags`). -/
  chromeDeclared : Bool := false
  styles : Styles := {}
  info : Meta := {}
  output : OutputSpec := {}
  asserts : Array Assertion := #[]
  /-- `\allow{W0307, ...}`: diagnostic codes whose losses this document
  accepts. The driver downgrades those errors to warnings and always prints
  the acceptance, so it is declared and visible, never ambient. -/
  allow : Array String := #[]
  body : Array Block := #[]
  deriving Repr, BEq, Inhabited

/-- The document's one frame numbering (T2–T4 hold over it). -/
def Doc.frameNumbers (doc : Doc) : Array (Option Nat) :=
  Ir.frameNumbers doc.body

/-- The numbering's denominator for the document. -/
def Doc.frameCount (doc : Doc) : Nat :=
  Ir.frameCount doc.body

/-- Render a symbolic glue the way it was declared, so goldens show intent
rather than a resolved number. -/
def dumpGlue (g : SymGlue) : String :=
  let part (l : Length) : String :=
    let bits := (if l.sp != 0 then [s!"{l.sp.toPtString}pt"] else []) ++
      (if l.em != 0 then [s!"{l.em}/1000em"] else []) ++
      (if l.ex != 0 then [s!"{l.ex}/1000ex"] else [])
    if bits.isEmpty then "0" else String.intercalate "+" bits
  let base := part g.width
  let plus := if g.stretch == ({} : Length) then "" else s!" plus {part g.stretch}"
  let minus := if g.shrink == ({} : Length) then "" else s!" minus {part g.shrink}"
  base ++ plus ++ minus

private def hex2 (v : UInt8) : String :=
  let d := "0123456789ABCDEF".toList
  String.ofList [d[v.toNat / 16]!, d[v.toNat % 16]!]

-- Display-only printers. Structural recursion through `List`, so no `partial`.

mutual

/-- The characters of inline content with every mark stripped: what a URL or
a palette key built from a parameter is worth as text. -/
def plainText (xs : Array Inline) : String :=
  plainTextList xs.toList

def plainTextList (xs : List Inline) : String :=
  match xs with
  | [] => ""
  | x :: rest => plainTextOne x ++ plainTextList rest

def plainTextOne (x : Inline) : String :=
  match x with
  | .text s => s
  | .math _ src => src
  | .formula _ src _ => src
  | .styled _ body => plainTextList body.toList
  | .colored _ _ body => plainTextList body.toList
  | .link _ body => plainTextList body.toList
  | .underline body => plainTextList body.toList
  | .step _ _ body => plainTextList body.toList
  | .fill | .pageNumber | .pageCount => ""
  | .image _ _ _ => ""
  | .linebreak _ => " "

end

/-- A step's range as the surface spells it: `step 2`, `step 2-3`, and
`step 2-2` for `<2->`, `<2-3>`, and `<2>`. -/
def dumpStepRange (n : Nat) (last : Option Nat) : String :=
  match last with
  | some u => s!"step {n}-{u}"
  | none => s!"step {n}"

mutual

/-- One line of a formula's structure, for the IR dump: every atom's class,
scalar, and scripts, so a golden pins exactly what elaboration decided.
`ord:𝑥^{ord:2} bin:+ ord:𝑦` reads as it sets. The accumulator threads
through the walk, as every structural printer here does. -/
def dumpMathItem (acc : String) (x : Math.MItem) : String :=
  match x with
  | .atom cls nuc sup sub lim =>
    let acc := acc ++ s!"{cls.label}:" ++ (if lim then "lim:" else "")
    dumpMathSub (dumpMathSup (dumpMathNucleus acc nuc) sup) sub
  | .space mu => acc ++ s!"mu:{mu}"

def dumpMathNucleus (acc : String) (n : Math.MNucleus) : String :=
  match n with
  | .sym c => acc.push c
  | .word s => acc ++ s.quote
  | .list body => (dumpMathList (acc.push '{') body).push '}'
  | .frac num den =>
    ((dumpMathList (acc ++ "frac{") num ++ "}{" |> fun a =>
      dumpMathList a den)).push '}'
  | .rad deg body =>
    let acc := match deg with
      | .nil => acc ++ "sqrt"
      | _ => (dumpMathList (acc ++ "sqrt[") deg) ++ "]"
    (dumpMathList (acc.push '{') body).push '}'
  | .delim l r body =>
    let name (c : Option Char) : String := match c with
      | some c => String.ofList [c]
      | none => "."
    (dumpMathList (acc ++ s!"left{name l}\{") body) ++ s!"}right{name r}"
  | .grid kind rows =>
    let tag := match kind with
      | .align => "align"
      | .gather => "gather"
      | .array cols =>
        "array:" ++ String.join (cols.toList.map fun a => match a with
          | .left => "l"
          | .center => "c"
          | .right => "r")
    dumpMathRows (acc ++ tag ++ "[") rows ++ "]"

def dumpMathRows (acc : String) (rs : Math.MRows) : String :=
  match rs with
  | .nil => acc
  | .cons r rest =>
    dumpMathRows (dumpMathRow (acc ++ "(") r ++ ")") rest

def dumpMathRow (acc : String) (r : Math.MRow) : String :=
  match r with
  | .nil => acc
  | .cons cell rest =>
    dumpMathRow (dumpMathList (acc ++ "|") cell) rest

def dumpMathSup (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => (dumpMathRest (dumpMathItem (acc ++ "^{") x) rest).push '}'

def dumpMathSub (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => (dumpMathRest (dumpMathItem (acc ++ "_{") x) rest).push '}'

def dumpMathList (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => dumpMathRest (dumpMathItem acc x) rest

def dumpMathRest (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => dumpMathRest (dumpMathItem (acc ++ " ") x) rest

end

mutual

def dumpInlines (ind : String) (xs : Array Inline) : String :=
  dumpInlineList ind xs.toList

def dumpInlineList (ind : String) (xs : List Inline) : String :=
  match xs with
  | [] => ""
  | x :: rest => dumpInline ind x ++ dumpInlineList ind rest

def dumpInline (ind : String) (x : Inline) : String :=
  match x with
  | .text s => s!"{ind}text {s.quote}\n"
  | .math d src =>
    let kind := if d then "display" else "inline"
    s!"{ind}math {kind} {src.quote}\n"
  | .formula d src body =>
    let kind := if d then "display" else "inline"
    s!"{ind}formula {kind} {src.quote}\n{ind}  {dumpMathList "" body}\n"
  | .styled st body => s!"{ind}styled {st.label}\n" ++ dumpInlines (ind ++ "  ") body
  | .colored c name body =>
    let tag := match name with
      | some n => s!"{n} #{hex2 c.r}{hex2 c.g}{hex2 c.b}"
      | none => s!"#{hex2 c.r}{hex2 c.g}{hex2 c.b}"
    s!"{ind}color {tag}\n" ++ dumpInlines (ind ++ "  ") body
  | .link url body =>
    s!"{ind}link {url.quote}\n" ++ dumpInlines (ind ++ "  ") body
  | .underline body =>
    s!"{ind}underline\n" ++ dumpInlines (ind ++ "  ") body
  | .step n last body =>
    s!"{ind}{dumpStepRange n last}\n" ++ dumpInlines (ind ++ "  ") body
  | .fill => s!"{ind}fill\n"
  | .pageNumber => s!"{ind}pagenumber\n"
  | .pageCount => s!"{ind}pagecount\n"
  | .image src size alt =>
    let dim (label : String) (l : Image.Len) : String :=
      let bits := (if l.sp != 0 then [s!"{l.sp.toPtString}pt"] else []) ++
        (if l.tw != 0 then [s!"{l.tw}/1000tw"] else []) ++
        (if l.th != 0 then [s!"{l.th}/1000th"] else [])
      s!" {label} {if bits.isEmpty then "0" else String.intercalate "+" bits}"
    let parts :=
      (match size.width with | some l => dim "width" l | none => "") ++
      (match size.height with | some l => dim "height" l | none => "") ++
      (if size.scaleNum != 1 || size.scaleDen != 1 then
        s!" scale {size.scaleNum}/{size.scaleDen}" else "") ++
      (if size.keepAspect then " keepaspect" else "") ++
      (if alt.isEmpty then "" else s!" alt {alt.quote}")
    s!"{ind}image {src.quote}{parts}\n"
  | .linebreak extra =>
    if extra == ({} : SymGlue) then s!"{ind}linebreak\n"
    else s!"{ind}linebreak {dumpGlue extra}\n"

end

mutual

def dumpBlocks (ind : String) (xs : Array Block) : String :=
  dumpBlockList ind xs.toList

def dumpBlockList (ind : String) (xs : List Block) : String :=
  match xs with
  | [] => ""
  | b :: rest => dumpBlock ind b ++ dumpBlockList ind rest

def dumpItems (ind : String) (items : List (Array Block)) : String :=
  match items with
  | [] => ""
  | item :: rest =>
    s!"{ind}item\n" ++ dumpBlocks (ind ++ "  ") item ++ dumpItems ind rest

def dumpColumns (ind : String) (cols : List (Option Nat × Array Block)) : String :=
  match cols with
  | [] => ""
  | (w, body) :: rest =>
    let self := (match w with
      | some f => s!"{ind}column {f}/1000\n"
      | none => s!"{ind}column\n") ++ dumpBlocks (ind ++ "  ") body
    let tail := dumpColumns ind rest
    self ++ tail

def dumpBlock (ind : String) (b : Block) : String :=
  match b with
  | .para content => s!"{ind}para\n" ++ dumpInlines (ind ++ "  ") content
  | .section level starred title =>
    let star := if starred then "*" else ""
    s!"{ind}section{star} {level}\n" ++ dumpInlines (ind ++ "  ") title
  | .list ordered items =>
    let kind := if ordered then "ordered" else "unordered"
    s!"{ind}list {kind}\n" ++ dumpItems (ind ++ "  ") items.toList
  | .center body => s!"{ind}center\n" ++ dumpBlocks (ind ++ "  ") body
  | .quote body => s!"{ind}quote\n" ++ dumpBlocks (ind ++ "  ") body
  | .columns cols => s!"{ind}columns\n" ++ dumpColumns (ind ++ "  ") cols.toList
  | .step n last body =>
    s!"{ind}{dumpStepRange n last}\n" ++ dumpBlocks (ind ++ "  ") body
  | .note body => s!"{ind}note\n" ++ dumpBlocks (ind ++ "  ") body
  | .only targets body =>
    s!"{ind}only {String.intercalate "," targets.toList}\n" ++ dumpBlocks (ind ++ "  ") body
  | .nav body => s!"{ind}nav\n" ++ dumpBlocks (ind ++ "  ") body
  | .logo content =>
    if content.isEmpty then s!"{ind}logo clear\n"
    else s!"{ind}logo\n" ++ dumpInlines (ind ++ "  ") content
  | .spaced before body =>
    s!"{ind}block before {dumpGlue before}\n" ++ dumpBlocks (ind ++ "  ") body
  | .verbatim covered s =>
    s!"{ind}verbatim{if covered.isSome then " covered" else ""}\n" ++
    String.join ((verbatimLines s).toList.map
      fun l => s!"{ind}  {l.quote}\n")
  | .frame title standout valign body =>
    let va := match valign with
      | .center => ""
      | .top => " top"
      | .bottom => " bottom"
      | .golden => " golden"
    s!"{ind}frame{if standout then " standout" else ""}{va}\n" ++
    (if title.isEmpty then ""
     else s!"{ind}  title\n" ++ dumpInlines (ind ++ "    ") title) ++
    dumpBlocks (ind ++ "  ") body
  | .framefoot content =>
    s!"{ind}framefoot\n" ++ dumpInlines (ind ++ "  ") content
  | .rule color name thickness =>
    let nm := match name with
      | some n => s!" {n}"
      | none => s!" #{hex2 color.r}{hex2 color.g}{hex2 color.b}"
    s!"{ind}rule{nm} {dumpGlue thickness}\n"

end

/-- The fraction pending overlay content covers to, unless the document
declares `covered`: 38% of each run's own ink over the surface —
Material's disabled-state opacity (m2.material.io/design/interaction/
states.html#disabled: content at 38% opacity), an *opacity*, so it applies
per colour; compositing over an opaque page is mixing toward it. -/
def coveredFractionDefault : Nat := 38

/-- One foreground/background pairing a themed element ships. -/
structure ColorPair where
  fg : Color
  bg : Color
  deriving Repr, BEq

/-- The document's resolved design: every semantic role the backends read,
with every default applied here and nowhere else — the type is the totality
claim, so a consumer can never invent a per-site fallback for a missing
key. `frametitle` and `progress` are `Option` because their *presence* is
the design (declaring `frametitlebg` is what turns the frame title into a
bar; `progressfg` is what themes the section pages) — but each carries a
total pair, so once a feature is on, no colour in it can be absent.
`fgDeclared`/`bgDeclared` record what the document said, because the
backends honour it: the PDF paints no page and HTML emits no body rule for
an undeclared colour (HTML's own un-themed ink and surface live in the
stylesheet, dark variant included, and are proved legible in `Contrast`). -/
structure Design where
  fg : Color
  bg : Color
  fgDeclared : Bool
  bgDeclared : Bool
  /-- Pending overlay content covers to this fraction (percent) of its
  own ink over the surface, per colour. -/
  coveredFraction : Nat
  /-- A declared constant cover for runs with no colour of their own
  (documents in the wild declare `covered = <colour>`); `none` covers
  them at `coveredFraction` of `fg`. Resolved once, in `Design.cover`. -/
  covered : Option Color
  /-- Quieted secondary furniture — the chrome footer's small text draws in
  it; the body ink when undeclared. -/
  muted : Color
  /-- The frame-title bar, when the design has one. -/
  frametitle : Option ColorPair
  /-- The themed section page and its progress bar, when the design has one. -/
  progress : Option ColorPair
  /-- A `[standout]` frame's pair — total: without the keys it inverts the
  page's own colours. -/
  standout : ColorPair
  /-- The title-page rule's colour; the ink when undeclared. Declared by
  both shipped bundles and consumed by no backend yet — the role check in
  `Tests.lean` names it until the title-page rule lands. -/
  separator : Color
  /-- Thickness of the progress bar, resolved at layout like any token. -/
  progressheight : SymGlue
  styles : Styles
  deriving Repr, BEq

/-- The one construction site: every default the backends used to apply at
their own use sites (`find?` + `getD`, each with its own chain) is applied
here, once. -/
def Design.ofDoc (doc : Doc) : Design :=
  let pal := doc.palette
  let fg := (pal.find? "fg").getD Color.black
  let bg := (pal.find? "bg").getD Color.white
  { fg := fg
    bg := bg
    fgDeclared := (pal.find? "fg").isSome
    bgDeclared := (pal.find? "bg").isSome
    coveredFraction := pal.coveredFraction.getD coveredFractionDefault
    covered := pal.find? "covered"
    muted := (pal.find? "muted").getD fg
    frametitle := (pal.find? "frametitlebg").map fun barBg =>
      { fg := (pal.find? "frametitlefg").getD bg
        bg := barBg }
    progress := (pal.find? "progressfg").map fun barFg =>
      { fg := barFg
        bg := (pal.find? "progressbg").getD bg }
    standout := { fg := (pal.find? "standoutfg").getD bg
                  bg := (pal.find? "standoutbg").getD fg }
    separator := (pal.find? "separator").getD fg
    progressheight := (doc.tokens.find? "progressheight").getD
      { width := Dim.Length.ofSp (Dim.pt 1) }
    styles := doc.styles }

/-- Per-element style, total: the empty style is the default, applied here
rather than at each consumer. -/
def Design.style (d : Design) (element : String) : ElementStyle :=
  (d.styles.find? element).getD {}

/-- The palette keys whose resolved `Design` field a backend consumes today,
each named with its consumers; `Tests.lean` checks every role a built-in
bundle declares appears here or is a content colour, so a decorative key no
code reads is a named warning, never silence. -/
def Design.consumedRoles : List String :=
  ["fg", "bg",                        -- Layout.run / B.docBg, HtmlDoc.themeCss
   "covered",                         -- Layout.run's overlay dimming
   "muted",                           -- Layout.run's chrome footer, HtmlDoc.themeCss
   "frametitlefg", "frametitlebg",    -- Layout.collectBlock, HtmlDoc.themeCss
   "progressfg", "progressbg",        -- Layout.collectBlock, HtmlDoc.themeCss
   "standoutfg", "standoutbg",        -- Layout.collectBlock frame arm
   "separator"]                       -- the title-page rule (Elab.titleBlocks
                                      -- via the titlepage style; Layout .rule,
                                      -- HtmlDoc's <hr class="separator">)


/-- How covering paints: the colour of a covered run that had none of its
own, and the per-colour cover of an explicitly coloured one — the same
ink, quieter, never a repaint to one constant. Built once per document by
`Design.cover` (the one resolving site); the walks below only apply it. -/
structure Cover where
  plain : Color
  of : Color → Color

-- Overlay walks. Structural recursion through `List`, as the printers above.

/-- Is a step's content pending on page `k`: before its range starts, or
past its declared end (`\uncover<2>` covers on 1 and again from 3, exactly
as beamer's transparent covering does). Pending content dims; it is never
hidden. -/
def stepPending (n : Nat) (last : Option Nat) (k : Nat) : Bool :=
  k < n || (match last with | some u => k > u | none => false)

mutual

/-- The last step a frame's body reaches: how many pages the PDF handout
gives the frame. A frame nested below another block keeps one page. -/
def maxStepBlocks (xs : Array Block) : Nat := maxStepBlockList xs.toList

def maxStepBlockList : List Block → Nat
  | [] => 1
  | b :: rest => max (maxStepBlock b) (maxStepBlockList rest)

/-- Exhaustive by design (never add a wildcard arm). The `1` arms are
decisions, not gaps: furniture (a section title, a frame footer) and the
note side channel sit outside the overlay model — the dim walks keep them
whole, so a step there must not multiply handout pages either — and
verbatim carries no inline structure. -/
def maxStepBlock : Block → Nat
  | .para content => maxStepInlines content
  | .list _ items => maxStepItems items.toList
  | .center body => maxStepBlockList body.toList
  | .quote body => maxStepBlockList body.toList
  | .spaced _ body => maxStepBlockList body.toList
  | .columns cols => maxStepColumns cols.toList
  | .step n last body => max (max n (last.getD n)) (maxStepBlockList body.toList)
  -- Conditional content steps like any other content: a backend that keeps
  -- it must give its overlays their pages. A nav's links may step too.
  | .only _ body => maxStepBlockList body.toList
  | .nav body => maxStepBlockList body.toList
  | .section _ _ _ => 1
  | .verbatim _ _ => 1
  | .note _ => 1
  | .frame _ _ _ _ => 1
  | .framefoot _ => 1
  | .logo _ => 1
  | .rule _ _ _ => 1

def maxStepItems : List (Array Block) → Nat
  | [] => 1
  | item :: rest => max (maxStepBlockList item.toList) (maxStepItems rest)

def maxStepColumns : List (Option Nat × Array Block) → Nat
  | [] => 1
  | (_, body) :: rest => max (maxStepBlockList body.toList) (maxStepColumns rest)

def maxStepInlines (xs : Array Inline) : Nat := maxStepInlineList xs.toList

def maxStepInlineList : List Inline → Nat
  | [] => 1
  | x :: rest => max (maxStepInline x) (maxStepInlineList rest)

def maxStepInline : Inline → Nat
  | .styled _ body => maxStepInlineList body.toList
  | .colored _ _ body => maxStepInlineList body.toList
  | .link _ body => maxStepInlineList body.toList
  | .underline body => maxStepInlineList body.toList
  | .step n last body => max (max n (last.getD n)) (maxStepInlineList body.toList)
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _
  | .fill | .pageNumber | .pageCount | .linebreak _ => 1

end

mutual

/-- Every paragraph below here covered: the body of a step that is
pending. Covered means covered — an explicit colour nested inside (an
alert, a palette name) is covered too, exactly as beamer's transparent
covering mutes coloured text — but covered means *the same colour,
quieter*: each coloured run takes its own cover (`cover.of`), never a
repaint to one constant that would make a covered alert and a covered
example the same grey. Runs with no colour of their own take
`cover.plain`. Verbatim dims through its own `covered` field; section
blocks carry no colour and stay (recorded in PLAN). -/
def shadeBlocks (cover : Cover) (xs : Array Block) : Array Block :=
  shadeBlockList cover #[] xs.toList

def shadeBlockList (cover : Cover) (out : Array Block) : List Block → Array Block
  | [] => out
  | b :: rest => shadeBlockList cover (out.push (shadeBlock cover b)) rest

def shadeBlock (cover : Cover) : Block → Block
  | .para content => .para #[.colored cover.plain none (shadeInlines cover #[] content.toList)]
  | .list o items => .list o (shadeItems cover #[] items.toList)
  | .center body => .center (shadeBlockList cover #[] body.toList)
  | .quote body => .quote (shadeBlockList cover #[] body.toList)
  | .spaced g body => .spaced g (shadeBlockList cover #[] body.toList)
  | .columns cols => .columns (shadeColumns cover #[] cols.toList)
  | .step n last body => .step n last (shadeBlockList cover #[] body.toList)
  | .only targets body => .only targets (shadeBlockList cover #[] body.toList)
  | .nav body => .nav (shadeBlockList cover #[] body.toList)
  | .verbatim _ s => .verbatim (some cover.plain) s
  | .section l st title => .section l st title
  | .note body => .note body
  | .frame t st v body => .frame t st v body
  | .framefoot content => .framefoot content
  | .logo content => .logo content
  | .rule c nm th => .rule c nm th

def shadeItems (cover : Cover) (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest => shadeItems cover (out.push (shadeBlockList cover #[] item.toList)) rest

def shadeColumns (cover : Cover) (out : Array (Option Nat × Array Block)) :
    List (Option Nat × Array Block) → Array (Option Nat × Array Block)
  | [] => out
  | (w, body) :: rest =>
    shadeColumns cover (out.push (w, shadeBlockList cover #[] body.toList)) rest

def shadeInlines (cover : Cover) (out : Array Inline) : List Inline → Array Inline
  | [] => out
  | x :: rest => shadeInlines cover (out.push (shadeInline cover x)) rest

def shadeInline (cover : Cover) : Inline → Inline
  | .colored c _ body => .colored (cover.of c) none (shadeInlines cover #[] body.toList)
  | .styled st body => .styled st (shadeInlines cover #[] body.toList)
  | .link u body => .link u (shadeInlines cover #[] body.toList)
  | .underline body => .underline (shadeInlines cover #[] body.toList)
  | .step n last body => .step n last (shadeInlines cover #[] body.toList)
  | .text s => .text s
  | .math d src => .math d src
  -- shading leaves formula and image nodes whole: a pending formula or
  -- raster dims in the backends' hands, not in this walk
  | .formula d src body => .formula d src body
  | .image src size alt => .image src size alt
  | .fill => .fill
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak e => .linebreak e

end

mutual

/-- The frame's body as step `k` of its overlay shows it: content outside
its declared range dims to `cover`, everything else stays. Only colours
change, so no step can reflow the slide — the cover-not-hide invariant, by
construction. -/
def dimBlocks (cover : Cover) (k : Nat) (xs : Array Block) : Array Block :=
  dimBlockList cover k #[] xs.toList

def dimBlockList (cover : Cover) (k : Nat) (out : Array Block) :
    List Block → Array Block
  | [] => out
  | b :: rest => dimBlockList cover k (out.push (dimBlock cover k b)) rest

def dimBlock (cover : Cover) (k : Nat) : Block → Block
  | .para content => .para (dimInlines cover k content)
  | .list o items => .list o (dimItems cover k #[] items.toList)
  | .center body => .center (dimBlockList cover k #[] body.toList)
  | .quote body => .quote (dimBlockList cover k #[] body.toList)
  | .spaced g body => .spaced g (dimBlockList cover k #[] body.toList)
  | .columns cols => .columns (dimColumns cover k #[] cols.toList)
  | .step n last body =>
    if stepPending n last k then .step n last (shadeBlocks cover body)
    else .step n last (dimBlockList cover k #[] body.toList)
  | .only targets body => .only targets (dimBlockList cover k #[] body.toList)
  | .nav body => .nav (dimBlockList cover k #[] body.toList)
  | .section l st title => .section l st title
  | .verbatim c s => .verbatim c s
  | .note body => .note body
  | .frame t st v body => .frame t st v body
  | .framefoot content => .framefoot content
  | .logo content => .logo content
  | .rule c nm th => .rule c nm th

def dimItems (cover : Cover) (k : Nat) (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest => dimItems cover k (out.push (dimBlockList cover k #[] item.toList)) rest

def dimColumns (cover : Cover) (k : Nat) (out : Array (Option Nat × Array Block)) :
    List (Option Nat × Array Block) → Array (Option Nat × Array Block)
  | [] => out
  | (w, body) :: rest =>
    dimColumns cover k (out.push (w, dimBlockList cover k #[] body.toList)) rest

def dimInlines (cover : Cover) (k : Nat) (xs : Array Inline) : Array Inline :=
  dimInlineList cover k #[] xs.toList

def dimInlineList (cover : Cover) (k : Nat) (out : Array Inline) :
    List Inline → Array Inline
  | [] => out
  | x :: rest => dimInlineList cover k (out.push (dimInline cover k x)) rest

def dimInline (cover : Cover) (k : Nat) : Inline → Inline
  | .styled st body => .styled st (dimInlineList cover k #[] body.toList)
  | .colored c nm body => .colored c nm (dimInlineList cover k #[] body.toList)
  | .link u body => .link u (dimInlineList cover k #[] body.toList)
  | .underline body => .underline (dimInlineList cover k #[] body.toList)
  | .step n last body =>
    if stepPending n last k then
      .step n last #[.colored cover.plain none (shadeInlines cover #[] body.toList)]
    else .step n last (dimInlineList cover k #[] body.toList)
  | .text s => .text s
  | .math d src => .math d src
  -- dimming leaves formula and image nodes whole, as the shade does
  | .formula d src body => .formula d src body
  | .image src size alt => .image src size alt
  | .fill => .fill
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak e => .linebreak e

end

mutual

/-- Inside a list item, a leading `.step` (an overlay `\item<2->`) is pure
grouping by the time layout runs — dimming is already painted into colours —
but it hides the item's first paragraph from the walk that attaches the
marker. Flatten it, so the marker lands where LaTeX puts the label. Layout's
own pre-pass; the HTML backend keeps the wrapper for its `data-step`. -/
def unwrapItemSteps (xs : Array Block) : Array Block :=
  unwrapItemStepList #[] xs.toList

def unwrapItemStepList (out : Array Block) : List Block → Array Block
  | [] => out
  | b :: rest => unwrapItemStepList (out.push (unwrapItemStep b)) rest

def unwrapItemStep : Block → Block
  | .list o items => .list o (unwrapItemStepItems #[] items.toList)
  | .center body => .center (unwrapItemStepList #[] body.toList)
  | .quote body => .quote (unwrapItemStepList #[] body.toList)
  | .spaced g body => .spaced g (unwrapItemStepList #[] body.toList)
  | .columns cols => .columns (unwrapItemStepCols #[] cols.toList)
  | .step n l body => .step n l (unwrapItemStepList #[] body.toList)
  | .only targets body => .only targets (unwrapItemStepList #[] body.toList)
  | .nav body => .nav (unwrapItemStepList #[] body.toList)
  | .frame t s v body => .frame t s v (unwrapItemStepList #[] body.toList)
  | .para content => .para content
  | .section l st title => .section l st title
  | .verbatim c s => .verbatim c s
  | .note body => .note body
  | .framefoot content => .framefoot content
  | .logo content => .logo content
  | .rule c nm th => .rule c nm th

def unwrapItemStepItems (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest =>
    let item := unwrapItemStepList #[] item.toList
    let item := match item[0]? with
      | some (Block.step _ _ body) => body ++ item.extract 1 item.size
      | _ => item
    unwrapItemStepItems (out.push item) rest

def unwrapItemStepCols (out : Array (Option Nat × Array Block)) :
    List (Option Nat × Array Block) → Array (Option Nat × Array Block)
  | [] => out
  | (w, body) :: rest =>
    unwrapItemStepCols (out.push (w, unwrapItemStepList #[] body.toList)) rest

end

-- Nothing vanishes: dimming recolours, never removes. The text of a frame's
-- body is identical on every handout page, so the union of what the steps
-- show is the whole content — each page already shows all of it, dimmed or
-- not. Stated over the walks above and proved by the same structural
-- recursion; a step function that dropped or reordered content would fail
-- these equalities.

mutual

/-- The characters of block content with every mark stripped: the block
companion of `plainText`, and what the overlay walks must preserve. The
accumulator threads through, as every walk here does. -/
def blocksText (xs : Array Block) : String := blockTextList "" xs.toList

def blockTextList (acc : String) : List Block → String
  | [] => acc
  | b :: rest => blockTextList (blockTextOne acc b) rest

def blockTextOne (acc : String) : Block → String
  | .para content =>
    let t := plainText content
    acc ++ t
  | .section _ _ title =>
    let t := plainText title
    acc ++ t
  | .list _ items => blockTextItems acc items.toList
  | .center body => blockTextList acc body.toList
  -- A quotation's text is real census content, exactly as a paragraph's.
  | .quote body => blockTextList acc body.toList
  | .spaced _ body => blockTextList acc body.toList
  | .columns cols => blockTextColumns acc cols.toList
  | .step _ _ body => blockTextList acc body.toList
  -- The census reads the DECLARED content: what a conditional addresses to
  -- one backend is still content the document declares, so it counts here;
  -- `keepFor` is where a backend's own view drops it.
  | .only _ body => blockTextList acc body.toList
  | .nav body => blockTextList acc body.toList
  | .note body => blockTextList acc body.toList
  | .verbatim _ s => acc ++ s
  | .logo content => acc ++ plainText content
  | .frame title _ _ body => blockTextList (acc ++ plainText title) body.toList
  | .framefoot content => acc ++ plainText content
  -- A rule is decorative ink; it carries no text.
  | .rule _ _ _ => acc

def blockTextItems (acc : String) : List (Array Block) → String
  | [] => acc
  | item :: rest => blockTextItems (blockTextList acc item.toList) rest

def blockTextColumns (acc : String) : List (Option Nat × Array Block) → String
  | [] => acc
  | (_, body) :: rest => blockTextColumns (blockTextList acc body.toList) rest

end

mutual

/-- Every `.section` level in document order: the document's heading
outline, the fact the outline diagnostics and the markdown preamble read.
A frame's body is walked (a deck's title heading stands inside the title
frame); a note is a side channel and never ships a heading. The
accumulator threads through, as every walk here does. -/
def headingLevels (xs : Array Block) : Array Nat := headingLevelList #[] xs.toList

def headingLevelList (out : Array Nat) : List Block → Array Nat
  | [] => out
  | b :: rest => headingLevelList (headingLevelOne out b) rest

def headingLevelOne (out : Array Nat) : Block → Array Nat
  | .section level _ _ => out.push level
  | .para _ => out
  | .list _ items => headingLevelItems out items.toList
  | .center body => headingLevelList out body.toList
  | .quote body => headingLevelList out body.toList
  | .spaced _ body => headingLevelList out body.toList
  | .columns cols => headingLevelColumns out cols.toList
  | .step _ _ body => headingLevelList out body.toList
  | .only _ body => headingLevelList out body.toList
  | .nav body => headingLevelList out body.toList
  | .frame _ _ _ body => headingLevelList out body.toList
  | .note _ => out
  | .verbatim _ _ => out
  | .framefoot _ => out
  | .logo _ => out
  | .rule _ _ _ => out

def headingLevelItems (out : Array Nat) : List (Array Block) → Array Nat
  | [] => out
  | item :: rest => headingLevelItems (headingLevelList out item.toList) rest

def headingLevelColumns (out : Array Nat) : List (Option Nat × Array Block) → Array Nat
  | [] => out
  | (_, body) :: rest => headingLevelColumns (headingLevelList out body.toList) rest

end

/-- A heading level in the author's own vocabulary. -/
private def levelName : Nat → String
  | 0 => "the title"
  | 1 => "'\\section'"
  | 2 => "'\\subsection'"
  | _ => "'\\subsubsection'"

/-- Outline diagnostics over the document's heading levels — the two
machine-checkable rules the authorities state, checked on the IR without
rendering anything.

Levels must not skip as the outline descends: each heading following
another must have a level "less than, equal to, or 1 greater" than its
lead (HTML §4.3.11, the conformance rule; WCAG technique G141 spells the
same proper nesting). The jump is what a screen reader reports as a
broken outline. And the level-0 title, when the document has one, comes
first: a title standing mid-outline heads nothing before it (the
elaborator already keeps it unique; its position is the document's).

Warnings, once each per document, never errors: a document that skips a
level still means something and still renders — the diagnostic names the
native spelling that repairs it. -/
def outlineDiags (doc : Doc) : Array Diag := Id.run do
  let levels := headingLevels doc.body
  let mut out : Array Diag := #[]
  let mut prev : Option Nat := none
  let mut gapNamed := false
  let mut titleNamed := false
  for l in levels do
    if let some p := prev then
      if l > p + 1 && !gapNamed then
        gapNamed := true
        out := out.push (Diag.of .W0320
          s!"heading levels skip a step: {levelName p} is followed by {levelName l}"
          (help := some "descend one level at a time (HTML §4.3.11, WCAG G141); \
a screen reader reads the gap as a broken outline"))
      if l == 0 && !titleNamed then
        titleNamed := true
        out := out.push (Diag.of .W0321
          "the document title follows another heading"
          (help := some "put \\maketitle before the first \\section, so the \
outline starts at its top"))
    prev := some l
  return out

mutual

/-- Does this inline content carry a physical-page placeholder
(`\pagenumber` / `\pagecount`)? The physical sequence's only spellings —
what `Layout.substPage` resolves, and what the frame sequence must never be
mixed with silently (`footerSequenceDiags`). Explicit arms: a new `Inline`
constructor must answer here (the obligation table; no wildcard). -/
def hasPhysicalPageOne : Inline → Bool
  | .pageNumber => true
  | .pageCount => true
  | .styled _ body => hasPhysicalPageList body.toList
  | .colored _ _ body => hasPhysicalPageList body.toList
  | .link _ body => hasPhysicalPageList body.toList
  | .underline body => hasPhysicalPageList body.toList
  | .step _ _ body => hasPhysicalPageList body.toList
  | .text _ => false
  | .math _ _ => false
  -- a formula's body is math atoms and an image carries no inline body:
  -- neither can hold a page-number placeholder
  | .formula _ _ _ => false
  | .image _ _ _ => false
  | .fill => false
  | .linebreak _ => false

def hasPhysicalPageList : List Inline → Bool
  | [] => false
  | x :: rest => hasPhysicalPageOne x || hasPhysicalPageList rest

end

def hasPhysicalPage (xs : Array Inline) : Bool :=
  hasPhysicalPageList xs.toList

/-- Is this slot the frame sequence's? The counting model keeps two distinct
sequences: the frame numbering (`Ir.frameNumbers`, rendered only by
`ChromeSlot.render`) and the physical pages (`\pagenumber`/`\pagecount`,
rendered only by `Layout.substPage`) — a stepped frame advances one and not
the other. -/
def ChromeSlot.isFrameSequence : ChromeSlot → Bool
  | .frameNumber => true
  | .frameFraction => true
  | .sectionTitle => false

/-- The footer band must not mix the two sequences silently: a `\framefoot`
note carrying `\pagenumber`/`\pagecount` beside a frame-sequence chrome slot
puts the physical count and the frame count in one band with no declared
relation — on a stepped frame they visibly disagree. Legal, but only
declared: a document that names its own `\chrome` slots has said what the
band holds; one that inherited them from a theme has not, and gets a warning
naming both sequences. Warning, not error (the audit-strict severity
policy): the content is present, its meaning is what degraded. -/
def footerSequenceDiags (doc : Doc) : Array Diag := Id.run do
  unless doc.docClass == "slides" && doc.foot.isNone && !doc.chromeDeclared do
    return #[]
  let frameSlot := (doc.chrome.footerLeft.map ChromeSlot.isFrameSequence).getD false
    || (doc.chrome.footerRight.map ChromeSlot.isFrameSequence).getD false
  unless frameSlot do return #[]
  let mut out : Array Diag := #[]
  for b in doc.body do
    if let .framefoot xs := b then
      if hasPhysicalPage xs && out.isEmpty then
        out := out.push (Diag.of .W0332
          "the footer mixes the physical page number with the frame number: \
the two sequences are distinct, and a stepped frame advances one and not \
the other"
          (help := some "declare the footer's slots yourself \
(\\chrome{ footer = { left = ..., right = \\framenumber } }) to say the \
mixing is meant, or drop \\pagenumber from \\framefoot"))
  return out

/-- The two sequences stay distinct, stated where they could fuse: the
physical pass (`Layout.substPage` rewrites exactly `.pageNumber` and
`.pageCount`) can never touch a rendered frame slot, because the frame
sequence's one rendering site emits no physical placeholder. So no future
change can quietly derive one number from the other's counter without
breaking this. -/
theorem frame_sequence_carries_no_physical (s : ChromeSlot)
    (sec : Array Inline) (n total : Nat) (hs : s.isFrameSequence = true) :
    hasPhysicalPage (s.render sec n total) = false := by
  cases s with
  | sectionTitle => simp [ChromeSlot.isFrameSequence] at hs
  | frameNumber =>
    simp [ChromeSlot.render, hasPhysicalPage, hasPhysicalPageList,
      hasPhysicalPageOne]
  | frameFraction =>
    simp [ChromeSlot.render, hasPhysicalPage, hasPhysicalPageList,
      hasPhysicalPageOne]

private theorem plainTextList_append (l1 l2 : List Inline) :
    plainTextList (l1 ++ l2) = plainTextList l1 ++ plainTextList l2 := by
  induction l1 with
  | nil => simp [plainTextList]
  | cons x rest ih => simp [plainTextList, ih, String.append_assoc]

private theorem blockTextList_chain (l1 l2 : List Block) (acc : String) :
    blockTextList acc (l1 ++ l2) = blockTextList (blockTextList acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextList]
  | cons b rest ih => simp [blockTextList, ih]

private theorem blockTextItems_chain (l1 l2 : List (Array Block)) (acc : String) :
    blockTextItems acc (l1 ++ l2) = blockTextItems (blockTextItems acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextItems]
  | cons item rest ih => simp [blockTextItems, ih]

private theorem blockTextColumns_chain (l1 l2 : List (Option Nat × Array Block))
    (acc : String) :
    blockTextColumns acc (l1 ++ l2)
      = blockTextColumns (blockTextColumns acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextColumns]
  | cons col rest ih => simp [blockTextColumns, ih]

mutual

theorem shadeInlines_text (cover : Cover) (xs : List Inline) (out : Array Inline) :
    plainTextList (shadeInlines cover out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [shadeInlines, plainTextList]
  | x :: rest =>
    rw [shadeInlines, shadeInlines_text cover rest (out.push (shadeInline cover x))]
    simp [plainTextList, plainTextList_append, shadeInline_text cover x,
      String.append_assoc]

theorem shadeInline_text (cover : Cover) (x : Inline) :
    plainTextOne (shadeInline cover x) = plainTextOne x := by
  match x with
  | .colored c n body =>
    rw [shadeInline]
    simp [plainTextOne, shadeInlines_text cover body.toList #[], plainTextList]
  | .styled st body =>
    rw [shadeInline]
    simp [plainTextOne, shadeInlines_text cover body.toList #[], plainTextList]
  | .link u body =>
    rw [shadeInline]
    simp [plainTextOne, shadeInlines_text cover body.toList #[], plainTextList]
  | .underline body =>
    rw [shadeInline]
    simp [plainTextOne, shadeInlines_text cover body.toList #[], plainTextList]
  | .step n last body =>
    rw [shadeInline]
    simp [plainTextOne, shadeInlines_text cover body.toList #[], plainTextList]
  | .image _ _ _ =>
    -- shading leaves an image node whole (raster content dims in the
    -- backends' hands, not here), and its text census is empty either way
    rfl
  | .formula _ _ _ =>
    -- shading leaves a formula node whole (a pending formula dims in the
    -- backends' hands); its census is its source, untouched on both sides
    rfl
  | .text _ | .math _ _ | .fill | .pageNumber | .pageCount | .linebreak _ =>
    rfl

end

mutual

theorem shadeBlockList_text (cover : Cover) (xs : List Block) (out : Array Block)
    (acc : String) :
    blockTextList acc (shadeBlockList cover out xs).toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [shadeBlockList, blockTextList]
  | b :: rest =>
    rw [shadeBlockList,
      shadeBlockList_text cover rest (out.push (shadeBlock cover b)) acc]
    simp [blockTextList, blockTextList_chain, shadeBlock_text cover b]

theorem shadeBlock_text (cover : Cover) (b : Block) (acc : String) :
    blockTextOne acc (shadeBlock cover b) = blockTextOne acc b := by
  match b with
  | .para content =>
    rw [shadeBlock]
    simp [blockTextOne, plainText, plainTextList, plainTextOne,
      shadeInlines_text cover content.toList #[]]
  | .list o items =>
    rw [shadeBlock]
    simp [blockTextOne, shadeItems_text cover items.toList #[] acc, blockTextItems]
  | .center body =>
    rw [shadeBlock]
    simp [blockTextOne, shadeBlockList_text cover body.toList #[] acc, blockTextList]
  | .quote body =>
    rw [shadeBlock]
    simp [blockTextOne, shadeBlockList_text cover body.toList #[] acc, blockTextList]
  | .spaced g body =>
    rw [shadeBlock]
    simp [blockTextOne, shadeBlockList_text cover body.toList #[] acc, blockTextList]
  | .columns cols =>
    rw [shadeBlock]
    simp [blockTextOne, shadeColumns_text cover cols.toList #[] acc, blockTextColumns]
  | .step n last body =>
    rw [shadeBlock]
    simp [blockTextOne, shadeBlockList_text cover body.toList #[] acc, blockTextList]
  | .only targets body =>
    rw [shadeBlock]
    simp [blockTextOne, shadeBlockList_text cover body.toList #[] acc, blockTextList]
  | .nav body =>
    rw [shadeBlock]
    simp [blockTextOne, shadeBlockList_text cover body.toList #[] acc, blockTextList]
  | .verbatim c s => rfl
  -- A logo declaration is page furniture: the shade never repaints it, so
  -- its census — the declaration's own inline text — is untouched.
  | .logo _ => rfl
  | .section _ _ _ | .note _ | .frame _ _ _ _ | .framefoot _ | .rule _ _ _ => rfl

theorem shadeItems_text (cover : Cover) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (shadeItems cover out items).toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [shadeItems, blockTextItems]
  | item :: rest =>
    rw [shadeItems,
      shadeItems_text cover rest (out.push (shadeBlockList cover #[] item.toList)) acc]
    simp [blockTextItems, blockTextItems_chain,
      shadeBlockList_text cover item.toList #[], blockTextList]

theorem shadeColumns_text (cover : Cover) (cols : List (Option Nat × Array Block))
    (out : Array (Option Nat × Array Block)) (acc : String) :
    blockTextColumns acc (shadeColumns cover out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [shadeColumns, blockTextColumns]
  | (w, body) :: rest =>
    rw [shadeColumns,
      shadeColumns_text cover rest
        (out.push (w, shadeBlockList cover #[] body.toList)) acc]
    simp [blockTextColumns, blockTextColumns_chain,
      shadeBlockList_text cover body.toList #[], blockTextList]

end

/-- Shading preserves every character: covered content is recoloured,
never removed. -/
theorem shadeBlocks_text (cover : Cover) (xs : Array Block) :
    blocksText (shadeBlocks cover xs) = blocksText xs := by
  simp [blocksText, shadeBlocks, shadeBlockList_text cover xs.toList #[] "",
    blockTextList]

mutual

theorem dimInlineList_text (cover : Cover) (k : Nat) (xs : List Inline)
    (out : Array Inline) :
    plainTextList (dimInlineList cover k out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [dimInlineList, plainTextList]
  | x :: rest =>
    rw [dimInlineList, dimInlineList_text cover k rest]
    simp [plainTextList, plainTextList_append, dimInline_text cover k x,
      String.append_assoc]

theorem dimInline_text (cover : Cover) (k : Nat) (x : Inline) :
    plainTextOne (dimInline cover k x) = plainTextOne x := by
  match x with
  | .styled st body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k body.toList #[], plainTextList]
  | .colored c nm body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k body.toList #[], plainTextList]
  | .link u body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k body.toList #[], plainTextList]
  | .underline body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k body.toList #[], plainTextList]
  | .step n last body =>
    rw [dimInline]
    by_cases h : stepPending n last k = true
    · simp [h, plainTextOne, plainTextList,
        shadeInlines_text cover body.toList #[]]
    · simp [h, plainTextOne, dimInlineList_text cover k body.toList #[],
        plainTextList]
  | .image _ _ _ =>
    -- dimming leaves an image node whole; empty text census on both sides
    rfl
  | .formula _ _ _ =>
    -- dimming leaves a formula node whole; its census is its source,
    -- untouched on both sides
    rfl
  | .text _ | .math _ _ | .fill | .pageNumber | .pageCount | .linebreak _ =>
    rfl

end

mutual

theorem dimBlockList_text (cover : Cover) (k : Nat) (xs : List Block)
    (out : Array Block) (acc : String) :
    blockTextList acc (dimBlockList cover k out xs).toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [dimBlockList, blockTextList]
  | b :: rest =>
    rw [dimBlockList, dimBlockList_text cover k rest]
    simp [blockTextList, blockTextList_chain, dimBlock_text cover k b]

theorem dimBlock_text (cover : Cover) (k : Nat) (b : Block) (acc : String) :
    blockTextOne acc (dimBlock cover k b) = blockTextOne acc b := by
  match b with
  | .para content =>
    rw [dimBlock]
    simp [blockTextOne, plainText, dimInlines,
      dimInlineList_text cover k content.toList #[], plainTextList]
  | .list o items =>
    rw [dimBlock]
    simp [blockTextOne, dimItems_text cover k items.toList #[] acc, blockTextItems]
  | .center body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k body.toList #[] acc, blockTextList]
  | .quote body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k body.toList #[] acc, blockTextList]
  | .spaced g body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k body.toList #[] acc, blockTextList]
  | .columns cols =>
    rw [dimBlock]
    simp [blockTextOne, dimColumns_text cover k cols.toList #[] acc, blockTextColumns]
  | .step n last body =>
    rw [dimBlock]
    by_cases h : stepPending n last k = true
    · simp [h, blockTextOne, shadeBlocks,
        shadeBlockList_text cover body.toList #[] acc, blockTextList]
    · simp [h, blockTextOne, dimBlockList_text cover k body.toList #[] acc,
        blockTextList]
  | .only targets body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k body.toList #[] acc, blockTextList]
  | .nav body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k body.toList #[] acc, blockTextList]
  -- A logo declaration is page furniture: dimming never repaints it, so
  -- its census — the declaration's own inline text — is untouched.
  | .logo _ => rfl
  | .verbatim _ _ | .section _ _ _ | .note _ | .frame _ _ _ _ | .framefoot _
  | .rule _ _ _ => rfl

theorem dimItems_text (cover : Cover) (k : Nat) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (dimItems cover k out items).toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [dimItems, blockTextItems]
  | item :: rest =>
    rw [dimItems, dimItems_text cover k rest]
    simp [blockTextItems, blockTextItems_chain,
      dimBlockList_text cover k item.toList #[], blockTextList]

theorem dimColumns_text (cover : Cover) (k : Nat)
    (cols : List (Option Nat × Array Block))
    (out : Array (Option Nat × Array Block)) (acc : String) :
    blockTextColumns acc (dimColumns cover k out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [dimColumns, blockTextColumns]
  | (w, body) :: rest =>
    rw [dimColumns, dimColumns_text cover k rest]
    simp [blockTextColumns, blockTextColumns_chain,
      dimBlockList_text cover k body.toList #[], blockTextList]

end

/-- Nothing vanishes: page `k` of a stepped frame carries every character
the frame carries — dimming recolours pending content, it never hides it.
The union of what the steps show is therefore the whole content. -/
theorem dimBlocks_text (cover : Cover) (k : Nat) (xs : Array Block) :
    blocksText (dimBlocks cover k xs) = blocksText xs := by
  simp [blocksText, dimBlocks, dimBlockList_text cover k xs.toList #[] "",
    blockTextList]

-- Backend conditionals: `keepFor` is one backend's view of the document,
-- and `keepFor_covers` is what stops a conditional from becoming a silent
-- delete. Structural recursion through `List`, as the walks above.

/-- The backend names an `{ifbackend}` target may spell: one per emitter,
exactly the values the CLI's `--emit` accepts (`Cli.Args.emitOne` mirrors
this list, and each backend passes its own entry to `keepFor`). -/
def backendNames : List String := ["pdf", "html", "md"]

/-- Does backend `t` keep this block? Only a conditional can exclude one. -/
def keptBy (t : String) : Block → Bool
  | .only targets _ => targets.contains t
  | .para _ | .section _ _ _ | .list _ _ | .center _ | .quote _ | .spaced _ _
  | .verbatim _ _ | .columns _ | .step _ _ _ | .note _ | .logo _
  | .frame _ _ _ _ | .framefoot _ | .rule _ _ _ | .nav _ => true

mutual

/-- The document as backend `t` sees it: an `.only` block whose targets
exclude `t` is dropped whole, everything else is kept, and the walk carries
into every body so a nested conditional resolves against its own targets.
Each backend applies this once at its entry, with its own name — the drop
decision lives here and nowhere else, so no backend can improvise a
different reading of the same target set. -/
def keepForOne (t : String) : Block → Block
  | .only targets body => .only targets (keepForList t body.toList).toArray
  | .nav body => .nav (keepForList t body.toList).toArray
  | .list o items => .list o (keepForItems t items.toList).toArray
  | .center body => .center (keepForList t body.toList).toArray
  | .quote body => .quote (keepForList t body.toList).toArray
  | .spaced g body => .spaced g (keepForList t body.toList).toArray
  | .columns cols => .columns (keepForColumns t cols.toList).toArray
  | .step n l body => .step n l (keepForList t body.toList).toArray
  | .note body => .note (keepForList t body.toList).toArray
  | .frame ti st v body => .frame ti st v (keepForList t body.toList).toArray
  | .para c => .para c
  | .section l st title => .section l st title
  | .verbatim c s => .verbatim c s
  | .logo c => .logo c
  | .framefoot c => .framefoot c
  | .rule c n th => .rule c n th

def keepForList (t : String) : List Block → List Block
  | [] => []
  | b :: rest =>
    match keptBy t b with
    | true => keepForOne t b :: keepForList t rest
    | false => keepForList t rest

def keepForItems (t : String) : List (Array Block) → List (Array Block)
  | [] => []
  | item :: rest => (keepForList t item.toList).toArray :: keepForItems t rest

def keepForColumns (t : String) :
    List (Option Nat × Array Block) → List (Option Nat × Array Block)
  | [] => []
  | (w, body) :: rest => (w, (keepForList t body.toList).toArray) :: keepForColumns t rest

end

def keepFor (t : String) (xs : Array Block) : Array Block :=
  (keepForList t xs.toList).toArray

mutual

/-- Every text leaf of the blocks — each paragraph's, title's, and verbatim
block's plain text as one element (most recent first; the census is read as
a set). The backend-conditional conservation theorem ranges over leaves
rather than `blocksText`'s one concatenated string because a leaf survives
`keepFor` whole or not at all: a character's membership in the
concatenation could be satisfied by coincidence, a whole surviving leaf
cannot be. -/
def textLeavesList (acc : List String) : List Block → List String
  | [] => acc
  | b :: rest => textLeavesList (textLeavesOne acc b) rest

def textLeavesOne (acc : List String) : Block → List String
  | .para content => plainText content :: acc
  | .section _ _ title => plainText title :: acc
  | .verbatim _ s => s :: acc
  | .logo content => plainText content :: acc
  | .framefoot content => plainText content :: acc
  | .list _ items => textLeavesItems acc items.toList
  | .center body => textLeavesList acc body.toList
  | .quote body => textLeavesList acc body.toList
  | .spaced _ body => textLeavesList acc body.toList
  | .columns cols => textLeavesColumns acc cols.toList
  | .step _ _ body => textLeavesList acc body.toList
  | .note body => textLeavesList acc body.toList
  | .only _ body => textLeavesList acc body.toList
  | .nav body => textLeavesList acc body.toList
  | .frame title _ _ body => textLeavesList (plainText title :: acc) body.toList
  -- A rule is decorative ink; it carries no text (as `blockTextOne` reads it).
  | .rule _ _ _ => acc

def textLeavesItems (acc : List String) : List (Array Block) → List String
  | [] => acc
  | item :: rest => textLeavesItems (textLeavesList acc item.toList) rest

def textLeavesColumns (acc : List String) :
    List (Option Nat × Array Block) → List String
  | [] => acc
  | (_, body) :: rest => textLeavesColumns (textLeavesList acc body.toList) rest

end

def textLeaves (xs : Array Block) : List String := textLeavesList [] xs.toList

mutual

/-- No content is addressed to no backend: along every nesting path, each
`.only` node's targets keep at least one member of `avail` — the ambient
set, `backendNames` at the top and the path intersection inside a
conditional, so an `{ifbackend}{pdf}` inside an `{ifbackend}{html}`
addresses the empty set whatever each node spells alone. Elaboration
performs the same intersection as it walks in and fires W0324 exactly where
this returns false (pinned by test; `Elab` is monadic, so the
correspondence is not itself a theorem). -/
def orphanFreeList (avail : List String) : List Block → Bool
  | [] => true
  | b :: rest => orphanFreeOne avail b && orphanFreeList avail rest

def orphanFreeOne (avail : List String) : Block → Bool
  | .only targets body =>
    let eff := avail.filter (fun a => targets.contains a)
    !eff.isEmpty && orphanFreeList eff body.toList
  | .list _ items => orphanFreeItems avail items.toList
  | .center body => orphanFreeList avail body.toList
  | .quote body => orphanFreeList avail body.toList
  | .spaced _ body => orphanFreeList avail body.toList
  | .columns cols => orphanFreeColumns avail cols.toList
  | .step _ _ body => orphanFreeList avail body.toList
  | .note body => orphanFreeList avail body.toList
  | .nav body => orphanFreeList avail body.toList
  | .frame _ _ _ body => orphanFreeList avail body.toList
  | .para _ | .section _ _ _ | .verbatim _ _ | .logo _ | .framefoot _
  | .rule _ _ _ => true

def orphanFreeItems (avail : List String) : List (Array Block) → Bool
  | [] => true
  | item :: rest => orphanFreeList avail item.toList && orphanFreeItems avail rest

def orphanFreeColumns (avail : List String) :
    List (Option Nat × Array Block) → Bool
  | [] => true
  | (_, body) :: rest =>
    orphanFreeList avail body.toList && orphanFreeColumns avail rest

end

def orphanFree (avail : List String) (xs : Array Block) : Bool :=
  orphanFreeList avail xs.toList

-- The accumulator lemmas: a leaf census over `acc` is the census over `[]`
-- appended to `acc`, so membership statements can be read off `mem_append`.

mutual

private theorem textLeavesList_acc (acc : List String) (xs : List Block) :
    textLeavesList acc xs = textLeavesList [] xs ++ acc := by
  match xs with
  | [] => simp [textLeavesList]
  | b :: rest =>
    rw [textLeavesList, textLeavesList,
      textLeavesList_acc (textLeavesOne acc b) rest,
      textLeavesList_acc (textLeavesOne [] b) rest,
      textLeavesOne_acc acc b]
    simp [List.append_assoc]

private theorem textLeavesOne_acc (acc : List String) (b : Block) :
    textLeavesOne acc b = textLeavesOne [] b ++ acc := by
  match b with
  | .para c => simp [textLeavesOne]
  | .section l st title => simp [textLeavesOne]
  | .verbatim c s => simp [textLeavesOne]
  | .logo c => simp [textLeavesOne]
  | .framefoot c => simp [textLeavesOne]
  | .rule c n th => simp [textLeavesOne]
  | .list o items =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesItems_acc acc items.toList
  | .center body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .quote body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .spaced g body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .columns cols =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesColumns_acc acc cols.toList
  | .step n l body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .note body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .only targets body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .nav body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .frame title st v body =>
    rw [textLeavesOne, textLeavesOne,
      textLeavesList_acc (plainText title :: acc) body.toList,
      textLeavesList_acc [plainText title] body.toList]
    simp

private theorem textLeavesItems_acc (acc : List String) (items : List (Array Block)) :
    textLeavesItems acc items = textLeavesItems [] items ++ acc := by
  match items with
  | [] => simp [textLeavesItems]
  | item :: rest =>
    rw [textLeavesItems, textLeavesItems,
      textLeavesItems_acc (textLeavesList acc item.toList) rest,
      textLeavesItems_acc (textLeavesList [] item.toList) rest,
      textLeavesList_acc acc item.toList]
    simp [List.append_assoc]

private theorem textLeavesColumns_acc (acc : List String)
    (cols : List (Option Nat × Array Block)) :
    textLeavesColumns acc cols = textLeavesColumns [] cols ++ acc := by
  match cols with
  | [] => simp [textLeavesColumns]
  | (w, body) :: rest =>
    rw [textLeavesColumns, textLeavesColumns,
      textLeavesColumns_acc (textLeavesList acc body.toList) rest,
      textLeavesColumns_acc (textLeavesList [] body.toList) rest,
      textLeavesList_acc acc body.toList]
    simp [List.append_assoc]

end

private theorem keepForList_kept (t : String) (b : Block) (rest : List Block)
    (h : keptBy t b = true) :
    keepForList t (b :: rest) = keepForOne t b :: keepForList t rest := by
  rw [keepForList, h]

private theorem keepForList_dropped (t : String) (b : Block) (rest : List Block)
    (h : keptBy t b = false) :
    keepForList t (b :: rest) = keepForList t rest := by
  rw [keepForList, h]

mutual

/-- The conservation theorem behind `keepFor_covers`, at the list level and
generalized over the ambient target set, which shrinks by intersection at
each nested conditional exactly as `orphanFree` and elaboration walk it. -/
theorem keepForList_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (xs : List Block) (h : orphanFreeList avail xs = true) :
    ∀ s ∈ textLeavesList [] xs, ∃ t ∈ avail, s ∈ textLeavesList [] (keepForList t xs) := by
  match xs with
  | [] =>
    intro s hs
    simp [textLeavesList] at hs
  | b :: rest =>
    intro s hs
    rw [orphanFreeList, Bool.and_eq_true] at h
    rw [textLeavesList, textLeavesList_acc (textLeavesOne [] b) rest,
      List.mem_append] at hs
    cases hs with
    | inr hone =>
      obtain ⟨t, ht, hkept, hmem⟩ := keepForOne_covers avail t0 h0 b h.1 s hone
      refine ⟨t, ht, ?_⟩
      rw [keepForList_kept t b rest hkept, textLeavesList,
        textLeavesList_acc (textLeavesOne [] (keepForOne t b)) (keepForList t rest)]
      exact List.mem_append.mpr (.inr hmem)
    | inl hrest =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 rest h.2 s hrest
      refine ⟨t, ht, ?_⟩
      cases hk : keptBy t b with
      | true =>
        rw [keepForList_kept t b rest hk, textLeavesList,
          textLeavesList_acc (textLeavesOne [] (keepForOne t b)) (keepForList t rest)]
        exact List.mem_append.mpr (.inl hmem)
      | false =>
        rw [keepForList_dropped t b rest hk]
        exact hmem

theorem keepForOne_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (b : Block) (h : orphanFreeOne avail b = true) :
    ∀ s ∈ textLeavesOne [] b,
      ∃ t ∈ avail, keptBy t b = true ∧ s ∈ textLeavesOne [] (keepForOne t b) := by
  match b with
  | .para c =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .section l st title =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .verbatim c str =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .logo c =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .framefoot c =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .rule c n th =>
    intro s hs
    simp [textLeavesOne] at hs
  | .center body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .quote body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .spaced g body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .step n l body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .note body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .nav body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .list o items =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForItems_covers avail t0 h0 items.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .columns cols =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForColumns_covers avail t0 h0 cols.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .frame title st v body =>
    intro s hs
    rw [textLeavesOne, textLeavesList_acc [plainText title] body.toList,
      List.mem_append] at hs
    cases hs with
    | inr hti =>
      refine ⟨t0, h0, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText title] ((keepForList t0 body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inr hti)
    | inl hbody =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hbody
      refine ⟨t, ht, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText title] ((keepForList t body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inl (by simpa using hmem))
  | .only targets body =>
    intro s hs
    rw [orphanFreeOne, Bool.and_eq_true] at h
    have hne : avail.filter (fun a => targets.contains a) ≠ [] := by
      intro he
      rw [he] at h
      simp [List.isEmpty] at h
    obtain ⟨t1, ht1⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨t, ht, hmem⟩ := keepForList_covers
      (avail.filter (fun a => targets.contains a)) t1 ht1 body.toList h.2 s
      (by simpa [textLeavesOne] using hs)
    have ht' := List.mem_filter.mp ht
    refine ⟨t, ht'.1, ht'.2, ?_⟩
    rw [keepForOne, textLeavesOne]
    simpa using hmem

theorem keepForItems_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (items : List (Array Block)) (h : orphanFreeItems avail items = true) :
    ∀ s ∈ textLeavesItems [] items,
      ∃ t ∈ avail, s ∈ textLeavesItems [] (keepForItems t items) := by
  match items with
  | [] =>
    intro s hs
    simp [textLeavesItems] at hs
  | item :: rest =>
    intro s hs
    rw [orphanFreeItems, Bool.and_eq_true] at h
    rw [textLeavesItems, textLeavesItems_acc (textLeavesList [] item.toList) rest,
      List.mem_append] at hs
    cases hs with
    | inr hitem =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 item.toList h.1 s hitem
      refine ⟨t, ht, ?_⟩
      rw [keepForItems, textLeavesItems,
        textLeavesItems_acc (textLeavesList [] (keepForList t item.toList).toArray.toList)
          (keepForItems t rest)]
      exact List.mem_append.mpr (.inr (by simpa using hmem))
    | inl hrest =>
      obtain ⟨t, ht, hmem⟩ := keepForItems_covers avail t0 h0 rest h.2 s hrest
      refine ⟨t, ht, ?_⟩
      rw [keepForItems, textLeavesItems,
        textLeavesItems_acc (textLeavesList [] (keepForList t item.toList).toArray.toList)
          (keepForItems t rest)]
      exact List.mem_append.mpr (.inl hmem)

theorem keepForColumns_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (cols : List (Option Nat × Array Block))
    (h : orphanFreeColumns avail cols = true) :
    ∀ s ∈ textLeavesColumns [] cols,
      ∃ t ∈ avail, s ∈ textLeavesColumns [] (keepForColumns t cols) := by
  match cols with
  | [] =>
    intro s hs
    simp [textLeavesColumns] at hs
  | (w, body) :: rest =>
    intro s hs
    rw [orphanFreeColumns, Bool.and_eq_true] at h
    rw [textLeavesColumns, textLeavesColumns_acc (textLeavesList [] body.toList) rest,
      List.mem_append] at hs
    cases hs with
    | inr hbody =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h.1 s hbody
      refine ⟨t, ht, ?_⟩
      rw [keepForColumns, textLeavesColumns,
        textLeavesColumns_acc (textLeavesList [] (keepForList t body.toList).toArray.toList)
          (keepForColumns t rest)]
      exact List.mem_append.mpr (.inr (by simpa using hmem))
    | inl hrest =>
      obtain ⟨t, ht, hmem⟩ := keepForColumns_covers avail t0 h0 rest h.2 s hrest
      refine ⟨t, ht, ?_⟩
      rw [keepForColumns, textLeavesColumns,
        textLeavesColumns_acc (textLeavesList [] (keepForList t body.toList).toArray.toList)
          (keepForColumns t rest)]
      exact List.mem_append.mpr (.inl hmem)

end

/-- **Nothing is addressable by no backend.** For a document whose backend
conditionals are all answered — along every nesting path each `.only`
node's target set keeps at least one available backend (`orphanFree`, the
condition whose violation elaboration diagnoses as W0324) — every declared
text leaf survives in at least one backend's kept document: the union over
the backends of what each `keepFor` keeps is the declared content. This is
the conservation theorem for the backend conditional, the one that stops
`{ifbackend}` from becoming a silent delete: dropping is only ever the
complement of another backend's keeping, or a named diagnostic. Stated over
the same `plainText` census machinery as the overlay conservation theorems
(`shadeBlocks_text`, `dimBlocks_text`), lifted to whole leaves because
`keepFor` drops whole subtrees. -/
theorem keepFor_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (xs : Array Block) (h : orphanFree avail xs = true) :
    ∀ s ∈ textLeaves xs, ∃ t ∈ avail, s ∈ textLeaves (keepFor t xs) := by
  intro s hs
  obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 xs.toList h s hs
  exact ⟨t, ht, by simpa [textLeaves, keepFor] using hmem⟩


-- Image walks: the request an image node states, and the caption an image
-- inherits. Structural recursion through `List`, as the printers above.

mutual

/-- Every image source the inlines reference, in document order, `out`
threading through so the walk is linear. -/
def imageSrcsInlines (out : Array String) (xs : Array Inline) : Array String :=
  imageSrcsInlineList out xs.toList

def imageSrcsInlineList (out : Array String) : List Inline → Array String
  | [] => out
  | x :: rest => imageSrcsInlineList (imageSrcsInline out x) rest

def imageSrcsInline (out : Array String) : Inline → Array String
  | .image src _ _ => if out.contains src then out else out.push src
  | .styled _ body => imageSrcsInlineList out body.toList
  | .colored _ _ body => imageSrcsInlineList out body.toList
  | .link _ body => imageSrcsInlineList out body.toList
  | .underline body => imageSrcsInlineList out body.toList
  | .step _ _ body => imageSrcsInlineList out body.toList
  | _ => out

end

mutual

def imageSrcsBlocks (out : Array String) (xs : Array Block) : Array String :=
  imageSrcsBlockList out xs.toList

def imageSrcsBlockList (out : Array String) : List Block → Array String
  | [] => out
  | b :: rest => imageSrcsBlockList (imageSrcsBlock out b) rest

def imageSrcsBlock (out : Array String) : Block → Array String
  | .para content => imageSrcsInlines out content
  | .section _ _ title => imageSrcsInlines out title
  | .list _ items => imageSrcsItems out items.toList
  | .center body => imageSrcsBlockList out body.toList
  | .quote body => imageSrcsBlockList out body.toList
  | .spaced _ body => imageSrcsBlockList out body.toList
  | .columns cols => imageSrcsColumns out cols.toList
  | .step _ _ body => imageSrcsBlockList out body.toList
  | .only _ body => imageSrcsBlockList out body.toList
  | .nav body => imageSrcsBlockList out body.toList
  | .note body => imageSrcsBlockList out body.toList
  | .logo content => imageSrcsInlines out content
  | .verbatim _ _ => out
  | .frame title _ _ body => imageSrcsBlockList (imageSrcsInlines out title) body.toList
  | .framefoot content => imageSrcsInlines out content
  | .rule _ _ _ => out

def imageSrcsItems (out : Array String) : List (Array Block) → Array String
  | [] => out
  | item :: rest => imageSrcsItems (imageSrcsBlockList out item.toList) rest

def imageSrcsColumns (out : Array String) : List (Option Nat × Array Block) → Array String
  | [] => out
  | (_, body) :: rest => imageSrcsColumns (imageSrcsBlockList out body.toList) rest

end

/-- Every image the document references, deduplicated, in document order:
the request value the CLI driver fulfils by reading and decoding each file
into the `Image.Store` layout and the backends consume. Files are effects,
so the core never opens one — the same shape as fonts. -/
def imageRefs (doc : Doc) : Array String := Id.run do
  let mut out := imageSrcsBlocks #[] doc.body
  if let some h := doc.head then out := imageSrcsInlines out h
  if let some f := doc.foot then out := imageSrcsInlines out f
  if let some l := doc.logo then out := imageSrcsInlines out l
  for (_, st) in doc.styles.entries do
    if let some tpl := st.font then out := imageSrcsInlines out tpl
    if let some m := st.marker then out := imageSrcsInlines out m
  return out

mutual

/-- Give every image that has no `alt` yet this text: how a `figure`'s
caption becomes the accessible name of the image it captions. -/
def setAltInlines (alt : String) (xs : Array Inline) : Array Inline :=
  setAltInlineList alt #[] xs.toList

def setAltInlineList (alt : String) (out : Array Inline) : List Inline → Array Inline
  | [] => out
  | x :: rest => setAltInlineList alt (out.push (setAltInline alt x)) rest

def setAltInline (alt : String) : Inline → Inline
  | .image src size old => .image src size (if old.isEmpty then alt else old)
  | .styled st body => .styled st (setAltInlineList alt #[] body.toList)
  | .colored c n body => .colored c n (setAltInlineList alt #[] body.toList)
  | .link u body => .link u (setAltInlineList alt #[] body.toList)
  | .underline body => .underline (setAltInlineList alt #[] body.toList)
  | .step n l body => .step n l (setAltInlineList alt #[] body.toList)
  | other => other

end

mutual

def setAltBlocks (alt : String) (xs : Array Block) : Array Block :=
  setAltBlockList alt #[] xs.toList

def setAltBlockList (alt : String) (out : Array Block) : List Block → Array Block
  | [] => out
  | b :: rest => setAltBlockList alt (out.push (setAltBlock alt b)) rest

def setAltBlock (alt : String) : Block → Block
  | .para content => .para (setAltInlines alt content)
  | .center body => .center (setAltBlockList alt #[] body.toList)
  | .quote body => .quote (setAltBlockList alt #[] body.toList)
  | .spaced g body => .spaced g (setAltBlockList alt #[] body.toList)
  | .step n l body => .step n l (setAltBlockList alt #[] body.toList)
  | .only targets body => .only targets (setAltBlockList alt #[] body.toList)
  | .nav body => .nav (setAltBlockList alt #[] body.toList)
  | other => other

end

def dumpDiag (d : Diag) : String :=
  let where' := match d.span with
    | some sp => s!"{sp.pos.line}:{sp.pos.col}"
    | none => "-"
  let help := match d.help with
    | some h => s!" | help: {h}"
    | none => ""
  s!"{d.severity.label}[{d.code}] {where'} {d.message}{help}\n"

def dump (doc : Doc) (diags : Array Diag) : String :=
  let opts := if doc.classOptions == "" then "" else s!" [{doc.classOptions}]"
  let head := s!"class {doc.docClass}{opts}\n"
  let page :=
    s!"page {doc.page.width.toPtString}x{doc.page.height.toPtString} " ++
    s!"vmargin {doc.page.vmargin.toPtString} hmargin {doc.page.hmargin.toPtString}" ++
    (if doc.page.fontSize != baseFontSize
      then s!" fontsize {doc.page.fontSize.toPtString}" else "") ++
    (match doc.page.parskip with
      | some g => s!" parskip {dumpGlue g}"
      | none => "") ++
    (if doc.page.bleed != 0 then s!" bleed {doc.page.bleed.toPtString}" else "") ++
    (match doc.page.hyphenate with
      | some b => s!" hyphenate {if b then "on" else "off"}"
      | none => "") ++
    (match doc.page.justify with
      | some b => s!" justify {if b then "on" else "off"}"
      | none => "") ++ "\n"
  let metaLine (label : String) (v : Option String) : String :=
    match v with
    | some s => s!"meta {label} {s.quote}\n"
    | none => ""
  let fontLine (label : String) (v : Option String) : String :=
    match v with
    | some f => s!"font {label} {f.quote}
"
    | none => ""
  let fontLines :=
    String.join (doc.fonts.dirs.toList.map fun d => fontLine "dir" (some d)) ++
    fontLine "body" doc.fonts.body ++ fontLine "sans" doc.fonts.sans ++
    fontLine "mono" doc.fonts.mono ++
    String.join (doc.fonts.faces.toList.map fun ((slot, bold, italic), f) =>
      let slotName := match slot with | 0 => "body" | 1 => "sans" | _ => "mono"
      let variant := match bold, italic with
        | false, false => "upright" | true, false => "bold"
        | false, true => "italic" | true, true => "bolditalic"
      fontLine s!"{slotName}.{variant}" (some f))
  let paletteLines := String.join (doc.palette.entries.toList.map fun (n, c) =>
    let mark := if doc.palette.decorative.contains n then " decorative" else ""
    s!"palette {n} #{hex2 c.r}{hex2 c.g}{hex2 c.b}{mark}\n") ++
    (match doc.palette.coveredFraction with
     | some f => s!"palette covered {f}%\n"
     | none => "")
  let tokenLines := String.join (doc.tokens.entries.toList.map fun (n, g) =>
    s!"token {n} {dumpGlue g}\n")
  let runLines :=
    (match doc.head with
     | some xs => "runninghead\n" ++ dumpInlines "  " xs
     | none => "") ++
    (match doc.foot with
     | some xs => "runningfoot\n" ++ dumpInlines "  " xs
     | none => "") ++
    (if doc.chrome.hasFooter then
      let slot (label : String) (s : Option ChromeSlot) : String :=
        match s with
        | some v => s!" {label} {v.label}"
        | none => ""
      s!"chrome footer{slot "left" doc.chrome.footerLeft}{slot "right" doc.chrome.footerRight}\n"
     else "") ++
    (match doc.logo with
     | some xs => "logo\n" ++ dumpInlines "  " xs
     | none => "")
  let infoLines :=
    metaLine "title" doc.info.title ++ metaLine "author" doc.info.author ++
    metaLine "subject" doc.info.subject ++ metaLine "keywords" doc.info.keywords ++
    metaLine "url" doc.info.url ++ metaLine "image" doc.info.image ++
    metaLine "favicon" doc.info.favicon
  let outputLines :=
    (if doc.output.formats.isEmpty then ""
     else s!"output formats {String.intercalate "," doc.output.formats.toList}\n") ++
    (match doc.output.css with
     | some c => s!"output css {c}\n"
     | none => "") ++
    (match doc.output.stylesheet with
     | some s => s!"output stylesheet {s.quote}\n"
     | none => "")
  let asserts := String.join (doc.asserts.toList.map fun a =>
    s!"assert {a.kind.source}\n")
  let allowLine := if doc.allow.isEmpty then ""
    else s!"allow {String.intercalate ", " doc.allow.toList}\n"
  let body := dumpBlocks "" doc.body
  let ds :=
    if diags.isEmpty then
      "-- diagnostics\n(none)\n"
    else
      "-- diagnostics\n" ++ String.join (diags.toList.map dumpDiag)
  head ++ page ++ fontLines ++ paletteLines ++ tokenLines ++ runLines ++ infoLines ++ outputLines ++ asserts ++ allowLine ++ body ++ ds

end LeanTex.Core.Ir
