import LeanTex.Core.Diag
import LeanTex.Core.Dim

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

/-- Named colours declared by `\palette`. -/
structure Palette where
  entries : Array (String × Color) := #[]
  /-- Entries declared under `\palette[decorative]{...}`: deliberately
  low-contrast — a watermark, a dimmed aside — and exempt from the pairing
  diagnostic, the way WCAG 2.2 SC 1.4.3 exempts pure decoration. -/
  decorative : Array String := #[]
  deriving Repr, BEq, Inhabited

def Palette.find? (p : Palette) (name : String) : Option Color :=
  (p.entries.find? (·.1 == name)).map (·.2)

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
  deriving Repr, BEq, Inhabited

/-- PDF document information, as declared by `\pdfmeta`. -/
structure Meta where
  title : Option String := none
  author : Option String := none
  subject : Option String := none
  keywords : Option String := none
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
  deriving Repr, BEq, Inhabited

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
  deriving Repr, BEq, Inhabited

/-- Elements a document may style. Section levels are `section`, `subsection`,
`subsubsection`; lists are `itemize` and `enumerate` — those two style every
nesting level, and `itemize2`..`itemize4` / `enumerate2`..`enumerate4`
override one level, the way `\labelitemii` or `\setlist[itemize,2]` does;
`frametitle`, `sectionpage`, and `standout` are the slides furniture (their
`font` is read; the other keys have no meaning there yet). -/
def styleableElements : List String :=
  ["section", "subsection", "subsubsection", "itemize", "enumerate",
   "itemize2", "itemize3", "itemize4", "enumerate2", "enumerate3", "enumerate4",
   "frametitle", "sectionpage", "standout"]

structure Styles where
  entries : Array (String × ElementStyle) := #[]
  deriving Repr, BEq, Inhabited

def Styles.find? (s : Styles) (element : String) : Option ElementStyle :=
  (s.entries.find? (·.1 == element)).map (·.2)

/-- What a chrome footer slot shows, resolved per page by the backends: the
title of the current top-level section, or the index of the page's own frame
(one number for all pages of a stepped frame). Data, not content: a theme
names the datum and the engine supplies the value, so a bundle stays a table
and no backend learns a theme's name. -/
inductive ChromeSlot where
  | sectionTitle
  | frameNumber
  deriving Repr, BEq, Inhabited

def ChromeSlot.label : ChromeSlot → String
  | .sectionTitle => "sectiontitle"
  | .frameNumber => "framenumber"

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

mutual

def fillOne (content : Array Inline) : Inline → Inline
  | .styled st body =>
    .styled st (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .colored c n body =>
    .colored c n (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .underline body =>
    .underline (if body.isEmpty then content else (fillList content body.toList).toArray)
  | other => other

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
  /-- First page that carries running content; `\thispagestyle{empty}` on the
  opening page is `2`. -/
  runningFrom : Nat := 1
  /-- Slide chrome: the themed default footer's slots. `foot` wins over it. -/
  chrome : Chrome := {}
  styles : Styles := {}
  info : Meta := {}
  output : OutputSpec := {}
  asserts : Array Assertion := #[]
  body : Array Block := #[]
  deriving Repr, BEq, Inhabited

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
  | .styled _ body => plainTextList body.toList
  | .colored _ _ body => plainTextList body.toList
  | .link _ body => plainTextList body.toList
  | .underline body => plainTextList body.toList
  | .step _ _ body => plainTextList body.toList
  | .fill | .pageNumber | .pageCount => ""
  | .linebreak _ => " "

end

/-- A step's range as the surface spells it: `step 2`, `step 2-3`, and
`step 2-2` for `<2->`, `<2-3>`, and `<2>`. -/
def dumpStepRange (n : Nat) (last : Option Nat) : String :=
  match last with
  | some u => s!"step {n}-{u}"
  | none => s!"step {n}"

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
  | .columns cols => s!"{ind}columns\n" ++ dumpColumns (ind ++ "  ") cols.toList
  | .step n last body =>
    s!"{ind}{dumpStepRange n last}\n" ++ dumpBlocks (ind ++ "  ") body
  | .note body => s!"{ind}note\n" ++ dumpBlocks (ind ++ "  ") body
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

end

/-- The colour pending overlay content dims to, unless the document's
palette declares `covered`: the same value as the HTML muted token, so the
two backends' handouts agree. -/
def coveredDefault : Color := { r := 0xA1, g := 0xA1, b := 0xAA }

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

def maxStepBlock : Block → Nat
  | .para content => maxStepInlines content
  | .list _ items => maxStepItems items.toList
  | .center body => maxStepBlockList body.toList
  | .spaced _ body => maxStepBlockList body.toList
  | .columns cols => maxStepColumns cols.toList
  | .step n last body => max (max n (last.getD n)) (maxStepBlockList body.toList)
  | _ => 1

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
  | _ => 1

end

mutual

/-- Every paragraph below here recoloured to the covered colour: the body
of a step that is pending. Covered means covered: an explicit colour nested
inside (an alert, a palette name) is repainted too, exactly as beamer's
transparent covering mutes coloured text — a covering the content's own
colours could defeat would leave a colour-rich slide reading as never
covered. Verbatim dims through its own `covered` field; section blocks
carry no colour and stay (recorded in PLAN). -/
def shadeBlocks (dim : Color) (xs : Array Block) : Array Block :=
  shadeBlockList dim #[] xs.toList

def shadeBlockList (dim : Color) (out : Array Block) : List Block → Array Block
  | [] => out
  | b :: rest => shadeBlockList dim (out.push (shadeBlock dim b)) rest

def shadeBlock (dim : Color) : Block → Block
  | .para content => .para #[.colored dim none (shadeInlines dim #[] content.toList)]
  | .list o items => .list o (shadeItems dim #[] items.toList)
  | .center body => .center (shadeBlockList dim #[] body.toList)
  | .spaced g body => .spaced g (shadeBlockList dim #[] body.toList)
  | .columns cols => .columns (shadeColumns dim #[] cols.toList)
  | .step n last body => .step n last (shadeBlockList dim #[] body.toList)
  | .verbatim _ s => .verbatim (some dim) s
  | other => other

def shadeItems (dim : Color) (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest => shadeItems dim (out.push (shadeBlockList dim #[] item.toList)) rest

def shadeColumns (dim : Color) (out : Array (Option Nat × Array Block)) :
    List (Option Nat × Array Block) → Array (Option Nat × Array Block)
  | [] => out
  | (w, body) :: rest =>
    shadeColumns dim (out.push (w, shadeBlockList dim #[] body.toList)) rest

def shadeInlines (dim : Color) (out : Array Inline) : List Inline → Array Inline
  | [] => out
  | x :: rest => shadeInlines dim (out.push (shadeInline dim x)) rest

def shadeInline (dim : Color) : Inline → Inline
  | .colored _ _ body => .colored dim none (shadeInlines dim #[] body.toList)
  | .styled st body => .styled st (shadeInlines dim #[] body.toList)
  | .link u body => .link u (shadeInlines dim #[] body.toList)
  | .underline body => .underline (shadeInlines dim #[] body.toList)
  | .step n last body => .step n last (shadeInlines dim #[] body.toList)
  | other => other

end

mutual

/-- The frame's body as step `k` of its overlay shows it: content outside
its declared range dims to `dim`, everything else stays. Only colours
change, so no step can reflow the slide — the dim-not-hide invariant, by
construction. -/
def dimBlocks (dim : Color) (k : Nat) (xs : Array Block) : Array Block :=
  dimBlockList dim k #[] xs.toList

def dimBlockList (dim : Color) (k : Nat) (out : Array Block) :
    List Block → Array Block
  | [] => out
  | b :: rest => dimBlockList dim k (out.push (dimBlock dim k b)) rest

def dimBlock (dim : Color) (k : Nat) : Block → Block
  | .para content => .para (dimInlines dim k content)
  | .list o items => .list o (dimItems dim k #[] items.toList)
  | .center body => .center (dimBlockList dim k #[] body.toList)
  | .spaced g body => .spaced g (dimBlockList dim k #[] body.toList)
  | .columns cols => .columns (dimColumns dim k #[] cols.toList)
  | .step n last body =>
    if stepPending n last k then .step n last (shadeBlocks dim body)
    else .step n last (dimBlockList dim k #[] body.toList)
  | other => other

def dimItems (dim : Color) (k : Nat) (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest => dimItems dim k (out.push (dimBlockList dim k #[] item.toList)) rest

def dimColumns (dim : Color) (k : Nat) (out : Array (Option Nat × Array Block)) :
    List (Option Nat × Array Block) → Array (Option Nat × Array Block)
  | [] => out
  | (w, body) :: rest =>
    dimColumns dim k (out.push (w, dimBlockList dim k #[] body.toList)) rest

def dimInlines (dim : Color) (k : Nat) (xs : Array Inline) : Array Inline :=
  dimInlineList dim k #[] xs.toList

def dimInlineList (dim : Color) (k : Nat) (out : Array Inline) :
    List Inline → Array Inline
  | [] => out
  | x :: rest => dimInlineList dim k (out.push (dimInline dim k x)) rest

def dimInline (dim : Color) (k : Nat) : Inline → Inline
  | .styled st body => .styled st (dimInlineList dim k #[] body.toList)
  | .colored c nm body => .colored c nm (dimInlineList dim k #[] body.toList)
  | .link u body => .link u (dimInlineList dim k #[] body.toList)
  | .underline body => .underline (dimInlineList dim k #[] body.toList)
  | .step n last body =>
    if stepPending n last k then
      .step n last #[.colored dim none (shadeInlines dim #[] body.toList)]
    else .step n last (dimInlineList dim k #[] body.toList)
  | other => other

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
  | .spaced g body => .spaced g (unwrapItemStepList #[] body.toList)
  | .columns cols => .columns (unwrapItemStepCols #[] cols.toList)
  | .step n l body => .step n l (unwrapItemStepList #[] body.toList)
  | .frame t s v body => .frame t s v (unwrapItemStepList #[] body.toList)
  | other => other

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
  | .spaced _ body => blockTextList acc body.toList
  | .columns cols => blockTextColumns acc cols.toList
  | .step _ _ body => blockTextList acc body.toList
  | .note body => blockTextList acc body.toList
  | .verbatim _ s => acc ++ s
  | .frame title _ _ body => blockTextList (acc ++ plainText title) body.toList
  | .framefoot content => acc ++ plainText content

def blockTextItems (acc : String) : List (Array Block) → String
  | [] => acc
  | item :: rest => blockTextItems (blockTextList acc item.toList) rest

def blockTextColumns (acc : String) : List (Option Nat × Array Block) → String
  | [] => acc
  | (_, body) :: rest => blockTextColumns (blockTextList acc body.toList) rest

end

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

theorem shadeInlines_text (dim : Color) (xs : List Inline) (out : Array Inline) :
    plainTextList (shadeInlines dim out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [shadeInlines, plainTextList]
  | x :: rest =>
    rw [shadeInlines, shadeInlines_text dim rest (out.push (shadeInline dim x))]
    simp [plainTextList, plainTextList_append, shadeInline_text dim x,
      String.append_assoc]

theorem shadeInline_text (dim : Color) (x : Inline) :
    plainTextOne (shadeInline dim x) = plainTextOne x := by
  match x with
  | .colored c n body =>
    rw [shadeInline]
    simp [plainTextOne, shadeInlines_text dim body.toList #[], plainTextList]
  | .styled st body =>
    rw [shadeInline]
    simp [plainTextOne, shadeInlines_text dim body.toList #[], plainTextList]
  | .link u body =>
    rw [shadeInline]
    simp [plainTextOne, shadeInlines_text dim body.toList #[], plainTextList]
  | .underline body =>
    rw [shadeInline]
    simp [plainTextOne, shadeInlines_text dim body.toList #[], plainTextList]
  | .step n last body =>
    rw [shadeInline]
    simp [plainTextOne, shadeInlines_text dim body.toList #[], plainTextList]
  | .text _ | .math _ _ | .fill | .pageNumber | .pageCount | .linebreak _ =>
    rfl

end

mutual

theorem shadeBlockList_text (dim : Color) (xs : List Block) (out : Array Block)
    (acc : String) :
    blockTextList acc (shadeBlockList dim out xs).toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [shadeBlockList, blockTextList]
  | b :: rest =>
    rw [shadeBlockList,
      shadeBlockList_text dim rest (out.push (shadeBlock dim b)) acc]
    simp [blockTextList, blockTextList_chain, shadeBlock_text dim b]

theorem shadeBlock_text (dim : Color) (b : Block) (acc : String) :
    blockTextOne acc (shadeBlock dim b) = blockTextOne acc b := by
  match b with
  | .para content =>
    rw [shadeBlock]
    simp [blockTextOne, plainText, plainTextList, plainTextOne,
      shadeInlines_text dim content.toList #[]]
  | .list o items =>
    rw [shadeBlock]
    simp [blockTextOne, shadeItems_text dim items.toList #[] acc, blockTextItems]
  | .center body =>
    rw [shadeBlock]
    simp [blockTextOne, shadeBlockList_text dim body.toList #[] acc, blockTextList]
  | .spaced g body =>
    rw [shadeBlock]
    simp [blockTextOne, shadeBlockList_text dim body.toList #[] acc, blockTextList]
  | .columns cols =>
    rw [shadeBlock]
    simp [blockTextOne, shadeColumns_text dim cols.toList #[] acc, blockTextColumns]
  | .step n last body =>
    rw [shadeBlock]
    simp [blockTextOne, shadeBlockList_text dim body.toList #[] acc, blockTextList]
  | .verbatim c s => rfl
  | .section _ _ _ | .note _ | .frame _ _ _ _ | .framefoot _ => rfl

theorem shadeItems_text (dim : Color) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (shadeItems dim out items).toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [shadeItems, blockTextItems]
  | item :: rest =>
    rw [shadeItems,
      shadeItems_text dim rest (out.push (shadeBlockList dim #[] item.toList)) acc]
    simp [blockTextItems, blockTextItems_chain,
      shadeBlockList_text dim item.toList #[], blockTextList]

theorem shadeColumns_text (dim : Color) (cols : List (Option Nat × Array Block))
    (out : Array (Option Nat × Array Block)) (acc : String) :
    blockTextColumns acc (shadeColumns dim out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [shadeColumns, blockTextColumns]
  | (w, body) :: rest =>
    rw [shadeColumns,
      shadeColumns_text dim rest
        (out.push (w, shadeBlockList dim #[] body.toList)) acc]
    simp [blockTextColumns, blockTextColumns_chain,
      shadeBlockList_text dim body.toList #[], blockTextList]

end

/-- Shading preserves every character: covered content is recoloured,
never removed. -/
theorem shadeBlocks_text (dim : Color) (xs : Array Block) :
    blocksText (shadeBlocks dim xs) = blocksText xs := by
  simp [blocksText, shadeBlocks, shadeBlockList_text dim xs.toList #[] "",
    blockTextList]

mutual

theorem dimInlineList_text (dim : Color) (k : Nat) (xs : List Inline)
    (out : Array Inline) :
    plainTextList (dimInlineList dim k out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [dimInlineList, plainTextList]
  | x :: rest =>
    rw [dimInlineList, dimInlineList_text dim k rest]
    simp [plainTextList, plainTextList_append, dimInline_text dim k x,
      String.append_assoc]

theorem dimInline_text (dim : Color) (k : Nat) (x : Inline) :
    plainTextOne (dimInline dim k x) = plainTextOne x := by
  match x with
  | .styled st body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text dim k body.toList #[], plainTextList]
  | .colored c nm body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text dim k body.toList #[], plainTextList]
  | .link u body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text dim k body.toList #[], plainTextList]
  | .underline body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text dim k body.toList #[], plainTextList]
  | .step n last body =>
    rw [dimInline]
    by_cases h : stepPending n last k = true
    · simp [h, plainTextOne, plainTextList,
        shadeInlines_text dim body.toList #[]]
    · simp [h, plainTextOne, dimInlineList_text dim k body.toList #[],
        plainTextList]
  | .text _ | .math _ _ | .fill | .pageNumber | .pageCount | .linebreak _ =>
    rfl

end

mutual

theorem dimBlockList_text (dim : Color) (k : Nat) (xs : List Block)
    (out : Array Block) (acc : String) :
    blockTextList acc (dimBlockList dim k out xs).toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [dimBlockList, blockTextList]
  | b :: rest =>
    rw [dimBlockList, dimBlockList_text dim k rest]
    simp [blockTextList, blockTextList_chain, dimBlock_text dim k b]

theorem dimBlock_text (dim : Color) (k : Nat) (b : Block) (acc : String) :
    blockTextOne acc (dimBlock dim k b) = blockTextOne acc b := by
  match b with
  | .para content =>
    rw [dimBlock]
    simp [blockTextOne, plainText, dimInlines,
      dimInlineList_text dim k content.toList #[], plainTextList]
  | .list o items =>
    rw [dimBlock]
    simp [blockTextOne, dimItems_text dim k items.toList #[] acc, blockTextItems]
  | .center body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text dim k body.toList #[] acc, blockTextList]
  | .spaced g body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text dim k body.toList #[] acc, blockTextList]
  | .columns cols =>
    rw [dimBlock]
    simp [blockTextOne, dimColumns_text dim k cols.toList #[] acc, blockTextColumns]
  | .step n last body =>
    rw [dimBlock]
    by_cases h : stepPending n last k = true
    · simp [h, blockTextOne, shadeBlocks,
        shadeBlockList_text dim body.toList #[] acc, blockTextList]
    · simp [h, blockTextOne, dimBlockList_text dim k body.toList #[] acc,
        blockTextList]
  | .verbatim _ _ | .section _ _ _ | .note _ | .frame _ _ _ _ | .framefoot _ => rfl

theorem dimItems_text (dim : Color) (k : Nat) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (dimItems dim k out items).toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [dimItems, blockTextItems]
  | item :: rest =>
    rw [dimItems, dimItems_text dim k rest]
    simp [blockTextItems, blockTextItems_chain,
      dimBlockList_text dim k item.toList #[], blockTextList]

theorem dimColumns_text (dim : Color) (k : Nat)
    (cols : List (Option Nat × Array Block))
    (out : Array (Option Nat × Array Block)) (acc : String) :
    blockTextColumns acc (dimColumns dim k out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [dimColumns, blockTextColumns]
  | (w, body) :: rest =>
    rw [dimColumns, dimColumns_text dim k rest]
    simp [blockTextColumns, blockTextColumns_chain,
      dimBlockList_text dim k body.toList #[], blockTextList]

end

/-- Nothing vanishes: page `k` of a stepped frame carries every character
the frame carries — dimming recolours pending content, it never hides it.
The union of what the steps show is therefore the whole content. -/
theorem dimBlocks_text (dim : Color) (k : Nat) (xs : Array Block) :
    blocksText (dimBlocks dim k xs) = blocksText xs := by
  simp [blocksText, dimBlocks, dimBlockList_text dim k xs.toList #[] "",
    blockTextList]

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
    s!"palette {n} #{hex2 c.r}{hex2 c.g}{hex2 c.b}{mark}\n")
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
     else "")
  let infoLines :=
    metaLine "title" doc.info.title ++ metaLine "author" doc.info.author ++
    metaLine "subject" doc.info.subject ++ metaLine "keywords" doc.info.keywords
  let asserts := String.join (doc.asserts.toList.map fun a =>
    s!"assert {a.kind.source}\n")
  let body := dumpBlocks "" doc.body
  let ds :=
    if diags.isEmpty then
      "-- diagnostics\n(none)\n"
    else
      "-- diagnostics\n" ++ String.join (diags.toList.map dumpDiag)
  head ++ page ++ fontLines ++ paletteLines ++ tokenLines ++ runLines ++ infoLines ++ asserts ++ body ++ ds

end LeanTex.Core.Ir
