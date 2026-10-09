module

public import LeanTex.Core.Diag
public import LeanTex.Core.Heading
public import LeanTex.Core.Dim
public import LeanTex.Core.Decl
public import LeanTex.Core.Image
public import LeanTex.Core.Math
public import LeanTex.Core.LocaleContract
public import LeanTex.Core.ListingHighlight
import LeanTex.Core.Loop
import Init.Data.Nat.ToString
public import Std.Data.HashMap

namespace LeanTex.Core.Ir

open LeanTex.Core LeanTex.Core.Dim

/-- The base font size every relative measure hangs off. It lives in the IR
because both backends read it: layout sets body text at this size, and HTML
derives its content measure from the page's text width in these units. -/
@[expose] public def baseFontSize : Sp := Dim.pt 10

/-- The leading ratio, per-mille: baselines sit at 6⁄5 of the size — the
routine text setting, 10/12 of Bringhurst's "settings such as 9/11, 10/12,
11/13 and 12/15 are routine" (Elements §2.2.1). It lives in the IR because
both backends read it: `leadingFor` applies it to every baseline distance
the PDF sets (the math grid included), and the HTML stylesheet emits it as
the heading line-height. -/
@[expose] public def leadingMilli : Nat := 1200

/-- Baseline distance for a size: `leadingMilli` of it, scaled by the page's
`leading` factor (`\linespread`'s home). The factor is where a document
declares the extra lead a wide measure wants; the engine never raises it
silently.

This is also the vertical rhythm's unit: the leading — not the font size —
"is the basic rhythmical unit" (Bringhurst §2.2.2), and it is a definition,
not a stored value — the rhythm moves with `\page{ fontsize }` and
`\linespread` because every reader re-derives it from its governing
context. It lives here, with the tokens it governs, because a guarantee
about tokens both backends read belongs where the tokens live, not inside
one consumer: the rhythm theorems below range over it, and each backend
owes its own realization of the gaps they quantize. -/
@[expose] public def leadingFor (size : Sp) (factor : Nat := 1000) : Sp :=
  size * (leadingMilli : Int) / 1000 * factor / 1000

/-- The rhythm's working quantum: the half-unit. Bringhurst §2.2.2 permits
half-lines in the measured intervals; every declared default vertical gap
is an integer number of these, which `default_rhythm_multiples` and
`caption_gaps_rhythm` state over the shipped defaults. -/
@[expose] public def rhythmQuantum (size : Sp) (factor : Nat := 1000) : Sp :=
  leadingFor size factor / 2

/-- The default gap between peer paragraphs: one rhythm quantum of the
governing size, half its leading (6pt at the 10pt base, 6.6pt at the
slides 11pt). Derivation-closed in the base size by construction —
`parskip_is_quantum` is `rfl` at every base — which is what makes a
uniform `\page{ fontsize }` scale the whole design (`\linespread` moves
the lines it declares, not the default gaps: the gap quantizes on the
base rhythm). A document declares its own through
`\page{ parskip = ... }`. -/
@[expose] public def parskipDefault (size : Sp) : SymGlue :=
  { width := Dim.Length.ofSp (rhythmQuantum size) }

/-- The rhythm quantum is positive at any body size of at least 1pt: the
one key fact every default-gap theorem consumes, proved once over the
arithmetic (`omega` over bare `Int`, the `slides_lines_survive_bands`
pattern) instead of once per consumer. -/
public theorem rhythmQuantum_pos (size : Int) (h : Dim.pt 1 ≤ size) :
    0 < rhythmQuantum size := by
  have hx : (65536 : Int) ≤ size := h
  show 0 < size * 1200 / 1000 * 1000 / 1000 / 2
  omega

/-- The comparison twin: the half-unit is strictly under the full unit, so
`≤` and `<` orderings between quantum multiples both read off this pair. -/
public theorem rhythmQuantum_lt_double (size : Int) (h : Dim.pt 1 ≤ size) :
    rhythmQuantum size < 2 * rhythmQuantum size := by
  have hx : (65536 : Int) ≤ size := h
  show size * 1200 / 1000 * 1000 / 1000 / 2
    < 2 * (size * 1200 / 1000 * 1000 / 1000 / 2)
  omega

/-- The default space between a cut mark's inner end and the trimmed page:
0.075 in, wider than the 1/16 in that published guillotine cutting
tolerances give as their outer bound (PrintNinja's pre-press guide,
Smartpress's cutting tolerance), so a cut within tolerance never meets a
mark. `\page{ mark-gap = ... }` overrides. -/
public def cutMarkGap : Sp := inch 3 / 40

/-- The default cut-mark thickness: a 0.5 bp hairline. This engine reads
`bp` as `pt` (`Decl.unitScaleBase`), so the value is 0.5 pt in sp.
`\page{ mark-thickness = ... }` overrides. -/
public def cutMarkThickness : Sp := pt 1 / 2

/-- The line-through rule thickness, 0.4 pt: ulem's default `\ULthickness`
(ulem.sty, 2019/11/18, `\def\ULthickness{0.4pt}`). The one source both
backends read — the PDF lowers a strike segment at this weight
(`Layout.lineThroughThickness` aliases this), and the HTML derives its
`text-decoration-thickness` from the same value (`HtmlDoc`), so a strike
is one weight on either artifact. -/
@[expose] public def lineThroughThickness : Sp := pt 2 / 5

/-- One rule a document draws on every page from a shipout hook
(`\AddToHook{shipout/background}{\put(x,y){\rule{w}{h}}}`, the kernel's
picture whose reference point is the page's top-left corner): its box in
medium coordinates, x right and y down from the medium's top-left corner,
and the palette name it is inked in. -/
public structure DrawnRule where
  x : Sp
  y : Sp
  w : Sp
  h : Sp
  color : String
  deriving Repr, BEq, Inhabited

/-- Page geometry, as declared by `\page`. -/
public structure PageSpec where
  width : Sp := pt 612
  height : Sp := pt 792
  /-- The vertical inch is a stated choice, not a derivation: the
  copy-fitting table that replaces the horizontal inch
  (`articleTextBlock`) sets only the measure, and no authority the engine
  follows names a vertical margin, so the letter-paper office convention
  stands. The horizontal default is replaced by the elaborator for an
  undeclared article page. -/
  vmargin : Sp := inch 1
  hmargin : Sp := inch 1
  /-- The body size, `\page{ fontsize = 11pt }` or the class option. The
  `slides` class defaults to `slidesFontSize`; everything else to
  `baseFontSize`. -/
  fontSize : Sp := baseFontSize
  /-- Line spacing as a factor over the default 1.2, in thousandths, so
  `\linespread{1.15}` has a home. -/
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
  /-- Whether the pages ship printer's cut marks (`\page{ marks = cut }`):
  eight hairlines inside the bleed strip, derived from the trim and bleed
  (`Layout.cutMarks`), never placed by hand. Off by default — a print
  shop that wants only the declared page boxes gets only boxes. -/
  marks : Bool := false
  /-- The clearance between a cut mark's inward end and the trim line it
  stops short of (`\page{ mark-gap = ... }`); `cutMarkGap` holds the
  default and its source. -/
  markGap : Sp := cutMarkGap
  /-- The cut marks' stroke thickness (`\page{ mark-thickness = ... }`);
  `cutMarkThickness` holds the default and its source. -/
  markThickness : Sp := cutMarkThickness
  /-- The document's size ladder, when a venue's refused size
  redefinitions were read out (per-mille of the body, `setStep`'s door;
  `PageSpec.scale` resolves). `none` is the engine's `sizeScale`. -/
  sizes : Option (List (String × Nat)) := none
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
  /-- Whether boundary glyphs protrude into the margin so the optical edge
  is straight — microtype's character protrusion (Thành, "Margin kerning
  and font expansion with pdfTeX", TUGboat 22(3); microtype manual §2),
  on by default as microtype's own `protrusion=true` is. `\page{
  protrusion = off }` or `\microtypesetup{protrusion=false}` opts out;
  `none` takes the default. -/
  protrude : Option Bool := none
  /-- Whether font boxes may expand within microtype's ±2% so the breaker
  gains a third degree of freedom (Thành, TUGboat 22(3); microtype manual
  §2), on by default as microtype's own `expansion=true` is. `\page{
  expansion = off }` or `\microtypesetup{expansion=false}` opts out;
  `none` takes the default. -/
  expand : Option Bool := none
  /-- Whether pages carry the physical page number, centred in the foot;
  `none` takes the class default (`ClassRecord.pageNumbers`). This is
  LaTeX's `plain` page style, spelled natively: `\page{ numbers = on }`
  is `\pagestyle{plain}`, `off` is `\pagestyle{empty}`'s number half. -/
  numbers : Option Bool := none
  /-- Whether counted body lines carry margin line numbers — lineno's
  `\linenumbers`, spelled natively `\page{ linenumbers = on }`. A declared
  flag, never a default: no class turns it on. Only the paged artifact
  draws the numbers — a line is a paged-media fact, and the HTML twin has
  no fixed lines to number, so it emits nothing (the recorded divergence;
  testdata/compat-index/lineno.txt carries it too). -/
  linenumbers : Option Bool := none
  /-- Print only line numbers divisible by this modulus, still counting
  every line — lineno's `\modulolinenumbers[n]`, whose counter initialises
  to 5 (lineno.sty, the user-commands section). `none` prints every
  counted line. -/
  lineModulo : Option Nat := none
  /-- The body-side furniture gap, in ink terms: the distance from the
  running head's and foot's body-side ink edge to the body area — one knob,
  both sides, which is what makes a flipped stack line up
  (`Layout.furniture_symmetric`). The natural declarations are rhythm
  multiples (`default_rhythm_multiples`' family: the half-unit 6 pt, the
  unit 12 pt at the 10 pt base). `none` is the default: the furniture
  hangs from half the margin and the body keeps its margin. -/
  furnitureGap : Option Sp := none
  /-- LaTeX's `\headsep`, as declared (the geometry key): it positions the
  header's *baseline* against the body. `Layout` reads it into the ink gap
  with the baseline-to-ink correction applied once (`furnGapOfSep`). -/
  headsep : Option Sp := none
  /-- LaTeX's `\footskip`, as declared: baseline to baseline, from the text
  area's floor to the foot's baseline, as LaTeX reads it
  (`Layout.latexFootY`); its declared difference from `headsep` is
  N0021's. -/
  footskip : Option Sp := none
  /-- LaTeX's `\flushbottom` (`some true`) or `\raggedbottom` (`some
  false`), natively `\page{ bottom = flush }`: whether a page the page
  builder broke stretches its glue to stand its last baseline on the text
  area's floor. `none` is the class's own, ragged for the flow classes, as
  article.cls declares for a one-sided document. -/
  flushBottom : Option Bool := none
  /-- The rules the document draws on every page (`DrawnRule`), in the
  order drawn. Eight that are exactly the cut marks of one trim declare
  that trim (`Layout.drawnTrim`). Only the paged artifact draws them: a
  rule anchored to the page's corner is a paged-media fact, and the HTML
  twin has no page corner to anchor it to — the recorded divergence cut
  marks and page boxes already make. -/
  drawn : Array DrawnRule := #[]
  /-- The document declares page boxes in a spelling the engine cannot
  evaluate — a page attribute assigned at shipout, as `\pdfvariable
  pageattr` is, whose values an `\edef` computes — so the trim its drawn
  cut marks cut stands for them (`Layout.drawnTrim`). Undeclared, drawn
  marks declare no trim, as in LaTeX, whose file then has no box but the
  medium. Natively `\page{ trim = marks }`. -/
  trimMarked : Bool := false
  deriving Repr, BEq, Inhabited

/-- The text block of an undeclared letter page: 26 picas (312 pt).
Bringhurst's copy-fitting table sets a text face whose lowercase alphabet
runs 130 pt — the middle of the 10 pt text-face range — on a measure of
about 26 picas for a single column (Elements of Typographic Style §2.1.2
and its table, as abridged in the memoir manual, Table 2.2). The
word-processor inch this replaces gave a 468 pt line, roughly a hundred
characters at 10 pt — the measure the band diagnostic exists to catch. A
document that declares any `\page` geometry keeps every value it named. -/
public def articleTextBlock : Sp := pt 312

/-- The slides stage and its defaults, beamer's own where beamer names one:
128×96 mm (the guide's "slides are by default only 128mm by 96mm large"),
160×90 mm at `aspectratio=169`, side text margins of 1 cm ("the left and
right margins, which default to 1 cm"), and an 11 pt base — beamer's
documented default font size, chosen so that "between 10 and 20 lines
should fit on each slide" and it is "difficult to fit too much onto a
slide" (beamer user guide §5.6.1, §18.2.1). The vertical margin is the
engine's own, for the pages that carry no footline — a section page, a
standout, the title page, an unthemed deck; a page that carries moloch's
footline takes beamer's own text area instead, the paper's top edge down to
the footline (`Layout.footFloor`). Being the engine's own, it is derived,
not chosen: two lines of the slides context's own rhythm (its earlier
spelling, 9 mm, missed that by 0.888 pt — a free scalar for no reason).
The lines-per-slide theorem in Layout is what holds these numbers
together. -/
@[expose] public def slidesStage43 : Sp × Sp := (Dim.mm 128, Dim.mm 96)
@[expose] public def slidesStage169 : Sp × Sp := (Dim.mm 160, Dim.mm 90)

/-- The slides stages, beamer's `aspectratio` table entire (beamer user
guide §8.1, the `aspectratio=` class option; the millimetre pairs are
`beamer.cls`'s own: 1610 → 160×100, 169 → 160×90, 149 → 140×90,
141 → 148.5×105, 54 → 125×100, 32 → 135×90, 43 → 128×96). Each row is
named by its ratio as `\page{ size = ... }` spells it — `√2:1` by beamer's
own digits `141` — and `slidesStageNamed` matches with the colon elided,
so `aspectratio=169` and the native `16:9` select one row. The lines-fit
contract (`Layout.slides_lines_in_band`) quantifies over every row:
adding a stage is entering that contract. -/
@[expose] public def slidesStages : Array (String × Sp × Sp) :=
  #[("4:3", slidesStage43),
    ("16:9", slidesStage169),
    ("16:10", Dim.mm 160, Dim.mm 100),
    ("14:9", Dim.mm 140, Dim.mm 90),
    ("141", Dim.mm100 14850, Dim.mm 105),
    ("5:4", Dim.mm 125, Dim.mm 100),
    ("3:2", Dim.mm 135, Dim.mm 90)]

/-- The stage a ratio name selects, colon elided on both sides: `16:9`,
`169`, and beamer's option digits agree on one row. -/
public def slidesStageNamed (name : String) : Option (Sp × Sp) :=
  let strip := fun (s : String) => String.ofList (s.toList.filter (· != ':'))
  (slidesStages.find? fun r => strip r.1 == strip name).map (·.2)

public def slidesHMargin : Sp := Dim.mm 10
@[expose] public def slidesFontSize : Sp := Dim.pt 11
@[expose] public def slidesVMargin : Sp := 2 * leadingFor slidesFontSize

/-- The article page's vertical inch, restated as rhythm: the letter-paper
office convention (`PageSpec.vmargin`'s docstring) happens to be exactly
six units of the base context's leading — 72 pt over 12 pt — so the
default page's vertical frame is on the grid it did not know it was on.
Held here so neither side drifts: an edit to the base leading or the
margin that breaks the coincidence must say which convention it is
keeping. -/
public theorem vmargin_on_rhythm :
    ({} : PageSpec).vmargin = 6 * leadingFor baseFontSize := by decide

/-- The card class's legibility floor: an angular x-height of 0.2° at the
40 cm hand-held distance is 1.4 mm, the bound of the fluent-reading range
in Legge & Bigelow 2011. The class implies `text.xheight >=` this;
`card_floor_within_scale` ties it to the size scale. -/
public def cardXHeightFloor : Sp := Dim.mm100 140
/-- The poster class's body size: beamerposter's scale-1 normalsize,
24.88 pt — the size10.clo ladder magnified for its A0 calibration
(beamerposter.sty v1.13, the fontscale table's base row). `scale=` and
the named sizes multiply it through `\page{ fontsize }`. -/
public def posterFontSize : Sp := Dim.pt 2488 / 100

/-- The poster class's legibility floor: the same 3.5 mrad angular
x-height bound as the card's (the fluent-reading range, Legge & Bigelow
2011), at a 1 m viewing distance — 3.5 mm. No authority fixes how far a
reader stands from a poster, so the distance is derived from the body
size the class already sources: beamerposter's scale-1 A0 normalsize is
24.88 pt (`posterFontSize`), whose x-height at a text face's typical
0.437 x/em is 3.8 mm — fluent at 3.5 mrad out to ~1.1 m. So 1 m is the
stated convention (a poster's body is read up close; titles carry
further), and the floor accepts the calibration it is derived from at
every scale ≥ 1 while still catching an unscaled 10 pt article body
pasted on a board. A document's own `\assert{ text.xheight >= ... }`
takes control. -/
public def posterXHeightFloor : Sp := Dim.mm100 350

/-- The equality boundary is explicit: device-operator provenance cannot
silently enter a screen or contrast comparison. -/
public theorem Color.beq_screen_exact (a b : Color) :
    (a == b) = (a.r == b.r && a.g == b.g && a.b == b.b && a.cmyk == b.cmyk) := by rfl

/-- Equality for a lookup that selects source-bearing data. Screen equality
is intentionally weaker; any selection that can carry a PDF rider uses this
relation instead. -/
public def Color.sameSource (a b : Color) : Bool :=
  a == b && a.pdfModel == b.pdfModel

/-- A source-equal selection cannot exchange its PDF device provenance. -/
public theorem Color.sameSource_pdfModel_exact (a b : Color) :
    a.sameSource b = true → (a.pdfModel == b.pdfModel) = true := by
  simp [Color.sameSource]

@[expose] public def Color.black : Color := { r := 0, g := 0, b := 0 }

/-- xcolor's screen projection of one CMYK channel: `1 - min(1, c+k)`,
then the package's TeX-scaled conversion to an HTML byte. -/
private def Color.cmykPreviewByte (v k : Decl.ColorComponent) : UInt8 :=
  let scale := v.scale * k.scale
  let used := min scale (v.num * k.scale + k.num * v.scale)
  ({ num := scale - used, scale := scale } : Decl.ColorComponent).unitByte

/-- A CMYK value used by the engine's thousandth mix arithmetic. The exact
source constructor below uses the same preview rule while retaining finer
components for PDF. -/
public def Color.ofCmyk (c m y k : Nat) : Color :=
  let part (v : Nat) : Decl.ColorComponent := { num := min 1000 v, scale := 1000 }
  let black := part k
  { r := cmykPreviewByte (part c) black, g := cmykPreviewByte (part m) black,
    b := cmykPreviewByte (part y) black, cmyk := some (c, m, y, k) }

/-- The colour model a colour was declared in — read off the rider, never
stored twice. Every colour operation is closed in its first operand's
model (`mix_model_exact`), so a print colour reaches the PDF in the model
the document wrote it in, whatever expression it travelled through. -/
public inductive Color.Model where
  | srgb
  | cmyk
  deriving Repr, BEq, DecidableEq, Inhabited

public def Color.model (c : Color) : Color.Model :=
  match c.cmyk with
  | some _ => .cmyk
  | none => .srgb

/-- Thousandths as a PDF decimal: 830 ↦ "0.83". Built structurally over the
digit list so a statement over the printed form can close by evaluation
(`pdfMilli_decode`): `String.dropEndWhile`'s position recursion blocks
kernel reduction. -/
public def Color.pdfMilli (v : Nat) : String :=
  let v := min v 1000
  if v == 0 then "0" else if v == 1000 then "1"
  else
    let ds := Nat.toDigits 10 v
    let ds := List.replicate (3 - ds.length) '0' ++ ds
    "0." ++ String.ofList (ds.reverse.dropWhile (· == '0')).reverse

/-- An 8-bit channel in thousandths, rounded half up: the one quantization
between the IR's sRGB bytes and the PDF's decimals. 256 values land on 256
distinct thousandths (`milli_inj`), so the PDF never merges two inks the
HTML keeps apart. -/
public def Color.milli (v : UInt8) : Nat := (v.toNat * 1000 + 127) / 255

/-- An HTML byte triple keeps its exact screen bytes and the five-decimal
DeviceRGB values xcolor's PDF driver derives from them. -/
public def Color.ofHtml (r g b : UInt8) : Color :=
  let part (v : UInt8) : Decl.ColorComponent := { num := v.toNat, scale := 1 }
  { r := r, g := g, b := b,
    pdfModel := some (.rgb (part r).pdfRgb (part g).pdfRgb (part b).pdfRgb) }

/-- An RGB-range source keeps decimal components until the PDF driver's
0–255 conversion and projects each independently to the HTML byte view. -/
public def Color.ofRgbByte (r g b : Decl.ColorComponent) : Color :=
  { r := r.rgbByte, g := g.rgbByte, b := b.rgbByte,
    pdfModel := some (.rgb r.pdfRgb g.pdfRgb b.pdfRgb) }

/-- A unit-rgb source keeps its exact components for PDF and uses xcolor's
fixed-point HTML projection for the shared screen view. -/
public def Color.ofRgbUnit (r g b : Decl.ColorComponent) : Color :=
  { r := r.unitByte, g := g.unitByte, b := b.unitByte,
    pdfModel := some (.rgb r.pdfUnit g.pdfUnit b.pdfUnit) }

/-- A gray source remains DeviceGray in PDF instead of becoming three equal
RGB channels; its screen preview is the same xcolor byte projection. -/
public def Color.ofGray (v : Decl.ColorComponent) : Color :=
  { r := v.unitByte, g := v.unitByte, b := v.unitByte,
    pdfModel := some (.gray v.pdfUnit) }

/-- A source CMYK value retains all decimal digits for DeviceCMYK. The
thousandth tuple is only the existing arithmetic projection used by mixes. -/
public def Color.ofCmykSource (c m y k : Decl.ColorComponent) : Color :=
  { r := cmykPreviewByte c k, g := cmykPreviewByte m k, b := cmykPreviewByte y k,
    pdfModel := some (.cmyk c.pdfUnit m.pdfUnit y.pdfUnit k.pdfUnit),
    cmyk := some (c.milli, m.milli, y.milli, k.milli) }

/-- PDF wants components in 0–1; three decimals is finer than 8-bit input. -/
@[expose] public def Color.pdfComponents (c : Color) : String :=
  pdfMilli (milli c.r) ++ " " ++ pdfMilli (milli c.g) ++ " " ++ pdfMilli (milli c.b)

/-- The fill-colour operation for this colour. Explicit source models keep
their device operator and exact validated components; native byte colours use
the established DeviceRGB projection, and legacy CMYK values keep their
thousandth rider. -/
public def Color.pdfFill (c : Color) : String :=
  match c.pdfModel with
  | some (.rgb r g b) => s!"{r} {g} {b} rg"
  | some (.gray v) => s!"{v} g"
  | some (.cmyk cy m y k) => s!"{cy} {m} {y} {k} k"
  | none => match c.cmyk with
    | some (cy, m, y, k) =>
      s!"{pdfMilli cy} {pdfMilli m} {pdfMilli y} {pdfMilli k} k"
    | none => s!"{c.pdfComponents} rg"

/-- The stroke-colour twin of `pdfFill`, with the corresponding uppercase
PDF operators. -/
public def Color.pdfStroke (c : Color) : String :=
  match c.pdfModel with
  | some (.rgb r g b) => s!"{r} {g} {b} RG"
  | some (.gray v) => s!"{v} G"
  | some (.cmyk cy m y k) => s!"{cy} {m} {y} {k} K"
  | none => match c.cmyk with
    | some (cy, m, y, k) =>
      s!"{pdfMilli cy} {pdfMilli m} {pdfMilli y} {pdfMilli k} K"
    | none => s!"{c.pdfComponents} RG"

/-- A colour declared in a model round-trips to that model in a backend
that supports it: the components the document declared are the components
the PDF paints with, exactly — never an RGB re-interpretation. -/
public theorem Color.cmyk_components_kept (c m y k : Nat) :
    (Color.ofCmyk c m y k).cmyk = some (c, m, y, k) ∧
    (Color.ofCmyk c m y k).pdfFill
      = s!"{pdfMilli c} {pdfMilli m} {pdfMilli y} {pdfMilli k} k" := by
  exact ⟨rfl, rfl⟩

/-- A native byte colour with no explicit device rider paints through the
established DeviceRGB projection. -/
public theorem Color.pdfFill_srgb (c : Color) (hm : c.pdfModel = none) (hc : c.cmyk = none) :
    c.pdfFill = s!"{c.pdfComponents} rg" := by
  simp [Color.pdfFill, hm, hc]

/-- Each exact source model selects its own PDF operator and keeps the
validated component spellings. -/
public theorem Color.pdf_models_exact (r g b c m y k : Decl.ColorComponent) :
    (Color.ofRgbUnit r g b).pdfFill = s!"{r.pdfUnit} {g.pdfUnit} {b.pdfUnit} rg" ∧
    (Color.ofGray r).pdfFill = s!"{r.pdfUnit} g" ∧
    (Color.ofCmykSource c m y k).pdfFill =
      s!"{c.pdfUnit} {m.pdfUnit} {y.pdfUnit} {k.pdfUnit} k" := by
  exact ⟨rfl, rfl, rfl⟩

/-- The reader of `pdfMilli`'s output: `"1"` ↦ 1000, `"0.d…"` ↦ the digits
padded to three, anything else 0. Exists for `pdfMilli_decode`. -/
public def Color.decodeMilli (s : String) : Nat :=
  match s.toList with
  | '0' :: '.' :: ds =>
    (ds ++ List.replicate (3 - ds.length) '0').foldl
      (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0
  | cs => if cs == ['1'] then 1000 else 0

/-- Every thousandth the PDF can print reads back as itself. -/
public theorem Color.pdfMilli_decode : ∀ v < 1001, decodeMilli (pdfMilli v) = v := by
  have digitZero (n : Nat) : (n.digitChar == '0') = (n == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Nat.digitChar_eq_zero]
  intro v hv
  have hmin : min v 1000 = v := Nat.min_eq_left (by omega)
  by_cases hz : v = 0
  · subst v
    rfl
  by_cases hunit : v = 1000
  · subst v
    rfl
  have hn : v < 1000 := by omega
  simp only [pdfMilli, hmin, beq_iff_eq, hz, hunit, ↓reduceIte]
  unfold decodeMilli
  rw [String.toList_append, String.toList_ofList]
  by_cases hten : v < 10
  · rw [Nat.toDigits_of_lt_base hten]
    simp [hz, Nat.toNat_digitChar_of_lt_ten hten]
  · rw [Nat.toDigits_of_base_le (by decide) (by omega : 10 ≤ v)]
    by_cases hhundred : v < 100
    · have hq : v / 10 < 10 := by omega
      have hq0 : v / 10 ≠ 0 := by omega
      have hqz : (v / 10 == 0) = false := beq_eq_false_iff_ne.mpr hq0
      have hr : v % 10 < 10 := by omega
      rw [Nat.toDigits_of_lt_base hq]
      by_cases hlast : v % 10 = 0
      · simp [List.dropWhile, digitZero, hqz, hlast,
          Nat.toNat_digitChar_of_lt_ten hq]
        omega
      · simp [hlast, Nat.toNat_digitChar_sub_48_of_lt_ten hq,
          Nat.toNat_digitChar_sub_48_of_lt_ten hr]
        omega
    · have hq : v / 10 / 10 < 10 := by omega
      have hq0 : v / 10 / 10 ≠ 0 := by omega
      have hqz : (v / 10 / 10 == 0) = false := beq_eq_false_iff_ne.mpr hq0
      have hm : v / 10 % 10 < 10 := by omega
      have hr : v % 10 < 10 := by omega
      rw [Nat.toDigits_of_base_le (by decide) (by omega : 10 ≤ v / 10)]
      rw [Nat.toDigits_of_lt_base hq]
      by_cases hlast : v % 10 = 0
      · by_cases hmiddle : v / 10 % 10 = 0
        · simp [List.dropWhile, digitZero, hqz, hlast, hmiddle,
            Nat.toNat_digitChar_of_lt_ten hq]
          omega
        · have hmz : (v / 10 % 10 == 0) = false := beq_eq_false_iff_ne.mpr hmiddle
          simp [List.dropWhile, digitZero, hlast, hmz,
            Nat.toNat_digitChar_sub_48_of_lt_ten hq,
            Nat.toNat_digitChar_sub_48_of_lt_ten hm]
          omega
      · simp [hlast, Nat.toNat_digitChar_sub_48_of_lt_ten hq,
          Nat.toNat_digitChar_sub_48_of_lt_ten hm,
          Nat.toNat_digitChar_sub_48_of_lt_ten hr]
        omega

/-- 256 channel values land on 256 distinct thousandths. -/
public theorem Color.milli_inj (a b : UInt8) (h : milli a = milli b) : a = b := by
  have ha : a.toNat < 256 := a.toNat_lt
  have hb : b.toNat < 256 := b.toNat_lt
  simp only [milli] at h
  exact UInt8.toNat_inj.mp (by omega)

public theorem Color.milli_lt (a : UInt8) : milli a < 1001 := by
  have := a.toNat_lt
  simp only [milli]
  omega

/-- The colour printer's marks paint in. ISO 32000-2 §8.6.6.4 names the
special colorant `All` — "useful for purposes such as painting
registration targets", ink on every separation — and DeviceCMYK 1,1,1,1
is its device spelling when the document declares print colours: the
marks then render on all four plates, as ISO 12647-conforming proofs
expect of registration marks. A document that declares no CMYK colour
has no separations to register, so its honest mark colour is plain
black. -/
public def Color.registration (printModel : Bool) : Color :=
  if printModel then Color.ofCmyk 1000 1000 1000 1000 else Color.black

/-- Named lengths declared by `\tokens`, in declaration order so a later
token may be defined in terms of an earlier one. -/
public structure Tokens where
  entries : Array (String × SymGlue) := #[]
  deriving Repr, BEq, Inhabited

public def Tokens.find? (t : Tokens) (name : String) : Option SymGlue :=
  (t.entries.find? (·.1 == name)).map (·.2)

/-- A resolved value beside the declaration it was resolved from. The
engine resolves a token at elaboration because the page needs a length;
the HTML needs the *name* as well, since a rule can only defer to a
reader's override by referencing the custom property by name
(`var(--separatorgap, …)`). A field carrying the bare value therefore
reaches one backend complete and the other blind — the shape that left
five declared tokens wired to nothing while `separator`, whose name rode
beside its colour on the same constructor, worked.

The name belongs here rather than inside `SymGlue` because provenance is
a property of the *reference*, not of the length: `SymGlue.add` has no
answer for the name of a sum of two tokens, and a derived `BEq` over a
value carrying its origin would call two equal lengths unequal. A
computed glue is `none` by construction, which is the honest answer. -/
public structure Sourced (α : Type) where
  value : α
  /-- The declared name the value came from, when it came from one. -/
  token : Option String
  deriving Repr, BEq, Inhabited

/-- A value with no declaration behind it: a computed glue, a class
default, an engine rhythm quantum. -/
@[expose] public def Sourced.bare {α : Type} (v : α) : Sourced α := { value := v, token := none }

/-- A token read for a value a backend will show, which is the only kind
of read that needs the name: the answer carries the name it was asked
for, so nothing downstream can resolve a token and forget where it came
from. `Tokens.find?` stays for the reads whose answer is consumed
arithmetically and has no name to keep. -/
public def Tokens.findSourced? (t : Tokens) (name : String) : Option (Sourced SymGlue) :=
  (t.find? name).map fun g => { value := g, token := some name }

/-- The lookup names what it was asked for and changes nothing else: the
value is `find?`'s, and the name is the key. This is what holds the
provenance channel honest — a `findSourced?` that dropped or renamed the
key would fail here rather than silently emitting a rule no reader can
override. -/
public theorem findSourced?_names (t : Tokens) (name : String) :
    (t.findSourced? name).map (·.value) = t.find? name ∧
      ∀ s ∈ t.findSourced? name, s.token = some name := by
  constructor
  · cases h : t.find? name <;> simp [Tokens.findSourced?, h]
  · intro s hs
    cases h : t.find? name <;> simp [Tokens.findSourced?, h] at hs
    exact hs ▸ rfl

/-- Replace-on-redeclare: a later declaration overrides, keeping one entry
per name. The one install mechanism — a document's `\tokens` and a theme's
bundle go through the same door. -/
public def Tokens.declare (t : Tokens) (key : String) (g : SymGlue) : Tokens :=
  { entries := (t.entries.filter (·.1 != key)).push (key, g) }

/-- The two halves of keyed last-wins, over the one keyed store both
`Tokens.declare` and `Palette.declare` are built on: the declared value is
the one read back, and a redeclaration collapses — declaring a key twice is
declaring the later value once. Public: `Theme`'s install fold runs the
same store step, so its lemmas consume these rather than re-proving them. -/
public theorem declare_find_eq {α : Type} (xs : Array (String × α)) (k : String) (v : α) :
    ((xs.filter (·.1 != k)).push (k, v)).find? (·.1 == k) = some (k, v) := by
  have hnone : (xs.filter (·.1 != k)).find? (·.1 == k) = none := by
    rw [Array.find?_eq_none]
    intro x hx
    have hne := (Array.mem_filter.mp hx).2
    simpa using hne
  rw [Array.find?_push, hnone]
  simp

private theorem declare_collapse {α : Type} (xs : Array (String × α)) (k : String) (v : α) :
    ((xs.filter (·.1 != k)).push (k, v)).filter (·.1 != k) = xs.filter (·.1 != k) := by
  rw [Array.filter_push]
  simp

/-- The locality half over the same store: a declaration changes exactly
the key it names — every other key reads back as before. -/
public theorem declare_keeps {α : Type} (xs : Array (String × α)) (k k' : String) (v : α)
    (h : k' ≠ k) :
    ((xs.filter (·.1 != k)).push (k, v)).find? (·.1 == k') = xs.find? (·.1 == k') := by
  rw [Array.find?_push, Array.find?_filter]
  have hpred : (fun a : String × α => decide ((a.fst != k) = true ∧ (a.fst == k') = true))
      = (fun a : String × α => a.fst == k') := by
    funext x
    by_cases hx : (x.1 == k') = true
    · have hxe : x.1 = k' := by simpa using hx
      simp [hxe, h]
    · simp [hx]
  rw [hpred]
  have hkk : (k == k') = false := by
    simpa using fun hk => h hk.symm
  simp [hkk]

/-- Keyed last-wins, read side (T2): `\tokens{ k = v }` means `find? k` is
`v`, whatever was declared before. -/
public theorem Tokens.declare_last_wins (t : Tokens) (k : String) (g : SymGlue) :
    (t.declare k g).find? k = some g := by
  unfold declare find?
  rw [declare_find_eq]
  rfl

/-- Keyed last-wins, write side (T2): redeclaring a key overwrites — the
earlier value leaves no residue, so same-key order is the only order two
`\tokens` blocks carry. -/
public theorem Tokens.declare_overwrite (t : Tokens) (k : String) (g g' : SymGlue) :
    (t.declare k g).declare k g' = t.declare k g' := by
  unfold declare
  rw [declare_collapse]

/-- An override changes exactly what it names (T2's locality half, the
`Tokens` twin of `Palette.declare_keeps_others`): every other token
resolves as it did before. -/
public theorem Tokens.declare_keeps_others (t : Tokens) (k k' : String) (g : SymGlue)
    (h : k' ≠ k) : (t.declare k g).find? k' = t.find? k' := by
  unfold declare find?
  rw [declare_keeps _ _ _ _ h]

-- Table rule weights and paddings: booktabs' documented defaults
-- (booktabs.dtx v1.61803398, §"The code": `\heavyrulewidth=.08em
-- \lightrulewidth=.05em \cmidrulewidth=.03em \belowrulesep=.65ex
-- \aboverulesep=.4ex \abovetopsep=0pt \belowbottomsep=0pt
-- \cmidrulekern=.5em \defaultaddspace=.5em`). booktabs is this engine's
-- table layout, not a package: "what distinguishes these from plain LaTeX
-- tables is the default use of additional space above and below rules, and
-- rules of varying 'thickness'" (booktabs.dtx §Introduction) — the padding
-- is part of the rule, never left to the author. Em/ex-relative as the
-- package spells them, and resolved as it assigns them: once, in the
-- preamble's font (`PreambleFace`), so a table at any size, in any face,
-- keeps the lengths lualatex gives it (2.88597pt of `\belowrulesep` in a
-- 10pt deck, 2.80147pt in a 10pt article). Each is overridable through
-- `\tokens{ <latex name> = ... }` under its LaTeX name, which resolves where
-- the table stands, as a `\setlength` in the body does.

/-- `\toprule`/`\bottomrule` weight: booktabs `\heavyrulewidth` (.08em). -/
public def heavyRuleWidth : Dim.Length := { em := 80 }
/-- `\midrule` weight: booktabs `\lightrulewidth` (.05em). -/
public def lightRuleWidth : Dim.Length := { em := 50 }
/-- `\cmidrule` weight: booktabs `\cmidrulewidth` (.03em). -/
public def cmidRuleWidth : Dim.Length := { em := 30 }
/-- Space under a rule, above the content it heads: booktabs
`\belowrulesep` (.65ex). -/
public def belowRuleSep : Dim.Length := { ex := 650 }
/-- Space over a rule, under the content above it: booktabs `\aboverulesep`
(.4ex). -/
public def aboveRuleSep : Dim.Length := { ex := 400 }
/-- Space over a `\toprule`: zero — "which seems sensible for a rule
designed to go at the top" (booktabs.dtx); the float's own caption gap
owns that space here. -/
public def aboveTopSep : Dim.Length := {}
/-- Space under a `\bottomrule`: zero, as booktabs' `\belowbottomsep`. -/
public def belowBottomSep : Dim.Length := {}
/-- Default end-trim of a trimmed `\cmidrule`: booktabs `\cmidrulekern`
(.5em). -/
public def cmidRuleKern : Dim.Length := { em := 500 }
/-- `\addlinespace` default: booktabs `\defaultaddspace` (.5em). -/
public def defaultAddSpace : Dim.Length := { em := 500 }
/-- Half the gap between two table columns: LaTeX's `\tabcolsep` — "the
columns in a tabular environment are separated by 2\tabcolsep", 6pt
(classes.dtx §Array and tabular). An `@{}` in the column spec deletes the
outer pad, as in LaTeX. -/
public def tabColSep : Dim.Length := { sp := Dim.pt 6 }
/-- The gap between text columns: LaTeX's `\columnsep`, 10pt
(classes.dtx §Multicolumn). Paracol subtracts it before sharing the
remaining measure (`\pcol@setcolwidth@r`). -/
public def columnSep : Dim.Length := { sp := Dim.pt 10 }
/-- Two stacked full rules separate by LaTeX's `\doublerulesep`, 2pt
(classes.dtx §Array and tabular) — drawn, but warned: "never use double
rules" (booktabs.dtx §The layout of formal tables). -/
public def doubleRuleSep : Dim.Length := { sp := Dim.pt 2 }

/-- The lengths a formal table reads, under their LaTeX names, each with the
default it takes undeclared. One table both backends read — the layout's
rows and rules (`Layout.tableLength`), the stylesheet's fallbacks
(`HtmlDoc.tableLengthFallback`) — so the length a page sets its table by is
the length the stage states. -/
public def tableLengths : List (String × Dim.Length) :=
  [("tabcolsep", tabColSep), ("doublerulesep", doubleRuleSep),
   ("heavyrulewidth", heavyRuleWidth), ("lightrulewidth", lightRuleWidth),
   ("cmidrulewidth", cmidRuleWidth), ("cmidrulekern", cmidRuleKern),
   ("aboverulesep", aboveRuleSep), ("belowrulesep", belowRuleSep),
   ("abovetopsep", aboveTopSep), ("belowbottomsep", belowBottomSep)]

/-- A table length's default (`tableLengths`); zero for a name it lacks. -/
public def tableLengthDefault (name : String) : Dim.Length :=
  (tableLengths.lookup name).getD {}

/-- latex.ltx's three vertical skip registers at their kernel values, the
same in every class (ltspace.dtx, as plain.tex sets them): what `\smallskip`,
`\medskip` and `\bigskip` spend, and beamer's block template above its title
box and below its body box (beamerinnerthemedefault.sty, `\medskipamount`
and `\smallskipamount`), where the document never sets them. -/
public def kernelSkip : String → Option SymGlue
  | "smallskipamount" =>
    some { width := .ofSp (Dim.pt 3), stretch := .ofSp (Dim.pt 1), shrink := .ofSp (Dim.pt 1) }
  | "medskipamount" =>
    some { width := .ofSp (Dim.pt 6), stretch := .ofSp (Dim.pt 2), shrink := .ofSp (Dim.pt 2) }
  | "bigskipamount" =>
    some { width := .ofSp (Dim.pt 12), stretch := .ofSp (Dim.pt 4), shrink := .ofSp (Dim.pt 4) }
  | _ => none

/-- The one resolving site for a skip register: the value the document set
it to (`\setlength{\medskipamount}`, a token of the register's name), else
the kernel's. Both backends read it — the PDF walk around a block, the HTML
gap sheet's block boundaries — as TeX's `\vskip\medskipamount` reads the
register in force. -/
public def skipAmount (tokens : Tokens) (name : String) : SymGlue :=
  (tokens.find? name).getD ((kernelSkip name).getD {})

/-- The three rule weights are a hierarchy, not three loose numbers: "the
top and bottom rules are heavier than the middle rule, which is in turn
heavier than the subrule" (booktabs.dtx §Introduction, of its own first
example). A weight edit that flattens the hierarchy fails the build. -/
public theorem rule_weights_ordered :
    0 < cmidRuleWidth.em ∧ cmidRuleWidth.em < lightRuleWidth.em ∧
    lightRuleWidth.em < heavyRuleWidth.em := by decide

/-- A rule clears more below than above: booktabs' `\belowrulesep` (.65ex)
against `\aboverulesep` (.4ex) — a rule binds to the content it closes and
clears the content it heads, which is exactly the "space above and below
rules" the package exists to add. -/
public theorem rule_seps_ordered : 0 < aboveRuleSep.ex ∧ aboveRuleSep.ex < belowRuleSep.ex := by
  decide

-- Float and caption separation. LaTeX's rule has a side to it, not just
-- an ordering: `\caption` pays `\abovecaptionskip` (10pt, classes.dtx
-- 10pt option) between the float's object and its caption, and
-- `\belowcaptionskip` (0pt) on the caption's far side — the text side is
-- the float separation the text already has (`\intextsep`, 12pt). For a
-- caption above its table the caption package's `tableposition=top`
-- swaps the pair (caption manual §2.2; venue classes do it by hand), so
-- the caption gap stays on the OBJECT side whichever side the caption
-- stands. A symmetric gap would double-count one side and starve the
-- other. The engine keeps that shape — `captionsep` is the object-side
-- gap, `floatsep` both text-side gaps (`Layout.floatPlan`) — and
-- quantizes both to the vertical rhythm (Bringhurst §2.2.2,
-- `default_rhythm_multiples` below): the caption gap is the half-unit
-- (6pt at the 10pt base, the rhythm-aligned stand-in for LaTeX's 10pt,
-- which is a multiple of nothing here), the float gap one full unit
-- (12pt, exactly `\intextsep`). No authority fixes the caption gap's
-- absolute value; the half-unit is the smallest rhythm multiple that
-- keeps LaTeX's ordering.

/-- Gap between a float's object and its caption — the object side only;
the caption's text side is `floatSepDefault` (the sourcing note above).
One rhythm quantum of the governing size. Overridable as
`\tokens{ captionsep = ... }` or the caption package's `skip=` key. -/
@[expose] public def captionSepDefault (size : Sp) : SymGlue :=
  { width := { sp := rhythmQuantum size } }
/-- Gap between a float and the text around it: one full rhythm unit of
the governing size. Overridable as `\tokens{ floatsep = ... }`. -/
@[expose] public def floatSepDefault (size : Sp) : SymGlue :=
  { width := { sp := 2 * rhythmQuantum size } }

/-- Gap between the last body line and the footnote region: `\skip\footins`
(classes.dtx, the 10pt option: 9pt plus 4pt minus 2pt), quantized to the
rhythm — two quanta, one full leading. The quantized value lies inside the
source glue's own range (7..13pt at the 10pt base, `footins_within_glue`),
so it is a length LaTeX's own glue could set. Overridable as
`\tokens{ footins = ... }`. -/
public def footinsDefault (size : Sp) : SymGlue :=
  { width := { sp := 2 * rhythmQuantum size } }

/-- The quantized `\skip\footins` is on the rhythm and inside the source
glue's own rubber range at the base it was sourced at: 9−2 ≤ 12 ≤ 9+4 pt.
An edit that moves the default off the grid or outside what the LaTeX glue
could legally set fails the build here. -/
public theorem footins_within_glue :
    (footinsDefault baseFontSize).width.sp = 2 * rhythmQuantum baseFontSize ∧
    Dim.pt 7 ≤ (footinsDefault baseFontSize).width.sp ∧
    (footinsDefault baseFontSize).width.sp ≤ Dim.pt 13 := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- The space a trivlist environment — `{center}`, `{flushleft}`,
`{flushright}` (ltlists.dtx: `\center` is `\trivlist\centering\item`) —
opens against the text above and below it:
LaTeX's top-level `\topsep`, which the size file's `\@listi` sets
(size10.clo:218 `8pt plus 2pt minus 4pt`, size11.clo:218 `9pt plus 3pt
minus 5pt`, size12.clo:218 `10pt plus 4pt minus 6pt`) and beamer keeps at top
level — its own `\@listi` (beamerbaselocalstructure.sty:152) is invoked only
inside a list, measured under lualatex as `8.0pt plus 2.0pt minus 4.0pt` in
a 10pt frame. Quantized to the rhythm as the display skip is: one quantum,
inside each size file's own range (`trivlist_between`), with size10's rubber
proportions (a fifth of the body stretch, two fifths shrink). `\partopsep`
(size10.clo:215, 2–3 pt in article; 0 in beamer, beamerbaselocalstructure
.sty:164) is added by LaTeX only where the environment opens a new
paragraph; lists and quotes spend it (`partopsepFor`, `inParagraphRole`),
and this quantized space does not.
Overridable as `\tokens{ topsep = ... }` or `\setlength{\topsep}{...}`. -/
@[expose] public def trivlistSkipDefault (size : Sp) : SymGlue :=
  { width := { sp := rhythmQuantum size }
    stretch := { sp := size / 5 }
    shrink := { sp := size * 2 / 5 } }

/-- The trivlist space's token name, as `\tokens` and `\setlength` spell it. -/
public def trivlistSkipName : String := "topsep"

/-- The one resolving site for a trivlist's space: the document's token
where declared, else the rhythm default at the governing size. Both
backends read it — the PDF walk around a trivlist, the HTML base sheet's
`var(--topsep, …)` fallback the same default. -/
public def trivlistSkip (tokens : Tokens) (size : Sp) : SymGlue :=
  (tokens.find? trivlistSkipName).getD (trivlistSkipDefault size)

/-- natbib's hanging indent for an author-year reference list, `\bibhang`
(natbib.sty:637–638, `\setlength{\bibhang}{1em}`): the list's
`\leftmargin`, with `\itemindent` its negative (`\NAT@bibsetup`,
natbib.sty:642–644), so an entry's first line stands at the margin and
its continuation lines one hang in. A numbered list hangs its labels
instead (`\NAT@bibsetnum`, natbib.sty:627). The document's token where
declared — `\setlength{\bibhang}` spells it — else natbib's value; both
backends read it. -/
public def bibHangName : String := "bibhang"

public def bibHang (tokens : Tokens) : SymGlue :=
  (tokens.find? bibHangName).getD { width := { em := 1000 } }

/-- natbib's gap between reference-list entries, `\bibsep`: the list's
`\itemsep`, its `\parsep` zero (`\NAT@bibsetup`). natbib reads the default
from the class's first-level list when it loads (natbib.sty:639–640,
`\itemsep` plus `\parsep` of `\@listi`): size10.clo:216–219 sets each to
`4pt plus 2pt minus 1pt`, size11.clo `4.5pt plus 2pt minus 1pt`,
size12.clo `5pt plus 2.5pt minus 1pt`. Another base keeps size10's
proportions of its own size. -/
public def bibSepName : String := "bibsep"

public def bibSepDefault (size : Sp) : SymGlue :=
  let g (w s h : Sp) : SymGlue :=
    { width := { sp := w }, stretch := { sp := s }, shrink := { sp := h } }
  if size == Dim.pt 10 then g (Dim.pt 8) (Dim.pt 4) (Dim.pt 2)
  else if size == Dim.pt 11 then g (Dim.pt 9) (Dim.pt 4) (Dim.pt 2)
  else if size == Dim.pt 12 then g (Dim.pt 10) (Dim.pt 5) (Dim.pt 2)
  else g (size * 4 / 5) (size * 2 / 5) (size / 5)

/-- The one resolving site for the gap between reference-list entries: the
document's token where declared (`\setlength{\bibsep}`), else natbib's
default at the governing size; `bibList_default_exact` (BibContract.lean)
holds the undeclared values. -/
public def bibSep (tokens : Tokens) (size : Sp) : SymGlue :=
  (tokens.find? bibSepName).getD (bibSepDefault size)

/-- The role a trivlist environment's body rides in: the environment
opens space (`\topsep` above and below), the `\centering` and `\raggedright`
declarations open none, and both elaborate to the same `.center` or
`.ragged` scope — so the environment's scope is wrapped in this engine role,
as a title slot's is (`titleSlotRole`). A name no document command can
spell (it carries a hyphen), so no authored role collides with it. -/
public def trivlistRole : String := "trivlist-env"

/-- The role a list or a quote rides in when its `\begin` follows the
text of an open paragraph with no blank line or `\par` between: LaTeX's
`\@trivlist` finds horizontal mode there and adds no `\partopsep` to the
environment's `\topsep`, above or below (latex.ltx:15871-15878), where in
vertical mode — after a blank line, another list, a scope's start — it
does (`partopsepFor`). A name no document command can spell (it carries a
hyphen), as `trivlistRole`'s is. -/
public def inParagraphRole : String := "in-paragraph"

/-- The role `\vspace*` rides in, an empty marker just before the space it
keeps: LaTeX's `\@vspacer` sets a zero rule ahead of the space
(latex.ltx:9374-9390), and a rule is where TeX's page builder stops
discarding at a page's top, so the space after it stays there, with
`\topskip` above the rule — the page's first item. A fact of the paged
artifact alone: a continuous medium has no page top. A name no document
command can spell (it carries a hyphen), as `trivlistRole`'s is. -/
public def pageAnchorRole : String := "page-anchor"

/-- The role `\nointerlineskip` rides in, an empty marker: TeX's
`\prevdepth` set to −1000 pt (latex.ltx `\def\nointerlineskip
{\prevdepth-\@m\p@}`), so the next box on the vertical list takes no
interline glue (TeXbook ch. 12). A fact of the paged artifact alone. -/
public def noInterlineRole : String := "no-interline"

/-- A declaration at a page boundary, independent of the page's ground and
vertical distribution. `empty` suppresses running furniture on one shipped
page; a boundary that ships nothing cannot spend that suppression.
Source: article.cls's `titlepage` sets `\thispagestyle{empty}` and page 1
on entry, then page 1 again after the closing `\newpage` in oneside mode. -/
public structure PageOpening where
  folio : Option Nat := none
  empty : Bool := false
  deriving Repr, BEq, Inhabited

/-- The logical folio and running style of the page being built. Physical
page indices and the total page count are separate: resetting the folio
does not remove or renumber an already shipped sheet. -/
public structure PageState where
  folio : Nat := 1
  furniture : Bool := true
  deriving Repr, BEq, Inhabited

/-- Apply only the opening's declarations. A reset does not restore an
empty style that has not yet reached shipout (`ltoutput.dtx`'s special
page-style flag is consumed by `\@outputpage`, not by `\newpage`). -/
public def PageState.applyOpening (s : PageState) (opening : PageOpening) : PageState :=
  { folio := opening.folio.getD s.folio
    furniture := s.furniture && !opening.empty }

/-- Ship one physical page: advance its logical folio and restore the
ordinary running style, as `\@outputpage` does. -/
public def PageState.ship (s : PageState) : PageState :=
  { folio := s.folio + 1, furniture := true }

/-- A page opening changes exactly its declared counter and can only
suppress furniture; an unspent empty style survives a counter-only reset. -/
public theorem PageState.opening_contract (s : PageState) (opening : PageOpening) :
    (s.applyOpening opening).folio = opening.folio.getD s.folio ∧
      (s.applyOpening opening).furniture = (s.furniture && !opening.empty) :=
  ⟨rfl, rfl⟩

/-- Shipment, rather than an empty boundary, advances the folio and
consumes the page-local style. The paged artifact projects this transition. -/
public theorem PageState.ship_contract (s : PageState) :
    s.ship.folio = s.folio + 1 ∧ s.ship.furniture = true := ⟨rfl, rfl⟩

/-- Reserved roles for article titlepage's two boundary declarations. A
space makes either name impossible as an authored control word. -/
public def titlePageBeginRole : String := "titlepage begin"
public def titlePageEndRole : String := "titlepage end"

/-- The one shared reading of titlepage's boundary roles. The end role is
emitted only in oneside mode; twoside keeps the post-titlepage folio. -/
public def pageOpeningOfRole? (n : String) : Option PageOpening :=
  if n == titlePageBeginRole then some { folio := some 1, empty := true }
  else if n == titlePageEndRole then some { folio := some 1 }
  else none

/-- Even an empty titlepage requests an empty first shipped page: its
closing counter reset cannot cancel the opening style. -/
public theorem titlepage_empty_exact (s : PageState) :
    (s.applyOpening { folio := some 1, empty := true }).applyOpening
        { folio := some 1 } = { folio := 1, furniture := false } := by
  simp [PageState.applyOpening]

/-- The engine roles that mark a fact of the page model and carry no
content: HTML, markdown and the structure tree read them as nothing. -/
@[expose] public def pageMarkerRole (n : String) : Bool :=
  n == pageAnchorRole || n == noInterlineRole || (pageOpeningOfRole? n).isSome

/-- Every declared opening is a page-model mark, with no continuous-medium
content of its own. HTML projects this fact instead of interpreting a
titlepage's spelling independently. -/
public theorem pageOpening_marker_exact (n : String) (opening : PageOpening)
    (h : pageOpeningOfRole? n = some opening) : pageMarkerRole n = true := by
  simp [pageMarkerRole, h]

/-- The inline role a description item's label rides in, first in the item's
first paragraph and followed by `\labelsep` (latex.ltx `description`:
`\list{}{\labelwidth\z@ \itemindent-\leftmargin
\let\makelabel\descriptionlabel}`, the label `\normalfont\bfseries`). The
page sets that paragraph with the label run in at the list's outer margin
and every further line at the item's indent; HTML sets the item as a
`<dt>`/`<dd>` pair. A name no document command can spell (it carries a
hyphen), so no authored role collides with it. -/
public def descLabelRole : String := "description-label"

/-- **The quantized trivlist space lies inside every size file's glue.** One
quantum at LaTeX's three standard bodies sits between `\topsep`'s own
minimum and maximum there — 4..10 pt at 10 pt, 4..12 pt at 10.95 pt,
4..14 pt at 12 pt — so the engine's default is a length each class's own
glue could have set. -/
public theorem trivlist_between :
    Dim.pt 4 ≤ (trivlistSkipDefault (Dim.pt 10)).width.sp ∧
      (trivlistSkipDefault (Dim.pt 10)).width.sp ≤ Dim.pt 10 ∧
    Dim.pt 4 ≤ (trivlistSkipDefault (Dim.pt 1095 / 100)).width.sp ∧
      (trivlistSkipDefault (Dim.pt 1095 / 100)).width.sp ≤ Dim.pt 12 ∧
    Dim.pt 4 ≤ (trivlistSkipDefault (Dim.pt 12)).width.sp ∧
      (trivlistSkipDefault (Dim.pt 12)).width.sp ≤ Dim.pt 14 := by
  decide

/-- Where a class's list spacing comes from: the size file of the standard
classes for the body size, beamer's own list family, which a deck and a
poster inherit (beamerposter loads beamer), or the web's, where a list is a
block like a paragraph and its items stand one leading apart — what the
HTML base sheet sets, and what a webpage's print twin follows. -/
public inductive ListLineage where
  | sizeFile
  | beamer
  | web
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One list level's vertical parameters, LaTeX's `\@list⟨n⟩` (ltlists.dtx):
`topsep` above and below the list, taken by `\addvspace` with the
surrounding paragraph's `\parskip` on top (`\@trivlist`, `\@item`,
`\@endparenv`); `itemsep` before every item after the first; and `parsep`,
which is `\parskip` inside the list (`\list` sets `\parskip\parsep`), so two
items stand `itemsep + parsep` apart and two paragraphs of one item
`parsep`. `partopsep` is the level's own `\partopsep` where its
`\@list⟨n⟩` sets it (size10.clo:233, level three), `none` where the value in
force stands (`partopsepFor`). -/
public structure ListSkips where
  topsep : SymGlue
  itemsep : SymGlue
  parsep : SymGlue
  partopsep : Option SymGlue
  deriving Repr, BEq

/-- Glue spelled in hundredths of a point: natural, stretch, shrink. -/
private def ptsGlue (w st sh : Int) : SymGlue :=
  { width := { sp := Dim.pt w / 100 }, stretch := { sp := Dim.pt st / 100 },
    shrink := { sp := Dim.pt sh / 100 } }

/-- The sourced list levels, verbatim: per lineage, size file and level one
to three. A deeper level keeps the third's values, because `\@listiv` and
beyond set margins only, so the values in force stand. -/
private def listSkipsTable : ListLineage → Nat → Nat → ListSkips
  -- size10.clo:216-233
  | .sizeFile, 10, 1 => ⟨ptsGlue 800 200 400, ptsGlue 400 200 100, ptsGlue 400 200 100, none⟩
  | .sizeFile, 10, 2 => ⟨ptsGlue 400 200 100, ptsGlue 200 100 100, ptsGlue 200 100 100, none⟩
  | .sizeFile, 10, _ =>
    ⟨ptsGlue 200 100 100, ptsGlue 200 100 100, {}, some (ptsGlue 100 0 100)⟩
  -- size11.clo:216-233
  | .sizeFile, 11, 1 => ⟨ptsGlue 900 300 500, ptsGlue 450 200 100, ptsGlue 450 200 100, none⟩
  | .sizeFile, 11, 2 => ⟨ptsGlue 450 200 100, ptsGlue 200 100 100, ptsGlue 200 100 100, none⟩
  | .sizeFile, 11, _ =>
    ⟨ptsGlue 200 100 100, ptsGlue 200 100 100, {}, some (ptsGlue 100 0 100)⟩
  -- size12.clo:216-233
  | .sizeFile, _, 1 => ⟨ptsGlue 1000 400 600, ptsGlue 500 250 100, ptsGlue 500 250 100, none⟩
  | .sizeFile, _, 2 => ⟨ptsGlue 500 250 100, ptsGlue 250 100 100, ptsGlue 250 100 100, none⟩
  | .sizeFile, _, _ =>
    ⟨ptsGlue 250 100 100, ptsGlue 250 100 100, {}, some (ptsGlue 100 0 100)⟩
  -- beamerbaselocalstructure.sty:152-163
  | .beamer, _, 1 => ⟨ptsGlue 300 200 250, ptsGlue 300 200 300, {}, none⟩
  | .beamer, _, _ => ⟨ptsGlue 200 100 200, ptsGlue 0 100 0, ptsGlue 0 100 0, none⟩
  -- the web's: no list space of its own (`listSkips` answers `none`)
  | .web, _, _ => ⟨{}, {}, {}, none⟩

/-- The size file a body size reads: the standard classes' `10pt`, `11pt`
and `12pt` options, and the nearest of them for any other size. -/
private def sizeFileOf (size : Sp) : Nat :=
  if size < Dim.pt 21 / 2 then 10 else if size < Dim.pt 23 / 2 then 11 else 12

/-- **The one resolving site for a list level's spacing**: the lineage's
sourced values at the body size and nesting level, `none` for the web's,
where a list opens only the peer gap a paragraph would. At 10, 11 and
12 pt they are the size file's own. A body size no size file sets scales
its nearest file's values with the type; LaTeX has no value there, and the
engine's other defaults follow the type the same way. beamer's values do
not depend on the size, as its `\@listi` does not. -/
public def listSkips (l : ListLineage) (size : Sp) (level : Nat) : Option ListSkips :=
  let lv := min (max level 1) 3
  match l with
  | .web => none
  | .beamer => some (listSkipsTable .beamer 0 lv)
  | .sizeFile =>
    let f := sizeFileOf size
    let s := listSkipsTable .sizeFile f lv
    let base := Dim.pt f
    if size == base then some s
    else some { topsep := s.topsep.scale size base.toNat
                itemsep := s.itemsep.scale size base.toNat
                parsep := s.parsep.scale size base.toNat
                partopsep := s.partopsep.map (·.scale size base.toNat) }

/-- The web's lineage sets no list skips, at any size or level. -/
public theorem listSkips_web_exact (size : Sp) (level : Nat) :
    listSkips .web size level = none := by
  simp only [listSkips]

/-- The class's `\partopsep`, the value in force where no list level sets
its own: size10.clo:215 `2pt plus 1pt minus 1pt`, size11.clo:215
`3pt plus 1pt minus 1pt`, size12.clo:215 `3pt plus 2pt minus 2pt`, scaled
with the type off the three bodies as `listSkips` scales; beamer's is zero
(beamerbaselocalstructure.sty:164), and the web's lists open none. -/
public def partopsepDefault (l : ListLineage) (size : Sp) : SymGlue :=
  match l with
  | .sizeFile =>
    let f := sizeFileOf size
    let g := match f with
      | 10 => ptsGlue 200 100 100
      | 11 => ptsGlue 300 100 100
      | _ => ptsGlue 300 200 200
    if size == Dim.pt f then g else g.scale size (Dim.pt f).toNat
  | .beamer | .web => {}

/-- **The one resolving site for a list's `\partopsep`**, the space
`\@trivlist` adds to `\topsep` where the list opens in vertical mode: the
level's own where its `\@list⟨n⟩` sets it — size10/11/12.clo:233, so a
level-three list takes 1pt whatever the document declared — else a
declared `\partopsep` (`\setlength`, `\tokens`), else the class's
(`partopsepDefault`). -/
public def partopsepFor (l : ListLineage) (size : Sp) (level : Nat) (tokens : Tokens) : SymGlue :=
  match (listSkips l size level).bind (·.partopsep) with
  | some g => g
  | none => (tokens.find? "partopsep").getD (partopsepDefault l size)

/-- The four glues a size file's `\normalsize` sets around display math:
`\abovedisplayskip` and `\belowdisplayskip`, and the short pair TeX takes
instead when the line before the display ends left of the formula
(TeXbook ch. 19; tex.web §1203). -/
public structure DisplaySkips where
  above : SymGlue
  below : SymGlue
  aboveShort : SymGlue
  belowShort : SymGlue
  deriving Repr, BEq

/-- The size files' display skips, verbatim, keyed by the class option's
point size: size10.clo:49-52, size11.clo:49-52 and size12.clo:49-52 for
the standard classes (KOMA's scrsize1Xpt.clo and memoir's mem1X.clo set the
same rows), and extsizes' size8, size9, size14, size17 and size20.clo:13-16
for beamer's other options (beamer.cls:155-166 inputs those files). Every
file sets `\belowdisplayskip \abovedisplayskip`. -/
private def displaySkipsTable : Nat → DisplaySkips
  | 8 | 9 => ⟨ptsGlue 800 400 400, ptsGlue 800 400 400, ptsGlue 0 300 0, ptsGlue 500 300 300⟩
  | 10 => ⟨ptsGlue 1000 200 500, ptsGlue 1000 200 500, ptsGlue 0 300 0, ptsGlue 600 300 300⟩
  | 11 => ⟨ptsGlue 1100 300 600, ptsGlue 1100 300 600, ptsGlue 0 300 0, ptsGlue 650 350 300⟩
  | 12 => ⟨ptsGlue 1200 300 700, ptsGlue 1200 300 700, ptsGlue 0 300 0, ptsGlue 650 350 300⟩
  | 14 => ⟨ptsGlue 1400 300 700, ptsGlue 1400 300 700, ptsGlue 0 400 0, ptsGlue 700 400 300⟩
  | 17 => ⟨ptsGlue 1500 400 800, ptsGlue 1500 400 800, ptsGlue 0 400 0, ptsGlue 800 400 300⟩
  | _ => ⟨ptsGlue 1700 500 800, ptsGlue 1700 500 800, ptsGlue 0 500 0, ptsGlue 1000 500 400⟩

/-- The class options a display's size file is read from, each with the
`\normalsize` its file sets (`\@xipt` is 10.95 pt, `\@xivpt` 14.4 pt,
`\@xviipt` 17.28 pt, `\@xxpt` 20.74 pt: ltplain's values). -/
private def displayOptions : List (Nat × Sp) :=
  [(8, Dim.pt 8), (9, Dim.pt 9), (10, Dim.pt 10), (11, Dim.pt 1095 / 100), (12, Dim.pt 12),
   (14, Dim.pt 144 / 10), (17, Dim.pt 1728 / 100), (20, Dim.pt 2074 / 100)]

/-- The `\normalsize` a class option's size file sets, for a body declared
at that option's point size: `11pt` sets 10.95 pt (size11.clo's `\@xipt`),
`14pt` 14.4 pt; a size that is no option's point size is its own. What a
package measures in the preamble is measured at this size
(`PreambleFace.ofClass`): booktabs under `11pt` fixes `\heavyrulewidth` at
0.876 pt, .08 of 10.95 pt (lualatex). -/
public def optionNormalSize (size : Sp) : Sp :=
  ((displayOptions.find? fun o => Dim.pt o.1 == size).map (·.2)).getD size

/-- The option whose point size stands nearest a body size. -/
private def displaySizeFileOf (size : Sp) : Nat :=
  (displayOptions.foldl (fun (best : Nat × Sp) (o : Nat × Sp) =>
    if (size - Dim.pt o.1).natAbs < (size - Dim.pt best.1).natAbs then (o.1, o.2) else best)
    (10, Dim.pt 10)).1

/-- The display skips at a body size: the size file's own where the body is
the option's point size or the `\normalsize` its file sets; otherwise the
nearest file's, scaled with the type, as `listSkips` scales — LaTeX has no
value there. -/
public def displaySkipsAt (size : Sp) : DisplaySkips :=
  let f := displaySizeFileOf size
  let s := displaySkipsTable f
  let body := ((displayOptions.lookup f).getD (Dim.pt f))
  if size == Dim.pt f || size == body then s
  else
    let base := (Dim.pt f).toNat
    ⟨s.above.scale size base, s.below.scale size base, s.aboveShort.scale size base,
     s.belowShort.scale size base⟩

/-- `\abovedisplayskip` at a body size, the long skip. -/
public def displaySkipDefault (size : Sp) : SymGlue := (displaySkipsAt size).above

/-- `\abovedisplayskip` at the base size: size10.clo's 10 pt. -/
public theorem displaySkipDefault_base_exact :
    (displaySkipDefault baseFontSize).width.sp = Dim.pt 10 := by
  decide

/-- The four display-skip token names, as `\tokens` and `\setlength` spell
them. -/
public def displaySkipAbove : String := "abovedisplayskip"
public def displaySkipBelow : String := "belowdisplayskip"
public def displaySkipAboveShort : String := "abovedisplayshortskip"
public def displaySkipBelowShort : String := "belowdisplayshortskip"

/-- **The one resolving site for the display skips**: each of the four the
document's token where declared, else the size file's at the governing
size. Both backends read it (`Layout`'s display arm; the HTML base sheet
emits the long pair's tokens with these defaults as their `var()`
fallbacks). -/
public def displaySkipsFor (tokens : Tokens) (size : Sp) : DisplaySkips :=
  let d := displaySkipsAt size
  { above := (tokens.find? displaySkipAbove).getD d.above
    below := (tokens.find? displaySkipBelow).getD d.below
    aboveShort := (tokens.find? displaySkipAboveShort).getD d.aboveShort
    belowShort := (tokens.find? displaySkipBelowShort).getD d.belowShort }

/-- The long skip above a display; see `displaySkipsFor`. -/
public def displayAbove (tokens : Tokens) (size : Sp) : SymGlue := (displaySkipsFor tokens size).above

/-- The long skip below a display; see `displaySkipsFor`. -/
public def displayBelow (tokens : Tokens) (size : Sp) : SymGlue := (displaySkipsFor tokens size).below

/-- **The display skips are the size file's** (`_exact`): an undeclared
document at the standard classes' three bodies reads size10/11/12.clo's
rows whole, the short pair included — the token layer adds nothing. -/
private theorem displaySkips_default_exact :
    displaySkipsFor {} (Dim.pt 10) = displaySkipsTable 10 ∧
    displaySkipsFor {} (Dim.pt 11) = displaySkipsTable 11 ∧
    displaySkipsFor {} (Dim.pt 12) = displaySkipsTable 12 := ⟨rfl, rfl, rfl⟩

/-- Where a display stands in its paragraph: the facts TeX's display
placement reads (tex.web §1145-1146, §1199-1206) that the block's shape
does not carry, recorded by elaboration from the source. `inPar`: text of
the same paragraph precedes it, so `\predisplaysize` is measured on that
paragraph's last line; otherwise amsmath's `$$` opens the paragraph and TeX
sets an empty line first. `parEnd`: a paragraph break follows, so the next
paragraph opens with its own separation; otherwise the text after the
display continues the paragraph. `align`: a display alignment (`align`,
`gather`), which §1206 always spaces with the long skips and whose rows
amsmath sets on its strut. `afterEnv`: in vertical mode the display opens
right after a list/quote/theorem end, whose `\endtrivlist` leaves `\@endpe`
set so the opening `\everypar` takes the indent box back (ltlists.dtx:
`\@doendpe`) — TeX sets no empty line, exactly as after a heading
(`\@afterheading`). This is the fact the walk read wrongly from its owed
glue, which a `\vspace` fills too; elaboration knows the preceding
environment and a space does not. The default is the common case, a display
inside a paragraph that runs on after it. -/
public structure DisplayCtx where
  inPar : Bool := true
  parEnd : Bool := false
  align : Bool := false
  afterEnv : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The role a display's context rides in: a name no document command can
spell (it carries a hyphen, as `inParagraphRole` does). -/
public def DisplayCtx.role (c : DisplayCtx) : String :=
  "display-" ++ (if c.inPar then "p" else "v") ++ (if c.parEnd then "e" else "c") ++
    (if c.align then "a" else "f") ++ (if c.afterEnv then "n" else "o")

/-- Every display context, for reading a role back. -/
public def DisplayCtx.all : List DisplayCtx :=
  [false, true].flatMap fun p => [false, true].flatMap fun e => [false, true].flatMap fun a =>
    [false, true].map fun v => { inPar := p, parEnd := e, align := a, afterEnv := v }

/-- The context a role names, if it is a display's. -/
public def DisplayCtx.ofRole? (n : String) : Option DisplayCtx :=
  DisplayCtx.all.find? (·.role == n)

/-- A display's role reads back as its context (`_exact`). -/
public theorem DisplayCtx.ofRole?_role_exact (c : DisplayCtx) : DisplayCtx.ofRole? c.role = some c := by
  cases c with
  | mk p e a v => cases p <;> cases e <;> cases a <;> cases v <;> decide

/-- A list opening a paragraph adds the class's `\partopsep` at the top
level and its level-three reset below: 2, 3 and 3 pt at the three standard
bodies (size10/11/12.clo:215), 1pt at level three (:233) whatever the
document declared, and beamer's zero. -/
public theorem partopsep_exact :
    (partopsepFor .sizeFile (Dim.pt 10) 1 {}).width.sp = Dim.pt 2 ∧
    (partopsepFor .sizeFile (Dim.pt 11) 1 {}).width.sp = Dim.pt 3 ∧
    (partopsepFor .sizeFile (Dim.pt 12) 1 {}).width.sp = Dim.pt 3 ∧
    (partopsepFor .sizeFile (Dim.pt 10) 3 {}).width.sp = Dim.pt 1 ∧
    (partopsepFor .beamer (Dim.pt 11) 1 {}).width.sp = 0 := by
  decide

/-- At the three standard body sizes a list's spacing is the size file's,
exactly: `\topsep` 8, 9, 10 pt and `\itemsep + \parsep` 8, 9, 10 pt at the
top level (size10/11/12.clo:216-219), and beamer's `\topsep` and
`\itemsep` are 3 pt with a zero `\parsep` (beamerbaselocalstructure
.sty:152-155). -/
public theorem listSkips_exact :
    ((listSkips .sizeFile (Dim.pt 10) 1).map fun s =>
      (s.topsep.width.sp, s.itemsep.width.sp + s.parsep.width.sp)) = some (Dim.pt 8, Dim.pt 8) ∧
    ((listSkips .sizeFile (Dim.pt 11) 1).map fun s =>
      (s.topsep.width.sp, s.itemsep.width.sp + s.parsep.width.sp)) = some (Dim.pt 9, Dim.pt 9) ∧
    ((listSkips .sizeFile (Dim.pt 12) 1).map fun s =>
      (s.topsep.width.sp, s.itemsep.width.sp + s.parsep.width.sp)) = some (Dim.pt 10, Dim.pt 10) ∧
    ((listSkips .beamer (Dim.pt 11) 1).map fun s =>
      (s.topsep.width.sp, s.itemsep.width.sp, s.parsep.width.sp)) = some (Dim.pt 3, Dim.pt 3, 0) := by
  decide

/-- How a theorem-like block spends its space (`thmSkips`): the trivlist
its spelling opens, and the lengths it sets before its `\item`. -/
public inductive ThmSpace where
  /-- latex.ltx `\@begintheorem` is `\trivlist` itself: `\topsep`, with
  `\partopsep` where it opens in vertical mode, and TeX's `\parskip` on
  top, above and below. -/
  | kernel
  /-- amsthm.sty `\@thm` under plain and definition: `\@topsep` is
  `\thm@preskip` and `\@topsepadd` is `\thm@postskip`, both `\topsep`
  (`\thm@space@setup`), so no `\partopsep`; and above no `\parskip`, which
  `\deferred@thm@head`'s `\addvspace{-\parskip}` takes back. -/
  | ams
  /-- amsthm's remark style: `\th@remark` halves both
  (`\divide\thm@preskip\tw@`). -/
  | amsHalf
  /-- amsthm's `proof`: `\topsep6\p@\@plus6\p@` over `\partopsep`,
  always, since its `\par` puts the `\trivlist` in vertical mode. -/
  | proof
  deriving Repr, BEq, DecidableEq, Inhabited

public def ThmSpace.all : List ThmSpace := [.kernel, .ams, .amsHalf, .proof]

/-- The engine role a theorem-like block rides in, one per `ThmSpace`: a
trivlist whose space is its spelling's. A name no document command can
spell (it carries a hyphen), as `trivlistRole`'s is. -/
public def thmSpaceRole : ThmSpace → String
  | .kernel => "trivlist-kernel"
  | .ams => "trivlist-ams"
  | .amsHalf => "trivlist-remark"
  | .proof => "trivlist-proof"

/-- The space a theorem role names. -/
public def thmSpaceOf? (n : String) : Option ThmSpace :=
  ThmSpace.all.find? (thmSpaceRole · == n)

/-- A theorem-like block's space above its head and below its last line,
and whether TeX's `\parskip` stands on top of the space above. -/
public structure ThmSkips where
  above : SymGlue
  below : SymGlue
  parskipAbove : Bool
  deriving Repr, BEq

/-- amsthm's proof: `\topsep6\p@\@plus6\p@` (amsthm.sty:433), whatever the
body size. -/
public def proofTopsep : SymGlue := { width := { sp := Dim.pt 6 }, stretch := { sp := Dim.pt 6 } }

/-- **The one resolving site for a theorem-like block's space**, read by
both backends: the `\topsep` in force where it stands — `\@listi`'s at top
level, which `\normalsize` sets, else the enclosing list level's
(`listSkips`) — spent as its spelling spends it (`ThmSpace`), `\partopsep`
through `partopsepFor`. `vertical` says whether the block opens in vertical
mode, which only the kernel's reads. `none` for the web's lineage, whose
theorems are the trivlist block (`trivlistSkip`). -/
public def thmSkips (l : ListLineage) (size : Sp) (level : Nat) (tokens : Tokens)
    (k : ThmSpace) (vertical : Bool) : Option ThmSkips :=
  (listSkips l size level).map fun sk =>
    let pts := partopsepFor l size level tokens
    match k with
    | .kernel =>
      let g := if vertical then sk.topsep.add pts else sk.topsep
      ⟨g, g, true⟩
    | .ams => ⟨sk.topsep, sk.topsep, false⟩
    | .amsHalf =>
      let g := sk.topsep.scale 1 2
      ⟨g, g, false⟩
    | .proof =>
      let g := proofTopsep.add pts
      ⟨g, g, true⟩

/-- **A theorem-like block's space is LaTeX's** at the three standard bodies
(`_exact`): the kernel's `\topsep` over `\partopsep` after a blank line —
10, 12, 13 pt — and `\topsep` alone in a paragraph; amsthm's `\topsep`
above and below plain and definition, no `\parskip` above, half of it for
remark; the proof's 6 pt over `\partopsep`, 8, 9, 9 pt (size10/11/12.clo:
215–218, amsthm.sty:74–76, 229–233, 433); none on the web's lineage. -/
public theorem thmSkips_exact :
    ((thmSkips .sizeFile (Dim.pt 10) 1 {} .kernel true).map (·.above.width.sp)) = some (Dim.pt 10) ∧
    ((thmSkips .sizeFile (Dim.pt 11) 1 {} .kernel true).map (·.above.width.sp)) = some (Dim.pt 12) ∧
    ((thmSkips .sizeFile (Dim.pt 12) 1 {} .kernel true).map (·.above.width.sp)) = some (Dim.pt 13) ∧
    ((thmSkips .sizeFile (Dim.pt 10) 1 {} .kernel false).map (·.below.width.sp)) = some (Dim.pt 8) ∧
    ((thmSkips .sizeFile (Dim.pt 10) 1 {} .ams true).map fun s =>
      (s.above.width.sp, s.below.width.sp, s.parskipAbove)) = some (Dim.pt 8, Dim.pt 8, false) ∧
    ((thmSkips .sizeFile (Dim.pt 12) 1 {} .ams true).map (·.above.width.sp)) = some (Dim.pt 10) ∧
    ((thmSkips .sizeFile (Dim.pt 10) 1 {} .amsHalf true).map (·.above.width.sp)) = some (Dim.pt 4) ∧
    ((thmSkips .sizeFile (Dim.pt 11) 1 {} .amsHalf true).map (·.above.width.sp)) =
      some (Dim.pt 9 / 2) ∧
    ((thmSkips .sizeFile (Dim.pt 10) 1 {} .proof false).map (·.above.width.sp)) = some (Dim.pt 8) ∧
    ((thmSkips .sizeFile (Dim.pt 11) 1 {} .proof false).map (·.below.width.sp)) = some (Dim.pt 9) ∧
    ((thmSkips .sizeFile (Dim.pt 12) 1 {} .proof false).map (·.above.width.sp)) = some (Dim.pt 9) ∧
    thmSkips .web (Dim.pt 10) 1 {} .ams true = none := by
  decide

/-- A list level's `\leftmargin⟨n⟩` in thousandths of an em of the class
base: the standard classes' one-column stack, 2.5, 2.2, 1.87, 1.7, 1 and
1 em (classes.dtx; article.cls:323-336, and scrartcl.cls:6752-6758 sets
the same), and beamer's 2 em at its three levels
(beamerbaselocalstructure.sty:144-146; beamer defines no fourth, so a
deeper level keeps the third's). The web's lineage declares none: its
lists hang the engine's own indent (`Layout.Geom.listIndent`). The em is
the body size: lualatex's first level stands 25, 27.37 and 30 pt in at the
10, 11 and 12 pt options. A two-column page's 2 em first level is not
modelled. -/
public def leftMarginMilli : ListLineage → Nat → Option Nat
  | .sizeFile, 1 => some 2500
  | .sizeFile, 2 => some 2200
  | .sizeFile, 3 => some 1870
  | .sizeFile, 4 => some 1700
  | .sizeFile, _ => some 1000
  | .beamer, _ => some 2000
  | .web, _ => none

/-- **The one resolving site for a list level's `\leftmargin`**: the
lineage's stack at the body size and nesting level — `\@listdepth`, over
every list and quotation — where the lineage declares one. Both artifacts
read it: the page's list, quotation and description margins, and the
sheet's padding (`HtmlDoc.listIndentCss`), in the em it is spelled in. A
document's own `\leftmargin⟨n⟩` rides in the token of that name
(`leftMarginName`), which both read first, as every `\list` of that level
reads the length in LaTeX. -/
public def leftMargin (l : ListLineage) (size : Sp) (level : Nat) : Option Sp :=
  (leftMarginMilli l (max level 1)).map fun m => size * (m : Int) / 1000

/-- The length a document declares a level's margin in: `\leftmargini`
to `\leftmarginvi`, the kernel's six (latex.ltx `\@listdepth` reads at
most six), a deeper level reading the sixth. -/
public def leftMarginName (level : Nat) : String :=
  "leftmargin" ++ (match min (max level 1) 6 with
    | 1 => "i" | 2 => "ii" | 3 => "iii" | 4 => "iv" | 5 => "v" | _ => "vi")

/-- At the 10 pt base a list level's margin is the class's own, exactly:
25, 22, 18.7 and 17 pt at the standard classes' four levels, and beamer's
20 pt at each of its three. -/
public theorem leftMargin_exact :
    leftMargin .sizeFile (Dim.pt 10) 1 = some (Dim.pt 25) ∧
    leftMargin .sizeFile (Dim.pt 10) 2 = some (Dim.pt 22) ∧
    leftMargin .sizeFile (Dim.pt 10) 3 = some (Dim.pt 187 / 10) ∧
    leftMargin .sizeFile (Dim.pt 10) 4 = some (Dim.pt 17) ∧
    leftMargin .beamer (Dim.pt 10) 3 = some (Dim.pt 20) ∧
    leftMargin .web (Dim.pt 10) 1 = none := by
  decide

/-- The heading's default spaces, their own tokens rather than the
parskip's doubles: article.cls pairs a zero `\parskip` with 3.5ex above /
2.3ex below a `\section` (classes.dtx `\@startsection`), so a class that
zeroes the peer gap must not silently zero the heading's. The
rhythm-aligned stand-ins are one full unit above and the half-unit below
(the heading and peer rows of `rhythmGapQuanta`), the same ordering. A
document with a larger declared parskip keeps the walk's 2-quanta growth
(the walk takes the larger); a declared `\style{section}{ before/after }`
overrides entirely. -/
public def headingBeforeDefault (size : Sp) : SymGlue :=
  { width := { sp := 2 * rhythmQuantum size } }
/-- The heading's default space below: the half-unit. See
`headingBeforeDefault`. -/
public def headingAfterDefault (size : Sp) : SymGlue :=
  { width := { sp := rhythmQuantum size } }

/-- A heading binds to the text it introduces: its default space above is
at least its space below (Hochuli, Detail in Typography, on section
openings: more space above the heading than below it; article.cls's
3.5ex/2.3ex is the same ordering at 1.52), both on the rhythm, and neither
zero. That the space above is exactly twice the quantum is
`rhythm_table_exact`'s heading row, stated once there. W0202 is the
declared-values half of the same rule; this is the defaults' half, and an
edit that inverts them fails the build here. -/
public theorem heading_space_above_ge_below (size : Int) (h : Dim.pt 1 ≤ size) :
    (headingAfterDefault size).width.sp ≤ (headingBeforeDefault size).width.sp ∧
    (headingAfterDefault size).width.sp = rhythmQuantum size ∧
    0 < (headingAfterDefault size).width.sp :=
  ⟨Int.le_of_lt (rhythmQuantum_lt_double size h), rfl, rhythmQuantum_pos size h⟩

/-- The default vertical rhythm is one system, not three numbers: the peer
gap (`parskipDefault`, 6pt at the 10pt base) is the rhythm quantum — half
the base leading — so the heading's default space above, `2 × parskip` in
the block walk, is exactly one full rhythm unit, and every default gap is a
multiple of the half-unit (Bringhurst §2.2.2: add vertical space in
measured intervals, multiples of the basic leading). The positivity
conjunct is what makes a heading's space above strictly exceed its space
below. Stated here, over the declared tokens, because both backends
realize these gaps: the PDF's placement and the HTML base stylesheet each
owe the theorem that what they ship equals what this layer declares. -/
public theorem default_rhythm_multiples (size : Int) (h : Dim.pt 1 ≤ size) :
    (parskipDefault size).width.sp = rhythmQuantum size ∧
    0 < (parskipDefault size).width.sp :=
  ⟨rfl, rhythmQuantum_pos size h⟩

/-- The anchor, `rfl` by derivation at every base: the peer gap IS the
rhythm quantum, because it is defined as it — no absolute constant
survives in the default, which is the soundness of mapping a poster's
`scale=` onto `\page{ fontsize }`. -/
public theorem parskip_is_quantum (size : Sp) :
    (parskipDefault size).width.sp = rhythmQuantum size := by rfl

/-- At the shipped article base the leading is even, so the half-unit
halves it exactly. The slides 11pt leading is odd in sp (865075), so its
quantum rounds down half an sp — invisible ink, stated rather than
implied; the exactness is per-base, the derivation universal
(`parskip_is_quantum`). -/
public theorem parskip_halves_leading_at_bases :
    2 * (parskipDefault baseFontSize).width.sp = leadingFor baseFontSize := by
  decide

/-- Caption and float gaps sit on the same rhythm: the caption gap — the
object-side gap, the sourcing note above `captionSepDefault` — is the
half-unit (one `parskip`), the float gap — both text-side gaps — the full
unit (two, which is also exactly LaTeX's `\intextsep` 12pt, classes.dtx
10pt option), and the caption binds tighter to its object than the float
to its page — the ordering LaTeX's own `\abovecaptionskip` 10pt <
`\intextsep` 12pt states (classes.dtx). Which physical side each value
lands on is `Layout.floatPlan`'s statement; this one holds the values. A
default edit that breaks the quantization or the ordering fails the
build; this is the user-visible "spacing around tables and figures"
contract, stated over the values the engine ships. -/
public theorem caption_gaps_rhythm (size : Int) (h : Dim.pt 1 ≤ size) :
    (captionSepDefault size).width.sp = rhythmQuantum size ∧
    (floatSepDefault size).width.sp = 2 * rhythmQuantum size ∧
    (captionSepDefault size).width.sp < (floatSepDefault size).width.sp :=
  ⟨rfl, rfl, rhythmQuantum_lt_double size h⟩

/-- The title block's author strut: two rhythm units of line box for the
author's name. The NeurIPS-lineage `.sty` sets `\rule{\z@}{24\p@}` in the
author `tabular` — and 24pt at the 10pt body *is* exactly 2u, a rhythm
multiple already, so the engine's value coincides with the venue's there.
Spelled in em so it re-derives from the body size, as the rhythm does —
but em-resolution floors, so the general equality with quantum multiples
is FALSE off the shipped bases: at size = 65538 sp the em-resolved value
and `4 * rhythmQuantum` differ (by ≤ 3 sp, whenever `size·1200/1000` is
odd). The exactness theorems below stay per-base `decide` for that
reason; the derivation is universal, the equality is not. -/
public def titleAuthorStrut : SymGlue := { width := { em := 2 * leadingMilli } }

/-- The gap after the whole title block, before the abstract or the text:
two rhythm units, shrinkable by the half-unit — a little rubber, as the
lineage's `\vskip 0.3in \@minus 0.1in` has. The venue's 21.7pt (shrunk
floor 14.5pt) becomes the engine's 24pt (floor 18pt) at the 10pt body:
the grid lands 2.3pt over what the venue eyeballed. -/
public def titleBlockAfter : SymGlue :=
  { width := { em := 2 * leadingMilli }, shrink := { em := leadingMilli / 2 } }

/-- The gap between a title bar and the type it cuts: three rhythm quanta
(1½ leadings), the same on both sides. Under the placement convention
(`Layout.interlineFor`) the gap runs to the type's *body* — the cap line
above the text, the baseline below it — so equal declared gaps are equal
visible gaps by definition (Hochuli, *Detail in Typography*, "Rules": a
rule relates to the type it cuts; Bringhurst §2.2.2 for the unit). The
venue contributes only the bars' weights; a document declares its own
asymmetry through `\style{titlepage}{ rule-above-gap = … }`. Spelled in
em, with `titleAuthorStrut`'s rounding caveat: exactness is per-base. -/
public def titleBarGap : SymGlue := { width := { em := 3 * leadingMilli / 2 } }

/-- LaTeX's `\strutbox` height at a size: 0.7 of its baselineskip
(ltfssbas.dtx, `\set@fontsize`: `\vrule\@height.7\baselineskip
\@depth.3\baselineskip`). What moloch's frametitle box is built from: the
box opens with a strut of `\ht\strutbox` in the frametitle font and pads
it by the same amount above and below (beamerouterthememoloch.dtx,
`\moloch@frametitlestrut@start`/`@end`,
`\moloch@frametitle@margin@top`/`@bottom`). -/
public def frameTitleStrut (titleSize : Sp) : Sp := leadingFor titleSize * 7 / 10

/-- The frametitle padding moloch's outer theme declares, as the token the
bundle installs: `\moloch@frametitle@margin@top = \moloch@frametitle@margin@bottom
= \ht\strutbox` measured after `\usebeamerfont{frametitle}` — so the
length is em of the *title's* size (0.7 of its leading), and the layout
resolves it there (`Layout` reads `frametitlepadding` at the title size),
not at the body's. A bundle declaring the token gets moloch's box; a bar
declared with no token keeps the engine's generic half-body pad. -/
public def frameTitlePadding : SymGlue := { width := { em := 7 * leadingMilli / 10 } }


/-- The skip outside a title bar — above the top one, below the bottom
one: one rhythm quantum. -/
public def titleBarSkip : SymGlue := { width := { em := leadingMilli / 2 } }

/-- The author block joins the rhythm (`default_rhythm_multiples`' family):
the strut and the post-block gap are half-unit multiples of the body
leading — four quanta each, the gap's shrink one — so the title block
stays the engine's typography while the venue chooses only that the
furniture exists (and the author's weight). Per-base `decide`, and it must
stay so: em-resolution floors, so this equality is false at general sizes
(65538 sp is a counterexample; `titleAuthorStrut`'s caveat). -/
public theorem title_author_rhythm :
    titleAuthorStrut.width.resolve baseFontSize 0 = 4 * rhythmQuantum baseFontSize ∧
    titleBlockAfter.width.resolve baseFontSize 0 = 4 * rhythmQuantum baseFontSize ∧
    titleBlockAfter.shrink.resolve baseFontSize 0 = rhythmQuantum baseFontSize := by
  decide

/-- The title bars join the rhythm too (`default_rhythm_multiples`'
family): the gap either side of a bar is three quanta, the skip outside
it one — every default around the title block is a half-unit multiple,
and an edit that moves a token off its multiple fails the build here.
Per-base `decide`, as `title_author_rhythm`: the general equality is
false off-base (em-resolution floors). -/
public theorem title_bar_rhythm :
    titleBarGap.width.resolve baseFontSize 0 = 3 * rhythmQuantum baseFontSize ∧
    titleBarSkip.width.resolve baseFontSize 0 = rhythmQuantum baseFontSize := by
  decide

/-- The declared rhythm multiples, one table both backends realize from: at
each kind of default block boundary, how many quanta the gap is. The PDF's
tokens are held to it (`rhythm_table_exact`; the heading row is the block
walk's `2 × parskip`), and the HTML base stylesheet computes its margins
from it — a backend that re-spelled a multiple would be a backend no
theorem covers. The quantum differs per context (the print leading against
the screen leading), which is exactly the statement: a boundary's multiple
is declared once; each backend realizes it in its own context's unit.
A display is not a row: its space is TeX's, measured from the baselines
(`displaySkipsFor` and the page's interline rule), never a multiple. -/
@[expose] public def rhythmGapQuanta : List (String × Nat) :=
  [("peer", 1), ("heading", 2), ("caption", 1), ("float", 2), ("trivlist", 2)]

/-- The table and the tokens agree: each declared default gap is its row's
multiple of the quantum, and the heading row is twice the peer row — the
walk's `parskip.add parskip` spelled as a multiple. The trivlist row is the
boundary's whole gap: the peer gap *and* the environment's own space on top
of it, because TeX contributes `\parskip` when the following paragraph
starts, after the trivlist's `\addvspace` already stands. An edit that
moves a token off its declared multiple, or drops a row a backend reads,
fails the build here. -/
public theorem rhythm_table_exact (size : Sp) :
    ((rhythmGapQuanta.lookup "peer").getD 0 : Int) * rhythmQuantum size
      = (parskipDefault size).width.sp ∧
    ((rhythmGapQuanta.lookup "caption").getD 0 : Int) * rhythmQuantum size
      = (captionSepDefault size).width.sp ∧
    ((rhythmGapQuanta.lookup "float").getD 0 : Int) * rhythmQuantum size
      = (floatSepDefault size).width.sp ∧
    ((rhythmGapQuanta.lookup "heading").getD 0 : Int) * rhythmQuantum size
      = (headingBeforeDefault size).width.sp ∧
    ((rhythmGapQuanta.lookup "trivlist").getD 0 : Int) * rhythmQuantum size
      = (parskipDefault size).width.sp + (trivlistSkipDefault size).width.sp ∧
    (rhythmGapQuanta.lookup "heading").getD 0
      = 2 * (rhythmGapQuanta.lookup "peer").getD 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide⟩ <;>
    simp [rhythmGapQuanta, parskipDefault, captionSepDefault, floatSepDefault,
      headingBeforeDefault, trivlistSkipDefault, Dim.Length.ofSp,
      List.lookup] <;> omega

/-- A role realized on a ground other than its palette's page: the role, the
colour it was declared as there, the ground, and the ink the contrast
contract chose (`Contrast.realizeDoc`). -/
public structure GroundInk where
  role : String
  declared : Color
  ground : Color
  ink : Color
  deriving Repr, BEq, Inhabited

/-- The key a role's realization on one ground is named by — the role, the
colour it was declared as, the ground — as the `subject` of its N0022 note,
so "every realization is reported" is a lookup. -/
public def inkKey (role : String) (declared ground : Color) : String :=
  let hex (c : Color) := s!"#{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}"
  s!"{role}:{hex declared}@{hex ground}"

/-- Named colours declared by `\palette`. -/
public structure Palette where
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
  /-- The realized inks of the roles used under this palette on grounds
  that are not its page, written by the realization pass and read by
  both backends through `Design.inks`. Empty until realization. -/
  inks : Array GroundInk := #[]
  deriving Repr, BEq, Inhabited

public def Palette.find? (p : Palette) (name : String) : Option Color :=
  (p.entries.find? (·.1 == name)).map (·.2)

/-- Replace-on-redeclare: a later declaration overrides, keeping one entry
per name. The one install mechanism — a document's `\palette` and a theme's
bundle go through the same door. -/
@[expose] public def Palette.declare (p : Palette) (key : String) (c : Color)
    (decorative : Bool := false) : Palette :=
  { p with
    entries := (p.entries.filter (·.1 != key)).push (key, c)
    decorative := if decorative then
        if p.decorative.contains key then p.decorative
        else p.decorative.push key
      else p.decorative.filter (· != key) }

/-- Remove one palette key while leaving every unrelated declaration in its
current epoch. Used by a page-ground reset when the opening document palette
had no explicit ground. -/
public def Palette.erase (p : Palette) (key : String) : Palette :=
  { p with entries := p.entries.filter (·.1 != key)
           decorative := p.decorative.filter (· != key) }

/-- Restore one key from an opening palette: its original value and
classification when present, absence when the opening palette inherited the
class default. -/
public def Palette.restore (p opening : Palette) (key : String) : Palette :=
  match opening.find? key with
  | some c => p.declare key c (opening.decorative.contains key)
  | none => p.erase key

/-- Erasing a key makes that key absent, not a guessed replacement colour. -/
public theorem Palette.erase_exact (p : Palette) (key : String) :
    (p.erase key).find? key = none := by
  simp only [Palette.erase, Palette.find?]
  have hnone : (p.entries.filter (·.1 != key)).find? (·.1 == key) = none := by
    rw [Array.find?_eq_none]
    intro x hx
    have hne := (Array.mem_filter.mp hx).2
    simpa using hne
  simp [hnone]

/-- Erasing one key preserves every other palette lookup. -/
public theorem Palette.erase_keeps_others (p : Palette) (key other : String)
    (h : other ≠ key) : (p.erase key).find? other = p.find? other := by
  unfold Palette.erase Palette.find?
  rw [Array.find?_filter]
  have hpred :
      (fun a : String × Color => decide ((a.fst != key) = true ∧ (a.fst == other) = true))
        = (fun a : String × Color => a.fst == other) := by
    funext x
    by_cases hx : (x.1 == other) = true
    · have hxe : x.1 = other := by simpa using hx
      simp [hxe, h]
    · simp [hx]
  rw [hpred]

/-- A reset reads exactly as the opening palette read, whether that means a
concrete document colour or the class's undeclared default. -/
public theorem Palette.restore_exact (p opening : Palette) (key : String) :
    (p.restore opening key).find? key = opening.find? key := by
  cases h : opening.find? key with
  | none => simpa [Palette.restore, h] using Palette.erase_exact p key
  | some c =>
    simp only [Palette.restore, h]
    unfold Palette.declare Palette.find?
    rw [declare_find_eq]
    rfl

/-- Keyed last-wins for colours (T2), the same statement `\tokens` carries:
the declared colour is the one resolved. -/
public theorem Palette.declare_last_wins (p : Palette) (k : String) (c : Color) :
    (p.declare k c).find? k = some c := by
  unfold declare find?
  rw [declare_find_eq]
  rfl

/-- Declaring a colour resolves to that colour for either decorative flag. -/
public theorem Palette.declare_find_exact (p : Palette) (key : String)
    (color : Color) (decorative : Bool) :
    (p.declare key color decorative).find? key = some color := by
  unfold Palette.declare Palette.find?
  rw [declare_find_eq]
  rfl

/-- Redeclaring a colour overwrites without residue (T2) — the door theme
bundles and documents share, so "override the theme's entry" is exact, not
approximate. -/
public theorem Palette.declare_overwrite (p : Palette) (k : String) (c c' : Color) :
    (p.declare k c).declare k c' = p.declare k c' := by
  unfold declare
  rw [declare_collapse]
  simp

/-- An override changes exactly what it names, the locality half: every
other key resolves as it did before, whether or not the declaration is
decorative. With `declare_last_wins` above this is the whole per-key
layering contract — every layer (engine default, theme bundle, document
declaration; values, not expressions, per the `Theme` docstring and PLAN
2026-09-17) installs through this one door, and the statement's absence is
what let a document's `\muted` erase a theme role silently. -/
public theorem Palette.declare_keeps_others (p : Palette) (k k' : String) (c : Color) (d : Bool)
    (h : k' ≠ k) : (p.declare k c d).find? k' = p.find? k' := by
  unfold declare find?
  rw [declare_keeps _ _ _ _ h]

/-- Restoring a page-ground key preserves every unrelated body declaration,
whether the opening palette supplies that key or leaves it absent. -/
public theorem Palette.restore_keeps_others (p opening : Palette) (key other : String)
    (h : other ≠ key) : (p.restore opening key).find? other = p.find? other := by
  unfold Palette.restore
  cases opening.find? key with
  | none => exact p.erase_keeps_others key other h
  | some c => exact p.declare_keeps_others key other c _ h

/-- Restoring one key never changes the palette's cover fraction. -/
public theorem Palette.restore_keeps_covered (p opening : Palette) (key : String) :
    (p.restore opening key).coveredFraction = p.coveredFraction := by
  unfold Palette.restore
  cases opening.find? key <;> rfl

/-- The restored key carries the opening declaration's decorative
classification when it exists, and no stale exemption when it does not. -/
public theorem Palette.restore_decorative_exact (p opening : Palette) (key : String) :
    (p.restore opening key).decorative.contains key =
      ((opening.find? key).isSome && opening.decorative.contains key) := by
  cases h : opening.find? key with
  | none => simp [Palette.restore, h, Palette.erase]
  | some c =>
    by_cases hd : key ∈ opening.decorative
    · by_cases hp : key ∈ p.decorative <;>
        simp [Palette.restore, h, Palette.declare, hd, hp]
    · simp [Palette.restore, h, Palette.declare, hd]

/-- A colour override never touches the covered fraction. -/
public theorem Palette.declare_keeps_covered (p : Palette) (k : String) (c : Color) (d : Bool) :
    (p.declare k c d).coveredFraction = p.coveredFraction := by rfl

/-- The decorative exemption rides with the declaration: a plain
redeclaration removes its key from the exempt set, so re-declaring a
colour without the opt-out restores the contrast check. The exemption is
WCAG 2.2 SC 1.4.3's decoration exemption, and it excuses the declared
value — a property of one declaration, never of the key forever: before
this statement a stale exemption outlived the value it excused, and a
redeclared colour shipped illegible in silence. -/
public theorem declare_decorative_rides (p : Palette) (k : String) (c : Color) :
    (p.declare k c false).decorative.contains k = false := by
  simp [Palette.declare]

/-- The other direction: declaring decorative exempts the key. -/
public theorem declare_decorative_names (p : Palette) (k : String) (c : Color) :
    (p.declare k c true).decorative.contains k = true := by
  simp only [Palette.declare, ite_true]
  by_cases h : k ∈ p.decorative <;> simp [h]

@[expose] public def Color.white : Color := { r := 255, g := 255, b := 255 }

/-- `pct`% of `x` over the rest of `y`, rounded half up — the one mixing
step, in whichever unit the model's components come in. -/
private def Color.mixStep (x y pct : Nat) : Nat := (x * pct + y * (100 - pct) + 50) / 100

/-- xcolor's `!` mix in sRGB: per 8-bit channel, rounded. The RGB path
of `mix`, bytewise the function every theme bundle was mixed with. -/
private def Color.mixSrgb (a : Color) (pct : Nat) (b : Color) : Color :=
  let ch (x y : UInt8) : UInt8 := UInt8.ofNat (mixStep x.toNat y.toNat pct)
  { r := ch a.r b.r, g := ch a.g b.g, b := ch a.b b.b }

/-- A colour's components in the CMYK model: its own when declared there,
otherwise xcolor's rgb→cmy→cmyk conversion (manual §6.2: `cmy = 1 − rgb`,
`k = min(c, m, y)`, then each of c, m, y less `k`), over the same
thousandths `pdfComponents` prints — so white is `(0,0,0,0)` and the
conversion is exact on the quantized channels. -/
private def Color.toCmyk (c : Color) : Nat × Nat × Nat × Nat :=
  match c.cmyk with
  | some q => q
  | none =>
    let cy := 1000 - milli c.r
    let m := 1000 - milli c.g
    let y := 1000 - milli c.b
    let k := min cy (min m y)
    (cy - k, m - k, y - k, k)

/-- xcolor's `!` mix in CMYK: per declared component, exactly, the second
operand brought into the model by `toCmyk`. The result is a CMYK
declaration (`ofCmyk`), so its preview and its PDF paint follow the same
two rules every declared print colour follows. -/
private def Color.mixCmyk (a : Nat × Nat × Nat × Nat) (pct : Nat) (b : Color) : Color :=
  let q := b.toCmyk
  Color.ofCmyk (mixStep a.1 q.1 pct) (mixStep a.2.1 q.2.1 pct)
    (mixStep a.2.2.1 q.2.2.1 pct) (mixStep a.2.2.2 q.2.2.2 pct)

/-- One step of xcolor's `!` mix: `pct`% of `a` over the rest of `b`, in
`a`'s model (xcolor manual §2.3.2: an expression is evaluated in the model
of its first colour). -/
public def Color.mix (a : Color) (pct : Nat) (b : Color) : Color :=
  match a.cmyk with
  | some q => mixCmyk q pct b
  | none => mixSrgb a pct b

/-- Mixing is closed in the first operand's model: a CMYK-first expression
stays CMYK, an RGB-first one stays RGB — the xcolor rule as an equation
over the engine's `mix`. -/
public theorem Color.mix_model_exact (a b : Color) (pct : Nat) :
    (a.mix pct b).model = a.model := by
  unfold Color.mix Color.model
  cases a.cmyk <;> rfl

/-- On the sRGB path `mix` is `mixSrgb`, bytewise the per-channel function
of before — what keeps every RGB-only theme bundle's value, and so every
contrast contract's `decide`, exactly where it was. -/
private theorem Color.mix_srgb_id (a b : Color) (pct : Nat) (h : a.cmyk = none) :
    a.mix pct b = a.mixSrgb pct b := by
  simp [Color.mix, h]

/-- A CMYK-first mix keeps every component the arithmetic says, exactly:
the rider of the result is the per-component step over the declared
operands. -/
private theorem Color.mix_cmyk_exact (a b : Color) (pct : Nat) (q : Nat × Nat × Nat × Nat)
    (h : a.cmyk = some q) :
    (a.mix pct b).cmyk = some (mixStep q.1 b.toCmyk.1 pct, mixStep q.2.1 b.toCmyk.2.1 pct,
      mixStep q.2.2.1 b.toCmyk.2.2.1 pct, mixStep q.2.2.2 b.toCmyk.2.2.2 pct) := by
  simp [Color.mix, h, Color.mixCmyk, Color.ofCmyk]

/-- The `!`-separated parts of a palette expression, each trimmed of ASCII
whitespace: structural recursion the kernel evaluates, so a contract over
`Palette.resolve` can close by `decide` — `String.splitOn`'s well-founded
recursion blocks kernel reduction. Behaviour matches
`(expr.splitOn "!").map (·.trimAscii.toString)` on every expression. -/
private def bangParts (cur : List Char) : List Char → List String
  | [] => [trimmed cur]
  | c :: rest =>
    if c == '!' then trimmed cur :: bangParts [] rest
    else bangParts (c :: cur) rest
where
  /-- `cur` holds the segment reversed; trim both ends of the restored order. -/
  trimmed (cur : List Char) : String :=
    let ws (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'
    String.ofList (((cur.dropWhile ws).reverse).dropWhile ws)

/-- xcolor's base colours, "always available" once the package loads
(xcolor manual §4.1, Table 1) — and the engine accepts xcolor natively,
so the names hold everywhere a colour expression resolves. Values are the
manual's rgb definitions scaled to sRGB bytes, rounded half up. A declared
palette entry of the same name wins, exactly as `\definecolor` overrides
in xcolor (`Palette.resolve` asks `find?` first). -/
private def xcolorBase (s : String) : Option Color :=
  match s with
  | "black" => some Color.black
  | "white" => some Color.white
  | "red" => some { r := 255, g := 0, b := 0 }
  | "green" => some { r := 0, g := 255, b := 0 }
  | "blue" => some { r := 0, g := 0, b := 255 }
  | "cyan" => some { r := 0, g := 255, b := 255 }
  | "magenta" => some { r := 255, g := 0, b := 255 }
  | "yellow" => some { r := 255, g := 255, b := 0 }
  | "brown" => some { r := 191, g := 128, b := 64 }
  | "lime" => some { r := 191, g := 255, b := 0 }
  | "olive" => some { r := 128, g := 128, b := 0 }
  | "orange" => some { r := 255, g := 128, b := 0 }
  | "pink" => some { r := 255, g := 191, b := 191 }
  | "purple" => some { r := 191, g := 0, b := 64 }
  | "teal" => some { r := 0, g := 128, b := 128 }
  | "violet" => some { r := 128, g := 0, b := 128 }
  | "gray" => some { r := 128, g := 128, b := 128 }
  | "darkgray" => some { r := 64, g := 64, b := 64 }
  | "lightgray" => some { r := 191, g := 191, b := 191 }
  | _ => none

/-- One atom of a palette expression: a declared entry first, then xcolor's
base colours — the single reader every name in an expression goes through. -/
private def Palette.atom (p : Palette) (s : String) : Option Color :=
  (p.find? s).orElse fun _ => xcolorBase s

/-- A palette expression: a name, or xcolor's `!` mix folding left —
`a!30!b` is 30% of `a` over `b`, and a trailing `a!30` mixes toward white,
so `black!2` is a near-white. xcolor's base colours are always available
(`xcolorBase`), and a declared entry of any of their names wins —
xcolor's `\definecolor{black}` overrides too — so a name means one thing
wherever it resolves: `find?` is the single reader of the entries, and
every atom here goes through it first. Before that rule, a palette naming
an entry `black` painted the declared colour where `find?` resolved and
pure black where a mix or `\textcolor` did
(`role_resolves_at_one_site` is the contract). -/
public def Palette.resolve (p : Palette) (expr : String) : Option Color :=
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
            match p.atom name with
            | some b => go (c.mix pct b) rest'
            | none => none
  match bangParts [] expr.toList with
  | [] => none
  | first :: rest =>
    match p.atom first with
    | some c => go c rest
    | none => none

/-- Resolve one typed colour specification to the single `Color` value both
backends consume. Named/no-model input delegates to the existing xcolor
expression resolver; every numeric model becomes a concrete value here and
nowhere else. -/
public def Palette.resolveSpec (p : Palette) : Decl.ColorSpec → Option Color
  | .named expr => p.resolve expr
  | .html r g b => some (Color.ofHtml r g b)
  | .rgbByte r g b => some (Color.ofRgbByte r g b)
  | .rgbUnit r g b => some (Color.ofRgbUnit r g b)
  | .gray v => some (Color.ofGray v)
  | .cmyk c m y k => some (Color.ofCmykSource c m y k)

/-- Parsing and resolution are one public door for source colour syntax.
Callers choose their diagnostic for an unsupported/malformed model or an
unresolved name, but no caller converts components independently. -/
public def Palette.resolveSource (p : Palette) (model : Option String) (src : String) :
    Except Decl.ColorSpecError (Option Color) := do
  return p.resolveSpec (← Decl.parseColorSpec model src)

/-- The typed resolver preserves the established no-model expression
semantics exactly. -/
public theorem Palette.resolveSpec_named_exact (p : Palette) (expr : String) :
    p.resolveSpec (.named expr) = p.resolve expr := by rfl

/-- Every concrete model projects by construction at the one resolving site,
retaining the source device operator while exposing one screen preview. -/
public theorem Palette.resolveSpec_models_exact (p : Palette) (r g b : UInt8)
    (x y z c m k : Decl.ColorComponent) :
    p.resolveSpec (.html r g b) = some (Color.ofHtml r g b) ∧
    p.resolveSpec (.rgbByte x y z) = some (Color.ofRgbByte x y z) ∧
    p.resolveSpec (.rgbUnit x y z) = some (Color.ofRgbUnit x y z) ∧
    p.resolveSpec (.gray x) = some (Color.ofGray x) ∧
    p.resolveSpec (.cmyk c m y k) = some (Color.ofCmykSource c m y k) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The mixing fold never leaves the model it started in: every step is a
`mix` whose first operand is the accumulator (`mix_model_exact`). -/
private theorem Palette.resolve_go_model_exact (p : Palette) :
    ∀ (parts : List String) (c c' : Color), Palette.resolve.go p c parts = some c' →
      c'.model = c.model
  | [], c, c', h => by
    simp only [Palette.resolve.go, Option.some.injEq] at h
    rw [h]
  | [pctS], c, c', h => by
    simp only [Palette.resolve.go] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq] at h
        rw [← h, Color.mix_model_exact]
  | pctS :: name :: rest', c, c', h => by
    simp only [Palette.resolve.go] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · have := Palette.resolve_go_model_exact p rest' _ _ h
          rw [this, Color.mix_model_exact]
        · exact absurd h (by simp)

/-- A palette expression resolves in the model of its first atom, whatever
the expression mixes in after it: `press!50!ink2` is a CMYK colour when
`press` is, `brand!50!press` an RGB one when `brand` is (xcolor manual
§2.3.2). Stated over the expression's own head, as `bangParts` splits it,
and over `atom`, the reader `resolve` itself uses for it. -/
private theorem Palette.resolve_model_exact (p : Palette) (expr : String) (c : Color)
    (h : p.resolve expr = some c) :
    ∃ first rest a, bangParts [] expr.toList = first :: rest ∧
      p.atom first = some a ∧ c.model = a.model := by
  unfold Palette.resolve at h
  split at h
  · exact absurd h (by simp)
  · rename_i first rest hparts
    split at h
    · rename_i a ha
      exact ⟨first, rest, a, hparts, ha, Palette.resolve_go_model_exact p rest a c h⟩
    · exact absurd h (by simp)

/-- A two-colour mix as its parts: `a!P!b`, or `a!P` over white — the one
step of xcolor's grammar whose weight a contrast repair can move without
touching the colours the author named. `none` for a bare name, a longer
chain, or a malformed expression. -/
public def Palette.mixParts (p : Palette) (expr : String) : Option (Color × Nat × Color) :=
  match bangParts [] expr.toList with
  | [first, pctS] => (p.atom first).bind fun a => pctS.toNat?.bind fun pct =>
      if pct > 100 then none else some (a, pct, Color.white)
  | [first, pctS, second] => (p.atom first).bind fun a => pctS.toNat?.bind fun pct =>
      if pct > 100 then none else (p.atom second).map fun b => (a, pct, b)
  | _ => none

/-- The mix expression with its weight replaced and its colours as written:
the spelling a re-weighted mix is reported in. -/
public def mixReweighed (expr : String) (pct : Nat) : String :=
  match bangParts [] expr.toList with
  | first :: _ :: rest => String.intercalate "!" (first :: toString pct :: rest)
  | parts => String.intercalate "!" parts

/-- **A mix's parts are the mix `resolve` computes.** The parts reader is a
second reading of the grammar `Palette.resolve` owns, so it is held to it:
whatever parts it returns mix to exactly the colour the expression
resolves to, and a re-weighting of those parts is a re-weighting of the
author's own mix, not of a colour the reader invented. -/
public theorem Palette.mixParts_exact {p : Palette} {e : String} {a b : Color} {pct : Nat}
    (h : p.mixParts e = some (a, pct, b)) : p.resolve e = some (a.mix pct b) := by
  unfold Palette.mixParts at h
  unfold Palette.resolve
  split at h
  · rename_i first pctS hparts
    rw [hparts]
    cases ha : p.atom first with
    | none => simp [ha] at h
    | some a0 =>
      cases hp : pctS.toNat? with
      | none => simp [ha, hp] at h
      | some q =>
        by_cases hq : q > 100
        · simp [ha, hp, hq] at h
        · simp only [ha, hp, hq, Option.bind_some, ite_false, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp [Palette.resolve.go, hp, hq, ha]
  · rename_i first pctS second hparts
    rw [hparts]
    cases ha : p.atom first with
    | none => simp [ha] at h
    | some a0 =>
      cases hp : pctS.toNat? with
      | none => simp [ha, hp] at h
      | some q =>
        by_cases hq : q > 100
        · simp [ha, hp, hq] at h
        · cases hb : p.atom second with
          | none => simp [ha, hp, hb] at h
          | some b0 =>
            simp only [ha, hp, hq, hb, Option.bind_some, ite_false, Option.map_some,
              Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            simp [Palette.resolve.go, hp, hq, hb, ha]
  · exact absurd h (by simp)

/-- Font families a document asks for, as declared by `\fonts`. `dirs` are
directories of font files the document ships, relative to the document, so a
document that carries its fonts renders the same on every host. Every `dir`
declared is kept: fontspec's `Path=` may name a different one per face. -/
public structure FontSpec where
  body : Option String := none
  sans : Option String := none
  mono : Option String := none
  /-- The math face (`\fonts{ math = ... }`, fontspec's `\setmathfont`):
  resolved like any named face, and required to carry an OpenType MATH
  table to be used. -/
  math : Option String := none
  /-- unicode-math's option-driven alphabet sources. The default is the
  package's (`text` for roman, italic, bold, sans and mono); explicit
  `=sym` values survive compatibility rewriting as typed policy. -/
  mathSources : Math.MathAlphabetSources := {}
  dirs : Array String := #[]
  /-- Per-variant faces the document named (fontspec's `UprightFont=`,
  `BoldFont=`, `ItalicFont=`, `BoldItalicFont=`, `FontFace={series}{shape}`):
  `(slot, weight, italic)` → the face name, resolved like any other named
  face and winning over the family's own variant. The weight is a series's
  CSS number (`Weight.css`). -/
  faces : Array ((Nat × Nat × Bool) × String) := #[]
  deriving Repr, BEq, Inhabited

/-- Replace-on-redeclare, the same door `Tokens.declare` and
`Palette.declare` are: a later declaration of the same variant overrides,
keeping one entry per `(slot, weight, italic)`. Sourced: fontspec (v2.9,
§"Choosing additional fonts") — each `\setmainfont`/`BoldFont=` call
*replaces* the family's setup for that shape; the last one given is the one
used. -/
public def FontSpec.declareFace (s : FontSpec) (variant : Nat × Nat × Bool)
    (face : String) : FontSpec :=
  { s with faces := (s.faces.filter (·.1 != variant)).push (variant, face) }

/-- The face the document declared for one slot variant, if any. -/
public def FontSpec.faceFor (s : FontSpec) (slot weight : Nat) (italic : Bool) : Option String :=
  (s.faces.find? (·.1 == (slot, weight, italic))).map (·.2)

/-- The last-declared face is the one resolved (the fontspec rule above,
mirroring `declare_overwrite` for tokens): redeclaring a variant is an
override, never a silently first-wins accident. -/
public theorem FontSpec.faceFor_last_declared (s : FontSpec) (v : Nat × Nat × Bool)
    (f : String) : (s.declareFace v f).faceFor v.1 v.2.1 v.2.2 = some f := by
  have hnone : (s.faces.filter (·.1 != v)).find? (·.1 == (v.1, v.2.1, v.2.2)) = none := by
    rw [Array.find?_eq_none]
    intro x hx
    have hne := (Array.mem_filter.mp hx).2
    simp only [bne_iff_ne, ne_eq] at hne
    simp only [beq_iff_eq]
    intro hcontra
    exact hne (by simpa using hcontra)
  unfold declareFace faceFor
  rw [Array.find?_push, hnone]
  simp

/-- What the reader must be able to reach in place of a non-text element:
`judged` is today's rule — the alt judges name a missing alternative and
`accessibility = AA` reads them; `required` asks the artifact itself to
carry the alternative as reader-visible structure, which only an artifact
with an alternative channel can honour. -/
public inductive AltPolicy where
  | judged
  | required
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The colour the reader is meant to see: `device` leaves the numbers to
the reader's device, today's rule; `srgb` asks that the artifact define
its colours as sRGB. -/
public inductive ColorIntent where
  | device
  | srgb
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Whether the artifact carries the faces it was set in: `embedded`, the
faces travel with the artifact (embedded in the PDF, shipped beside the
page); `none`, the document accepts that something else owns them — a
site's stylesheet. -/
public inductive FontPolicy where
  | embedded
  | none
  deriving Repr, @[expose] BEq, DecidableEq, Inhabited

/-- The semantic output contract: facts about the artifact the reader must
get, declared once in `\output` and read by every backend against its own
realization record. Every default is today's behaviour, so an undeclared
document builds exactly as before. `fonts` is the one field with no
default of its own: undeclared, `Doc.fontPolicy` derives it from the
stylesheet story the document told. -/
public structure OutputContract where
  alternatives : AltPolicy := .judged
  color : ColorIntent := .device
  fonts : Option FontPolicy := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a backend carries alternatives: `none` (the PDF today: alt text has
no channel until the artifact is tagged), `attribute` (HTML's `alt`). -/
public inductive AltReal where
  | none
  | attribute
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a backend carries colour: `device` (the PDF writes device colour
with no output intent), `srgbByDefinition` (CSS colours are sRGB by the
specification, so the HTML meets `srgb` with nothing to do). -/
public inductive ColorReal where
  | device
  | srgbByDefinition
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a backend carries faces: `embeds` (in the file), `ships` (beside
the page, when the document's policy asks). -/
public inductive FontReal where
  | embeds
  | ships
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a backend uses script: `never`; `constantGated` (one constant
script, gated on a class, with a declared floor when scripting is off). -/
public inductive ScriptReal where
  | never
  | constantGated
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a backend carries mathematics: `layout` (glyphs placed by the
engine), `mathmlCore` (MathML Core, the browser lays out). -/
public inductive MathReal where
  | layout
  | mathmlCore
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One backend's realization record: values only, the `ClassRecord`
discipline. The values are backend vocabulary living here because both
backends must read one type and this module cannot import a backend;
each constant lives in its own backend (`Pdf.profile`, `HtmlDoc.profile`).
`scripting` and `math` are recorded but no contract key reads them yet. -/
public structure Realization where
  alternatives : AltReal
  color : ColorReal
  fonts : FontReal
  scripting : ScriptReal
  math : MathReal
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A declared contract fact an artifact does not realize: the fact's key,
what was declared, what the artifact does instead. -/
public structure Unmet where
  fact : String
  declared : String
  realized : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The closed key list of the contract — the facts `unmet` can name and
the keys `\output` accepts for them. -/
public def OutputContract.facts : List String := ["alternatives", "color", "fonts"]

/-- One fact judged: unmet when the realization cannot honour the
declaration. Written as one door so `unmet_covers` reads the fact key off
the call, never off the message. -/
private def OutputContract.judge (fact declared realized : String) (met : Bool) :
    Option Unmet :=
  if met then none else some { fact, declared, realized }

private theorem OutputContract.judge_fact {fact declared realized : String} {met : Bool}
    {u : Unmet} (h : OutputContract.judge fact declared realized met = some u) :
    u.fact = fact := by
  unfold judge at h
  split at h
  · exact absurd h (by simp)
  · cases h; rfl

/-- The facts this artifact does not realize, one entry per unmet key.
`alternatives = required` needs an alternative channel; `color = srgb`
needs colours defined as sRGB; `fonts = embedded` is met by either way of
carrying faces, so it is unmet by no realization recorded today — the
markdown twin's record, when it exists, is where that arm fires.
`fonts = none` and every default ask nothing. -/
public def OutputContract.unmet (c : OutputContract) (r : Realization) : Array Unmet :=
  #[judge "alternatives" "required" "no alternative channel"
      (match c.alternatives, r.alternatives with
        | .judged, _ => true
        | .required, .attribute => true
        | .required, .none => false),
    judge "color" "srgb" "device colour"
      (match c.color, r.color with
        | .device, _ => true
        | .srgb, .srgbByDefinition => true
        | .srgb, .device => false),
    judge "fonts" "embedded" "no faces carried"
      (match c.fonts, r.fonts with
        | none, _ => true
        | some .none, _ => true
        | some .embedded, .embeds => true
        | some .embedded, .ships => true)].filterMap id

/-- The undeclared contract asks nothing of any realization. -/
public theorem OutputContract.unmet_default_exact (r : Realization) :
    ({} : OutputContract).unmet r = #[] := by
  simp [unmet, judge]

/-- Every unmet fact names a key of the closed list (`_covers`): a
diagnostic's `subject` is always one of the keys `\output` accepts. -/
public theorem OutputContract.unmet_covers (c : OutputContract) (r : Realization) :
    ∀ u ∈ c.unmet r, u.fact ∈ OutputContract.facts := by
  intro u hu
  simp only [unmet, Array.mem_filterMap, id] at hu
  obtain ⟨j, hj, hju⟩ := hu
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;> rw [judge_fact hju] <;> simp [facts]

/-- Each unmet fact is one W0701 whose `subject` is the fact's key: the
warning is per artifact and per fact, never merged, so a document that
declares two facts a backend lacks is told twice, once each. -/
public def contractDiags (us : Array Unmet) : Array Diag :=
  us.map fun u =>
    Diag.of .W0701
      s!"output contract: '{u.fact} = {u.declared}' is declared and this artifact carries {u.realized}"
      (help := some s!"drop '{u.fact} = {u.declared}' from '\\output', or build a format that carries it")
      (subject := some u.fact)

/-- One diagnostic per unmet fact (`_accounts`): the census of unmet facts
and the warnings reporting them are the same count. -/
public theorem contract_accounts (us : Array Unmet) : (contractDiags us).size = us.size :=
  Array.size_map ..

/-- What to build, as declared by `\output`: the document carries its own
build intent, the way `\documentclass` already does. Names stay strings here
so the core does not know the CLI's option types. -/
public structure OutputSpec where
  formats : Array String := #[]
  /-- The semantic contract the artifacts are held to (`OutputContract`);
  every key defaults to today's behaviour. -/
  contract : OutputContract := {}
  /-- The conformance profiles the PDF is held to (`profiles = pdf/a-4,
  pdf/ua-2`): a set of registered names, each implying the assertion
  `pdf.profile = <name>`, judged on the census of the built bytes. Names
  stay strings here for the reason `formats` does; the PDF contract module
  owns the table they index. -/
  profiles : Array String := #[]
  css : Option String := none
  /-- A local stylesheet the driver captures relative to the document.
  Its rules follow the engine's styles, so the named sheet wins ties.
  Checked HTML publication refuses uncaptured rendering dependencies. -/
  stylesheet : Option String := none
  /-- The markdown twin's written file name (`md = "llms.txt"`): the twin
  exists for the llms.txt convention (llmstxt.org), whose name is fixed,
  and the HTML head's alternate link must name the file as served — a
  build that renames the output after the fact breaks that link, so the
  name is declared where the build intent lives. Undeclared, the twin
  takes the source's stem. -/
  md : Option String := none
  deriving Repr, BEq, Inhabited

/-- One format onto the list, dedup by name: the pure half of
`applyOutput`'s formats walk, extracted so the no-duplicates statement
ranges over the function the engine runs. -/
public def OutputSpec.addFormat (o : OutputSpec) (f : String) : OutputSpec :=
  { o with formats := if o.formats.contains f then o.formats else o.formats.push f }

/-- A format list never grows a duplicate (T4): `formats = pdf, pdf` and a
second `\output` block naming `pdf` again are one entry — the list-append
half of the surface stays a set. -/
public theorem OutputSpec.addFormat_nodup (o : OutputSpec) (f : String)
    (h : o.formats.toList.Nodup) : (o.addFormat f).formats.toList.Nodup := by
  unfold addFormat
  split
  · exact h
  · next hc =>
    rw [Array.toList_push]
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_singleton] at hy
    apply hc
    subst hy
    subst hxy
    simpa [Array.contains_iff_mem] using hx

/-- One profile onto the set, dedup by name: the pure half of
`applyOutput`'s profiles walk, `addFormat`'s twin. -/
public def OutputSpec.addProfile (o : OutputSpec) (p : String) : OutputSpec :=
  { o with profiles := if o.profiles.contains p then o.profiles else o.profiles.push p }

/-- A profile set never grows a duplicate: `profiles = pdf/a-4, pdf/a-4` is
one entry and one implied assertion — the declaration is a set. -/
public theorem OutputSpec.addProfile_nodup (o : OutputSpec) (p : String)
    (h : o.profiles.toList.Nodup) : (o.addProfile p).profiles.toList.Nodup := by
  unfold addProfile
  split
  · exact h
  · next hc =>
    rw [Array.toList_push]
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_singleton] at hy
    apply hc
    subst hy
    subst hxy
    simpa [Array.contains_iff_mem] using hx

/-- Document metadata, as declared by `\pdfmeta` — the one record every
surface derives from. The PDF reads title/author/subject/keywords into its
Info dictionary and XMP, and `url` into XMP `dc:identifier`; the HTML head
reads all of them plus `image` and `favicon`; the markdown twin reads title
and subject as its llms.txt preamble. `image` and `favicon` are web-surface
facts with no PDF meaning; nothing else here is per-backend. -/
public structure Meta where
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
  /-- The document's main language, a BCP 47 tag: babel's package options
  declare it (last option = main, babel's rule), `\pdfmeta{ language = .. }`
  spells it natively. Both artifacts declare it — `<html lang>` and the
  PDF catalog `/Lang` — and every language-reading site (captions,
  hyphenation patterns, quotes) resolves through it. -/
  language : Option String := none
  /-- The PDF version the document declares (`\DocumentMetadata{
  pdfversion = 1.7 }`, natively `\pdfmeta{ version = "1.7" }`): `1.7`
  writes a PDF 1.7 file — the header, and the structure tree in 1.7's one
  standard namespace with the 2.0-only types role-mapped onto 1.7's
  (`Pdf.pdf17Role`). Undeclared, or `2.0`, the file is PDF 2.0. -/
  pdfVersion : Option String := none
  deriving Repr, BEq, Inhabited

/-- The document's resolved main locale: the declared language when a
record ships for it, English otherwise (the site that declared the tag
named the miss, W0368). One resolving site, read by both backends. -/
public def Meta.locale (m : Meta) : Locale :=
  (m.language.bind Locale.forTag).getD Locale.en

/-- The OpenType features both backends apply, one record: the PDF path
applies them to the glyphs it sets, the HTML path requests them of the
browser (`font-kerning`), so the artifacts cannot disagree —
`features_agree` holds by construction, the two emissions being two
projections of one value. `kern` defaults on, HarfBuzz's own default
set; a `\tokens` knob arrives with the features it gates, and until
then the record is the engine's one constant. -/
public structure Features where
  kern : Bool := true
  deriving Repr, BEq, Inhabited

/-- The features in force: the one resolving site. -/
public def features : Features := {}

public inductive CmpOp where
  | eq
  | ne
  | le
  | lt
  | ge
  | gt
  deriving Repr, BEq, Inhabited

public def CmpOp.label : CmpOp → String
  | .eq => "=="
  | .ne => "!="
  | .le => "<="
  | .lt => "<"
  | .ge => ">="
  | .gt => ">"

public def CmpOp.holds : CmpOp → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .le, a, b => a ≤ b
  | .lt, a, b => a < b
  | .ge, a, b => a ≥ b
  | .gt, a, b => a > b

/-- A layout invariant the engine checks against what it actually shipped. -/
public inductive AssertKind where
  | pages (op : CmpOp) (n : Int)
  | fontsAllEmbedded
  /-- Every piece of ink inside the margins. On a card the margins are the
  print safe zone, so this is "nothing risks the trim". -/
  | textInArea
  /-- The smallest x-height set anywhere is at least this, judged from each
  run's font at its size: the legibility floor is an angular x-height, so
  the check reads the metric the source speaks in. -/
  | minXHeight (min : Sp)
  /-- The document conforms to the engine's judged WCAG 2.2 AA rows: no
  accessibility fact the judges name (a failing contrast pair, an image
  with no text alternative, a broken heading outline) and a declared
  language. Facts the engine cannot judge (a PDF's tagged reading order,
  browser rendering) are outside the assertion and stay named in PLAN,
  never implied passes. -/
  | accessibilityAA
  /-- The PDF satisfies the named conformance profile's contract, judged
  on the read-side census of the bytes just built — implied by
  `\output{ profiles = <name> }`, one per name, never declared directly.
  It fails with the violated rules as its actual; nothing claims the
  profile in the file until the writer reads the contract. -/
  | pdfProfile (name : String)
  deriving Repr, BEq, Inhabited

public def AssertKind.source : AssertKind → String
  | .pages op n => s!"pages {op.label} {n}"
  | .fontsAllEmbedded => "fonts.all_embedded"
  | .textInArea => "text.in_area"
  | .minXHeight m => s!"text.xheight >= {m.toPtString}pt"
  | .accessibilityAA => "accessibility = AA"
  | .pdfProfile name => s!"pdf.profile = {name}"

/-- The emitted artifacts an assertion is judged on, in `OutputSpec.formats`'
own vocabulary (`"pdf"`, `"html"`, `"md"`; strings, so the core learns no
CLI type). Empty means the assertion reads no artifact:

| kind | reads | judged on |
|---|---|---|
| `pages`, `textInArea`, `minXHeight` | none | the layout, whatever is emitted — facts of `Layout.run`, which runs unconditionally and is a function of the document |
| `accessibilityAA` | none | the document and its judged diagnostics, neither per artifact |
| `fontsAllEmbedded` | `pdf`, `html` | each emitted artifact: the PDF by the census of its bytes, the HTML by the faces it ships beside the page |
| `pdfProfile` | `pdf` | the PDF alone, by the census of its bytes against the profile's contract |

The driver judges a non-empty `reads` against what the run emits, and a
run emitting none of them fails the assertion loud rather than passing it
vacuously (`assert_reads_shipped`). No class implies `fontsAllEmbedded`, so
that failure is reachable only from a document that asked; `pdfProfile` is
implied by `profiles =`, so `formats = html, profiles = pdf/a-4` fails
there too. -/
public def AssertKind.reads : AssertKind → Array String
  | .pages _ _ => #[]
  | .fontsAllEmbedded => #["pdf", "html"]
  | .textInArea => #[]
  | .minXHeight _ => #[]
  | .accessibilityAA => #[]
  | .pdfProfile _ => #["pdf"]

/-- The assertions whose subject is bytes are the ones that read
artifacts: the font one reads exactly the two that carry faces, a profile
one reads exactly the PDF (`_accounts` shape: the per-artifact judgement
is paid for by a named artifact list). -/
public theorem assert_reads_shipped :
    (∀ k : AssertKind, k.reads ≠ #[] ↔ k = .fontsAllEmbedded ∨ ∃ n, k = .pdfProfile n) ∧
    AssertKind.reads .fontsAllEmbedded = #["pdf", "html"] ∧
    ∀ n, AssertKind.reads (.pdfProfile n) = #["pdf"] := by
  refine ⟨fun k => ?_, rfl, fun _ => rfl⟩
  cases k <;> simp [AssertKind.reads]

public structure Assertion where
  kind : AssertKind
  span : Option Span := none
  /-- Failure guidance. A class-implied assertion says which contract fired
  and how declaring intent takes control of it. -/
  help : Option String := none
  deriving Repr, BEq, Inhabited

/-- The weight axis: the nine NFSS series values (LaTeX News 31, "Improved
load-times for expl3 … New or improved commands": the standardised weight
codes; fntguide §2.2's series axis) the surface can select —
`\fontseries`, fontspec's `FontFace={series}{shape}{font}`. It lives in
the IR because both backends read it: the PDF resolves a face per weight
(`FontSet.lookup`), the HTML emits the numeric value per run. -/
public inductive Weight where
  | ul | el | l | sl | m | sb | b | eb | ub
  deriving Repr, BEq, DecidableEq

public instance : Inhabited Weight := ⟨.m⟩

/-- The CSS/OpenType numeric value of each series (CSS Fonts 4 §2.2 /
OpenType OS/2 `usWeightClass`, the same registry: 100 Thin, 200
Extra-light, 300 Light, 400 Normal, 600 Semi-bold, 700 Bold, 800
Extra-bold, 900 Black). `m` is NFSS's *default* series — the regular
weight, 400, not the registry's 500 "Medium" — and `sl` (semi-light) has
no slot in the nine-step table; 350 is DirectWrite's `SemI_LIGHT`, the
one registry that names it. No single authority numbers all nine, so
those two placements are this table's decision; the round-trip theorem
below is what makes the assignment a bijection onto its image. -/
public def Weight.css : Weight → Nat
  | .ul => 100
  | .el => 200
  | .l => 300
  | .sl => 350
  | .m => 400
  | .sb => 600
  | .b => 700
  | .eb => 800
  | .ub => 900

/-- Every series, in weight order — what `ofCss` searches and the
round-trip theorem quantifies over. -/
public def Weight.all : List Weight := [.ul, .el, .l, .sl, .m, .sb, .b, .eb, .ub]

/-- The series nearest a numeric weight (a face's `usWeightClass`), ties
to the lighter: the inverse direction of the bijection, total over every
input. -/
public def Weight.ofCss (n : Nat) : Weight :=
  (Weight.all.foldl (init := Weight.ul) fun best w =>
    let d := fun v : Weight => max v.css n - min v.css n
    if d w < d best then w else best)

/-- The NFSS spelling of each series, `\fontseries`'s vocabulary. -/
public def Weight.series : Weight → String
  | .ul => "ul"
  | .el => "el"
  | .l => "l"
  | .sl => "sl"
  | .m => "m"
  | .sb => "sb"
  | .b => "b"
  | .eb => "eb"
  | .ub => "ub"

/-- The NFSS width codes (fntguide §2.2: the width half of a series
value). The engine has no width axis; parsing names them so a
`\fontseries{bx}` honours its weight and can say what the `x` asked for. -/
private def seriesWidthCodes : List String :=
  ["uc", "ec", "sc", "c", "sx", "ex", "ux", "x"]

/-- Parse an NFSS series value into its weight and width halves
(fntguide §2.2: a series combines a weight code and a width code, each
dropped when medium — `bx` is bold extended, `c` is medium condensed,
`m` is both). Longest weight code first, so `sb` is semi-bold, never
`s`+garbage. `none` when the string is no series value at all. -/
public def Weight.parseSeries (s : String) : Option (Weight × String) :=
  if s == "m" then some (.m, "") else
  let codes : List Weight := [.ul, .el, .sl, .sb, .eb, .ub, .l, .b]
  match codes.find? fun w => s.startsWith w.series with
  | some w =>
    let rest := (s.drop w.series.length).toString
    if rest.isEmpty || seriesWidthCodes.contains rest then some (w, rest)
    else none
  | none =>
    -- No weight half: the whole value must be a width code at medium
    -- weight (`c`, `x`, …).
    if seriesWidthCodes.contains s then some (.m, s) else none

/-- Bold, where a Bool is the question (WCAG 2.2's large-text criterion,
`FontDb.resolve`'s satisfaction check): the registry's own boundary, 700. -/
public def Weight.isBold (w : Weight) : Bool := 700 ≤ w.css

/-- The two directions of the series↔number map compose to the identity:
each series is the nearest series to its own number, which is what makes
`css` a bijection onto its image and `ofCss` its inverse there. The parse
half — `parseSeries w.series = some (w, "")` — is String-typed, which the
kernel cannot reduce, so it is pinned by an executable check in
Tests/FontMath rather than stated here. -/
public theorem Weight.ofCss_css_id : ∀ w : Weight, ofCss w.css = w := by
  intro w; cases w <;> rfl

public inductive Style where
  | bold
  | italic
  | mono
  | smallcaps
  | emph
  | sans
  | normal
  /-- The roman (serif) family: NFSS's `\rmfamily`/`\textrm`, the body slot.
  Family selection only — series and shape stand. -/
  | roman
  /-- The medium series: `\mdseries`/`\textmd` turns bold off without
  touching family or shape. -/
  | medium
  /-- A series off the bold/medium corners: `\fontseries{l}` and the runs
  a `FontFace={series}{shape}` declaration is selected for. `.bold` and
  `.medium` stay their own constructors — they are the two spellings LaTeX
  gives names to — and `Style.weight?` is the one map all three project
  through, so the backends cannot disagree on what a series means. -/
  | series (w : Weight)
  /-- The upright shape: `\upshape`/`\textup`. NFSS shapes are exclusive
  (fntguide §2.2: upright, italic, slanted, small caps are one axis), so
  selecting upright clears italic and small caps both. -/
  | upright
  | size (name : String)
  /-- `\fontsize{size}{leading}\selectfont`: both dimensions stay affine
  until the run's local measure and current font metrics are known. -/
  | fontSize (size leading : Affine Measure)
  /-- A language switch (BCP 47 tag): `\foreignlanguage`, `\selectlanguage`,
  babel's `otherlanguage`. Not a new `Inline` constructor — every walk
  already recurses through `.styled` generically, and the attribute is
  pure markup (`langWrap_text`): hyphenation patterns and the artifacts'
  span-level language declarations read it, ink never moves. -/
  | lang (tag : String)
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
@[expose] public def sizeScale : List (String × Nat) :=
  [("tiny", 500), ("scriptsize", 700), ("footnotesize", 800), ("small", 900),
   ("normalsize", 1000), ("large", 1200), ("Large", 1440), ("LARGE", 1728),
   ("huge", 2074), ("Huge", 2488)]

/-- A named step of the scale applied to a base size — the one resolving
site for `base * step / 1000`, so the backends and the layout cannot
drift on what a named size means. A name off the scale is the base
itself: the identity factor, `normalsize`'s. -/
@[expose] public def scaleStep (base : Sp) (name : String) : Sp :=
  base * ((sizeScale.lookup name).getD 1000) / 1000

/-- The size a document title sets at when no `titlepage` font template
declares one: the one resolving site, so the two backends read one
function rather than each naming a step. A flow page takes `LARGE`
(classes.dtx's `\@maketitle` sets `{\LARGE \@title \par}`); a deck takes
`Large`, one step below (beamerfontthemedefault.sty,
`\setbeamerfont{title}{size=\Large, parent=structure}`, the step
beamerfontthememoloch.sty re-declares for its own lineage). Reading the
flow step on a deck set its title 20% large, enough to re-flow a title
line whose breaks the author declared. -/
@[expose] public def titleSize (base : Sp) (slides : Bool) : Sp :=
  scaleStep base (if slides then "Large" else "LARGE")

/-- Adjacent steps of the scale, in order: what the scale theorems below
quantify over. -/
public def sizeScaleSteps : List (Nat × Nat) :=
  (sizeScale.map (·.2)).zip (sizeScale.map (·.2)).tail

/-- The scale is strictly monotone: a larger name is a larger size, so a
document can rank two declared sizes by rank alone. -/
public theorem sizeScale_monotone : ∀ p ∈ sizeScaleSteps, p.1 < p.2 := by decide

/-- Every step's ratio lies in [10⁄9, 7⁄5]: no two adjacent sizes collapse
into each other (at least a major second apart) and no step jumps more than
`tiny`'s catch-up to `scriptsize` (a ratio band, the modular-scale property,
stated over the integers). -/
public theorem sizeScale_ratio_band :
    ∀ p ∈ sizeScaleSteps, 10 * p.1 ≤ 9 * p.2 ∧ 5 * p.2 ≤ 7 * p.1 := by decide

/-- `normalsize` is the identity: the scale is anchored at the body size. -/
public theorem sizeScale_normalsize : sizeScale.lookup "normalsize" = some 1000 := by decide

/-- Above `normalsize` the scale is geometric with ratio 1.2 to per-mille
rounding: each step is `\magstep`'s minor-third ratio, |6a − 5b| ≤ 4‰. -/
public theorem sizeScale_display_geometric :
    ∀ p ∈ sizeScaleSteps, 1000 ≤ p.1 →
      6 * p.1 ≤ 5 * p.2 + 4 ∧ 5 * p.2 ≤ 6 * p.1 + 4 := by decide

/-- The card's contract and the type scale agree at the card's own base
size: at the conventional x-height ratio (half the nominal size, the
fallback the shipped-ink judge uses for a font that declares none), every
scale step from `footnotesize` up clears the 1.4 mm legibility floor the
class implies — the class never states an assertion its own defaults
violate, and what fails (`scriptsize`, `tiny`) is exactly what the
assertion exists to catch on the shipped pages. -/
public theorem card_floor_within_scale :
    ∀ p ∈ sizeScale, 800 ≤ p.2 →
      baseFontSize * (p.2 : Int) / 1000 / 2 ≥ cardXHeightFloor := by decide

/-- The poster's mirror of `card_floor_within_scale`: at the same
half-nominal fallback ratio, every scale step from `footnotesize` up on
beamerposter's scale-1 body (`posterFontSize`) clears the 1 m fluent-
reading floor — the class never states an assertion the calibration it is
derived from violates, and what fails (`scriptsize`, `tiny`, or a body
pasted in unscaled from an article) is what the assertion exists to catch. -/
public theorem poster_floor_within_scale :
    ∀ p ∈ sizeScale, 800 ≤ p.2 →
      posterFontSize * (p.2 : Int) / 1000 / 2 ≥ posterXHeightFloor := by decide

/-- Whether a ladder never decreases in its named order — what the size
read-out door demands of a venue's ladder. Non-strict where the engine's
own scale is strict (`sizeScale_monotone`): a venue may set two
neighbouring sizes equal (the NeurIPS lineage sets `\footnotesize` =
`\small` = 9 pt), and what the door refuses is disorder — a larger name
set smaller. `sizeScale` itself is ordered (`sizeScale_stepsOrdered`),
and `size_ladder_monotone` extends the property to every ladder the door
accepts. -/
public def stepsOrdered (scale : List (String × Nat)) : Bool :=
  ((scale.map (·.2)).zip (scale.map (·.2)).tail).all fun p => p.1 ≤ p.2

public theorem sizeScale_stepsOrdered : stepsOrdered sizeScale = true := by decide

/-- Replace one named step of a ladder — the door a venue's refused
`\@setfontsize` size commands are read through, per-mille of the body.
`none` when the name is off the ladder or the replaced ladder would no
longer be ordered: LaTeX's own scale is ordered by design (size10.clo's
values), and the engine's size comparisons assume it, so a venue step
that breaks the order keeps the built-in instead, named. -/
public def setStep (scale : List (String × Nat)) (name : String) (f : Nat) :
    Option (List (String × Nat)) :=
  if (scale.lookup name).isNone then none
  else
    let s' := scale.map fun p => if p.1 == name then (p.1, f) else p
    if stepsOrdered s' then some s' else none

/-- Every ladder `setStep` accepts is ordered in the named order: the
read-out cannot admit a venue that sets `\small` larger than
`\normalsize` — that step keeps the built-in (W0361 names it). -/
public theorem size_ladder_monotone (scale : List (String × Nat)) (name : String)
    (f : Nat) (s' : List (String × Nat)) (h : setStep scale name f = some s') :
    stepsOrdered s' = true := by
  unfold setStep at h
  split at h
  · exact absurd h (by simp)
  · dsimp only at h
    split at h
    next hm => injection h with h'; subst h'; exact hm
    next => exact absurd h (by simp)

/-- Replace several named steps at once, judged as one ladder — the door a
venue's whole read-out goes through first: per-step application through
`setStep` depends on the order the venue wrote its redefinitions in (a
ladder shrunk from `\small` down is refused at `\small` against the
engine's still-standing `\footnotesize`), and a venue's ladder is one
declaration, not a sequence. `none` when the replaced ladder disorders;
the caller then salvages step by step and the offenders are named. -/
public def setStepsAll (scale : List (String × Nat)) (steps : List (String × Nat)) :
    Option (List (String × Nat)) :=
  let s' := scale.map fun q => match steps.lookup q.1 with
    | some f => (q.1, f)
    | none => q
  if stepsOrdered s' then some s' else none

/-- The batch door's half of `size_ladder_monotone`: a venue ladder
accepted whole is ordered whole. -/
public theorem size_ladder_monotone_all (scale steps : List (String × Nat))
    (s' : List (String × Nat)) (h : setStepsAll scale steps = some s') :
    stepsOrdered s' = true := by
  unfold setStepsAll at h
  dsimp only at h
  split at h
  next hm => injection h with h'; subst h'; exact hm
  next => exact absurd h (by simp)

/-- The size ladder in force for a document: its own, read from a venue's
size commands, or the engine's scale. The one resolving site — a consumer
of a named size step reads the ladder from here (or the `Geom` copy of
it), never `sizeScale` directly, now that a document may own the ladder. -/
public def PageSpec.scale (p : PageSpec) : List (String × Nat) :=
  p.sizes.getD sizeScale

/-- `scaleStep` over a document's ladder: the same integer arithmetic, the
scale a parameter. A name off the ladder is the base itself. -/
public def scaleStepIn (scale : List (String × Nat)) (base : Sp) (name : String) : Sp :=
  base * ((scale.lookup name).getD 1000) / 1000

public theorem scaleStepIn_default (base : Sp) (name : String) :
    scaleStepIn sizeScale base name = scaleStep base name := by rfl

public def Style.label : Style → String
  | .bold => "bold"
  | .italic => "italic"
  | .mono => "mono"
  | .smallcaps => "smallcaps"
  | .emph => "emph"
  | .sans => "sans"
  | .normal => "normal"
  | .roman => "roman"
  | .medium => "medium"
  | .series w => s!"series:{w.series}"
  | .upright => "upright"
  | .size n => s!"size:{n}"
  | .fontSize _ _ => "fontsize"
  | .lang tag => s!"lang:{tag}"


/-- What a resolved cross-reference renders (`refText`): LaTeX's bare
number (`\ref`) and parenthesised equation number (`\eqref`), and
cleveref's forms (cleveref manual v0.21.4 §2) — the kind's locale name
before the number (`\cref`/`\Cref` — `cap` picks the capitalised name,
which English also unabbreviates), the first key of a `\crefrange` pair
(plural name, number, the range conjunction), the label format alone
(`\labelcref`, also the range pair's second key), and the name alone
(`\namecref`/`\nameCref`). -/
public inductive RefForm where
  | plain
  | paren
  | cref (cap : Bool)
  | crefRange (cap : Bool)
  | labelOnly
  | name (cap : Bool)
  deriving Repr, BEq

/-- The natbib command a citation was written with — natbib.sty's command
table (`\DeclareRobustCommand\citet` and its siblings), each one setting
which parts print and whether brackets wrap them: `\citet` (textual),
`\citep` (parenthetical), `\cite` (`auto`: textual in author-year mode,
parenthetical in numbers mode, natbib.sty `\NAT@cites`), `\citealt` and
`\citealp` (the two without brackets), `\citeauthor`, `\citeyear`,
`\citeyearpar`, `\citenum` (the list position alone), `\citetext`
(natbib.sty's `\NAT@open#1\NAT@close`: the elaborator sets its body as body
text between two `bracket` marks, so a citation inside it is a citation like
any other), and the kernel's `\nocite` (its keys enter the list, and nothing
prints). Which punctuation draws them is the bibliography's to decide
(`Bib.renderCite`). -/
public inductive CiteCmd where
  | textual
  | paren
  | auto
  | alt
  | alp
  | author
  | year
  | yearPar
  | num
  | text
  | nocite
  /-- One citation bracket, natbib's `\NAT@open` when `opening` and its
  `\NAT@close` otherwise: the marks `\citetext` sets around its body. -/
  | bracket (opening : Bool)
  deriving Repr, BEq, Inhabited

/-- What a citation declares beside its keys: the command, the starred
form's full author list (`\citet*`), the capitalized form (`\Citet`), and
the optional notes — one `[...]` is the note after the citation, two are
the notes before and after it (natbib.sty's header: `\citep[see][p.~5]`).
A note is its elaborated text: natbib sets it as written, and nothing in a
citation's rendering reads structure inside one. -/
public structure CiteForm where
  cmd : CiteCmd
  full : Bool := false
  up : Bool := false
  pre : String := ""
  post : String := ""
  deriving Repr, BEq, Inhabited

/-- natbib's citation commands (natbib.sty's command table), each with the
form it selects: `\citefullauthor` is `\citeauthor*` there, and the
capitalized five are the only ones natbib defines; the kernel's `\cite` and
`\nocite` are read through the same rows, with natbib or without it. The
one naming site — the elaborator reads a command through it and the dump
spells a form back through it. -/
public def natbibCites : List (String × CiteForm) :=
  [("citet", { cmd := .textual }), ("citep", { cmd := .paren }),
   ("cite", { cmd := .auto }), ("citealt", { cmd := .alt }),
   ("citealp", { cmd := .alp }), ("citeauthor", { cmd := .author }),
   ("citefullauthor", { cmd := .author, full := true }),
   ("citeyear", { cmd := .year }), ("citeyearpar", { cmd := .yearPar }),
   ("citenum", { cmd := .num }), ("citetext", { cmd := .text }),
   ("nocite", { cmd := .nocite }),
   ("Citet", { cmd := .textual, up := true }), ("Citep", { cmd := .paren, up := true }),
   ("Citealt", { cmd := .alt, up := true }), ("Citealp", { cmd := .alp, up := true }),
   ("Citeauthor", { cmd := .author, up := true })]

/-- The command a form spells back as; a bracket mark as the natbib macro it
is. -/
public def CiteForm.command (f : CiteForm) : String :=
  if let .bracket o := f.cmd then (if o then "NAT@open" else "NAT@close")
  else ((natbibCites.find? fun (_, g) => g.cmd == f.cmd && g.up == f.up).map (·.1)).getD "cite"

/-- The weight a style selects, when it touches the axis: the one map
`.bold`, `.medium`, `.series`, and `.normal`'s reset project through.
Layout's `applyStyle` follows it exactly (`weight_agree` in Layout.lean),
and the HTML emission reads the same `w` its `.series` arm carries — so
the face a run selects is one function of the style in both backends. -/
@[expose] public def Style.weight? : Style → Option Weight
  | .bold => some .b
  | .medium => some .m
  | .series w => some w
  | .normal => some .m
  | _ => none

/-- The text alternative a non-text object declares (WCAG 2.2 SC 1.1.1;
ISO 32000-2 §14.9.3; the LaTeX Tagging Project's `alt=`/`artifact` keys).
Three states, never a string: an empty string cannot say whether nothing
was said or the object is decoration. -/
public inductive Alt where
  | undeclared
  | decorative
  | described (text : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The one site that builds a described alternative from text: blank text
is nothing said, so `alt=` and `alt={ }` stay `.undeclared`. -/
public def Alt.declare (s : String) : Alt :=
  if s.trimAscii.toString.isEmpty then .undeclared else .described s.trimAscii.toString

/-- The text a described alternative carries, `""` for the other two: what
a reader with only a string to fill (a link's reading, markdown) takes. -/
public def Alt.text : Alt → String
  | .described t => t
  | .undeclared | .decorative => ""

/-- An alternative as the IR dump spells it after its node: nothing when
undeclared, so a document that declares none dumps as it always did. -/
public def Alt.dumpSuffix : Alt → String
  | .undeclared => ""
  | .decorative => " artifact"
  | .described t => s!" alt {t.quote}"

/-- No described alternative reads as nothing: `declare` refuses blank
text. -/
public theorem Alt.declare_nonempty (s t : String) (h : Alt.declare s = .described t) :
    ¬ t.isEmpty := by
  unfold Alt.declare at h
  split at h
  · cases h
  · rename_i hne
    injection h with h
    subst h
    exact hne

/-- Is a step's content pending on page `k`: before its range starts, or
past its declared end (`\uncover<2>` covers on 1 and again from 3, exactly
as beamer's transparent covering does). Pending content dims; it is never
hidden. -/
@[expose] public def stepPending (n : Nat) (last : Option Nat) (k : Nat) : Bool :=
  k < n || (match last with | some u => k > u | none => false)

/-- A nonempty union of numbered intervals. The selector stores no content:
repeated or overlapping intervals never duplicate the body it selects.
`none` is an open end, not the frame's current last step. -/
public structure OverlaySpec where
  first : Nat
  last : Option Nat
  more : List (Nat × Option Nat) := []
  deriving Repr, BEq, DecidableEq, Inhabited

namespace OverlaySpec

@[expose] public def ranges (s : OverlaySpec) : List (Nat × Option Nat) :=
  (s.first, s.last) :: s.more

/-- Membership is disjunction, not the hull of the declared intervals. -/
@[expose] public def selects (s : OverlaySpec) (k : Nat) : Bool :=
  s.ranges.any fun (n, last) => !stepPending n last k

@[expose] public def pending (s : OverlaySpec) (k : Nat) : Bool := !s.selects k

/-- Alternation stores the step-one reading first, on either side of a union. -/
@[expose] public def showsFirst (s : OverlaySpec) (k : Nat) : Bool := s.pending k == s.pending 1

public def reachesOther (s : OverlaySpec) (steps : Nat) : Bool :=
  (List.range steps).any fun i => !s.showsFirst (i + 1)

/-- Interval order cannot change where a nested pause starts counting. -/
public def start (s : OverlaySpec) : Nat := s.more.foldl (fun n r => min n r.1) s.first

/-- Explicit numbered endpoints determine the frame's extent; an open end
extends through that extent without inventing an extra page. -/
public def maxStep (s : OverlaySpec) : Nat :=
  s.more.foldl (fun n r => max n (max r.1 (r.2.getD r.1)))
    (max s.first (s.last.getD s.first))

public def union (s t : OverlaySpec) : OverlaySpec := { s with more := s.more ++ t.ranges }

/-- Enumerate the frame, not the selector's intervals: a numbered step
appears once even when several intervals select it. -/
public def numberedSteps (steps : Nat) (p : Nat → Bool) : List Nat :=
  ((List.range steps).map (· + 1)).filter p

public def selectedSteps (s : OverlaySpec) (steps : Nat) : List Nat :=
  numberedSteps steps s.selects

/-- The finite projection of either arm in page-order storage. Visibility,
replacement and conditional styling share these same numbered steps. -/
public def pageSteps (s : OverlaySpec) (steps : Nat) (first : Bool) : List Nat :=
  numberedSteps steps fun k => s.showsFirst k == first

public theorem selects_exact (s : OverlaySpec) (k : Nat) :
    s.selects k = true ↔ ∃ r ∈ s.ranges, stepPending r.1 r.2 k = false := by
  simp [selects]

public theorem union_selects_exact (s t : OverlaySpec) (k : Nat) :
    (s.union t).selects k = (s.selects k || t.selects k) := by
  simp [selects, union, ranges, List.any_append, Bool.or_assoc]

public theorem union_self_id (s : OverlaySpec) (k : Nat) :
    (s.union s).selects k = s.selects k := by
  simp [union_selects_exact]

public theorem union_comm_agree (s t : OverlaySpec) (k : Nat) :
    (s.union t).selects k = (t.union s).selects k := by
  simp [union_selects_exact, Bool.or_comm]

/-- Nested covering is conjunction of selection, regardless of which
operations carry the selectors. A covered ancestor stays covered. -/
public theorem pending_nested_exact (s t : OverlaySpec) (k : Nat) :
    (s.pending k || t.pending k) = !(s.selects k && t.selects k) := by
  simp [pending, Bool.not_and]

@[simp] public theorem singleton_pending_exact (n : Nat) (last : Option Nat) (k : Nat) :
    (OverlaySpec.mk n last []).pending k = stepPending n last k := by
  simp [pending, selects, ranges]

public theorem showsFirst_id (s : OverlaySpec) : s.showsFirst 1 = true := by
  simp [showsFirst]

/-- Store alternatives in first-page order, regardless of which side of
an exact selector contains step one. Every alternation constructor uses
this bridge from the author's active/otherwise order to artifact order. -/
public def pageOrder {α : Type} (s : OverlaySpec) (active otherwise : α) : α × α :=
  if s.pending 1 then (otherwise, active) else (active, otherwise)

/-- Selecting from page-order storage recovers the author's chosen arm at
every step, for any payload and any union of numbered intervals. -/
public theorem pageOrder_select_exact {α : Type} (s : OverlaySpec) (k : Nat)
    (active otherwise : α) :
    (if s.showsFirst k then (s.pageOrder active otherwise).1
      else (s.pageOrder active otherwise).2) =
      (if s.selects k then active else otherwise) := by
  by_cases hk : s.selects k = true <;> by_cases hfirst : s.selects 1 = true <;>
    simp_all [pageOrder, showsFirst, pending]

/-- No numbered page is lost or added by a finite artifact projection. -/
public theorem numberedSteps_mem (steps k : Nat) (p : Nat → Bool) :
    k ∈ numberedSteps steps p ↔ 1 ≤ k ∧ k ≤ steps ∧ p k = true := by
  simp only [numberedSteps, List.mem_filter, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hs⟩
    exact ⟨by omega, by omega, hs⟩
  · rintro ⟨h1, h2, hs⟩
    exact ⟨⟨k - 1, by omega, by omega⟩, hs⟩

public theorem numberedSteps_contract (steps : Nat) (p : Nat → Bool) :
    (numberedSteps steps p).Nodup := by
  apply List.Pairwise.filter
  apply List.Pairwise.map (R := fun a b : Nat => a ≠ b) (fun n : Nat => n + 1)
  · intro a b h
    omega
  · exact List.nodup_range

public theorem selectedSteps_mem (s : OverlaySpec) (steps k : Nat) :
    k ∈ s.selectedSteps steps ↔ 1 ≤ k ∧ k ≤ steps ∧ s.selects k = true :=
  numberedSteps_mem steps k s.selects

public theorem pageSteps_mem (s : OverlaySpec) (steps k : Nat) (first : Bool) :
    k ∈ s.pageSteps steps first ↔
      1 ≤ k ∧ k ≤ steps ∧ s.showsFirst k = first := by
  simp [pageSteps, numberedSteps_mem]

/-- Exactly one arm reaches each numbered page. This is independent of
the arms' payload, so it also covers nested or newly added modifiers. -/
public theorem pageSteps_partition_contract (s : OverlaySpec) (steps k : Nat)
    (hk : 1 ≤ k) (hsteps : k ≤ steps) :
    ((s.pageSteps steps true).contains k || (s.pageSteps steps false).contains k) = true ∧
    ((s.pageSteps steps true).contains k && (s.pageSteps steps false).contains k) = false := by
  simp only [List.contains_eq_mem, pageSteps_mem, hk, hsteps, true_and]
  cases s.showsFirst k <;> decide

end OverlaySpec

public inductive Decoration where
  | underline
  | lineThrough
  deriving Repr, BEq, DecidableEq, Inhabited

public inductive Inline where
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
  /-- Diagnostic provenance only. Every semantic reading traverses `body`
  unchanged; the span neither styles content nor adds a semantic leaf.
  Source-free compilation removes this wrapper with `eraseLocations`. -/
  | located (span : Span) (body : Array Inline)
  /-- An authored role: the expansion of a document-defined command with at
  least one parameter (`\muted{...}` under `\define \muted(word: content)`),
  wrapped so the name survives into the artifact as an addressable
  annotation — the class hook. A 0-ary definition is a spelling, not a
  classifier of an argument, and is not wrapped. Layout and the PDF page
  are transparent to it (`role_transparent_layout`): the annotation is
  HTML's, until tagged PDF gives it a structure element to ride. -/
  | role (name : String) (body : Array Inline)
  /-- `\href{url}{body}`: a hyperlink. Becomes an `<a>` in HTML and a Link
  annotation in PDF, so the URL rides the IR rather than a backend. -/
  | link (url : String) (body : Array Inline)
  /-- `\label{key}`: the anchor a cross-reference lands on. Elaboration
  binds it to the nearest preceding numbered thing in flow order (a
  heading, a captioned float, a numbered equation) and records the binding
  in the label table; the node itself ships no ink — HTML emits an empty
  anchor element whose id is `labelAnchor key`, every other consumer passes
  it through. -/
  | label (key : String)
  /-- `\ref{key}` / `\eqref{key}` / cleveref's family: a cross-reference.
  Elaboration emits it unresolved — `text = "??"`, LaTeX's own spelling,
  `target = none` — and `resolveRefs` fills the text and the anchor once
  the whole document's labels are known, so backends only render: PDF sets
  `text`, HTML links it to `target`. `form` is what resolution renders
  (`refText`): the bare number, `\eqref`'s parentheses, or a cleveref
  form carrying the target kind's locale name. -/
  | ref (key : String) (form : RefForm) (text : String) (target : Option String)
  /-- A drawn text decoration. Geometry is resolved from the active face by
  layout; backends preserve the typed kind rather than inferring it from a
  generic rule. -/
  | decorated (kind : Decoration) (body : Array Inline)
  /-- `\hfill`: stretch that pushes what follows to the far margin. -/
  | fill
  /-- `\hspace{...}`: affine horizontal glue; the starred form survives a
  line break. -/
  | hspace (glue : Affine Measure) (keep : Bool)
  /-- `\rule[raise]{width}{height}`: a painted inline rectangle. -/
  | rule (width height raise : Affine Measure)
  /-- Running-content placeholders, resolved once page count is known. -/
  | pageNumber
  | pageCount
  /-- `\\`, carrying LaTeX's optional extra space: `\\[1ex]`. -/
  | linebreak (extra : SymGlue)
  /-- A strut, LaTeX's `\rule{\z@}{h}`: a zero-width prop that makes its
  line's box at least `h` tall above the baseline. It ships no ink and no
  text — layout raises the line, the other backends keep an empty carrier —
  so it owes no census fact. The author line of a styled title block
  carries one (`ElementStyle.authorStrut`). -/
  | strut (height : SymGlue)
  /-- TeX's italic correction, `\/`: a kern as wide as the italic
  correction of the word glyph before it (zero in an upright face), which
  also parts that glyph from a space's pair kern. `maybe` is ltfntcmd's
  `\maybe@ic`, what a text-font command sets at the edges of its argument
  (`\check@icl`, `\check@icr`): the correction is made only where the face
  in force is upright, and it lifts a space the glyph was followed by. It
  ships no ink and no text. -/
  | italicCorr (maybe : Bool)
  /-- Overlay content crisp exactly on the selector's steps (`\uncover<2>`,
  `<2->`, `<2-3>`, `<1,4>`): outside the union it dims, never hides, so no
  step reflows the slide (PLAN M5). Zero metric impact — a pure grouping
  both backends may recolor or tag. -/
  | onSteps (spec : OverlaySpec) (body : Array Inline)
  /-- Overlay *alternation* (`\alt<2>{a}{b}`): exactly one of the two groups
  is inked per step page. The declared exception to dim-not-hide (PLAN M5):
  dimming is a quieter version of the truth for `step`, but two
  alternatives dimmed side by side are a *different* page, and one a reader
  reads as content — `\alt<2>{apple}{banana}` rendered "applebanana". Nor
  can a pair of `step` nodes carry it: the complement of a mid-deck range
  is two ranges, so a pair also showed nothing at all past the range's end.

  The groups are stored in PAGE order, not spec order: `firstPage` is what
  step 1 ships and `otherPage` what the steps on the far side of the spec
  ship, so `\alt<2>{a}{b}` stores `b` first. Elaboration decides the order
  once, where the spec is parsed, and every walk after it reads both groups
  left to right — which is why the text census, the PDF structure tree and
  the pages agree with no walk testing the range. Spec order put the tree's
  reading order backwards from the handout's: page 1's ink landed under a
  leaf whose census was the other alternative, and the second leaf was
  named by no page at all.

  Consequences, both real and both paid here: an `alt` frame's step pages
  differ in content, so they do not share a text census the way `step`
  pages do, and the line reflows between steps when the groups differ in
  width — which is what replacement means. The document-level
  census carries both alternatives (`plainTextOne`), the page's carries
  the one the step inks (`OverlaySpec.showsFirst`, read by the layout walk beside the
  dim walk — dimming recolours and never selects, so `dimInline_text` stays
  true). -/
  | altSteps (spec : OverlaySpec) (firstPage : Array Inline)
      (otherPage : Array Inline)
  /-- An external image (`\includegraphics`, and what a `figure` or a deck
  logo reduces to): a box of raster content. `src` is the path as written —
  the file itself is the driver's effect, surfaced through `imageRefs` and
  fulfilled as an `Image.Store` — and `alt` is the text alternative the
  author declared (`alt={...}`, `artifact`, or a figure's caption filled in
  by `setAltBlocks`), the one value both backends project. -/
  | image (src : String) (size : Image.Spec) (alt : Alt)
  /-- An icon (`\faGithub`, `\faIcon{arrow-up}` — the spellings the
  fontawesome5 package defines): one glyph in an icon face, resolved like
  any other scalar through the per-scalar fallback chain, so a document
  that ships or installs the icon font renders it and one that does not
  gets the coverage diagnostic naming the scalar. `label` is the required
  text alternative (WCAG 2.2 SC 1.1.1): icon glyphs live in the Private
  Use Area, which assistive technology cannot read, so an icon without a
  text alternative is unrepresentable by construction. HTML hides the
  glyph from AT and carries the label as the accessible name; the
  markdown twin renders the label itself. -/
  | icon (scalar : Char) (label : String)
  /-- A citation (`\cite`, natbib's `\citep`/`\citet` and their family): the
  keys of one citation group, as written, and the form it was written in.
  Elaboration emits it unresolved — the `.bib` file is the driver's effect —
  and resolution (`Bib.apply`) *replaces* the node with the bibliography's
  own inlines: marks linked to their entries, brackets and separators per
  the document's natbib punctuation, so no backend ever reads a citation
  form. A node a backend still sees is one no bibliography resolved; it
  renders `citeMark` per key, LaTeX's own spelling for an undefined
  citation, and W0351 or the missing-file diagnostic has already said
  why. -/
  | cite (form : CiteForm) (keys : Array String)
  /-- `\footnote{...}`: a note set at the foot of the page its mark lands
  on. `num` is the resolved mark number — elaboration assigns it in flow
  order through `footnoteMark` (`\footnote[n]` overrides without stepping
  the counter, LaTeX's own semantics; `footnote_numbers_gapless` is the
  numbering contract). The body is inline content only: a paragraph break
  inside a note is set as a space, named (W0371) — a block body would put
  an Inline→Block edge into the elaboration termination knot and grow
  every Inline-only walk a Block companion. The body is document text and
  survives every walk (`footnoteWrap_text`); the mark digit is generated ink,
  excluded from the census as `citeMark` is. -/
  | footnote (num : Option Nat) (body : Array Inline)
  deriving Repr, BEq, Inhabited

/-- Single-interval construction; union nodes use `onSteps` directly. -/
@[match_pattern, expose] public def Inline.step (n : Nat) (last : Option Nat) (body : Array Inline) : Inline :=
  .onSteps ⟨n, last, []⟩ body

/-- Single-interval alternation, with the same page-order storage. -/
@[match_pattern, expose] public def Inline.alt (n : Nat) (last : Option Nat)
    (firstPage otherPage : Array Inline) : Inline :=
  .altSteps ⟨n, last, []⟩ firstPage otherPage


/-- An alternation in source order; the shared page-order bridge is the
only place its active and otherwise arms change positions. -/
public def Inline.alternate (spec : OverlaySpec) (active otherwise : Array Inline) : Inline :=
  let (firstPage, otherPage) := spec.pageOrder active otherwise
  .altSteps spec firstPage otherPage

/-- Which edges of a text-font command get an italic correction, factored
over the surface token predicates so prose and native picture labels read
the same ltfntcmd rule. -/
public def fontCmdEdges {α : Type} (isSpace isNocorr : α → Bool)
    (reads : Option α → Bool) (body : List α) (next? : Option α) : Bool × Bool :=
  match body.dropWhile isSpace with
  | [] => (false, false)
  | first :: rest => (!isNocorr first && reads body.head?,
      !rest.any isNocorr && reads next?)

/-- The inline sequence one text-font command contributes: its selected
face, the argument-side correction under that face, and the trailing
correction under the surrounding face. -/
@[expose] public def fontCmdInlines (style : Style) (edges : Bool × Bool)
    (inner : Array Inline) : Array Inline :=
  let run : Inline := .styled style (if edges.1 then #[.italicCorr true] ++ inner else inner)
  if edges.2 then #[run, .italicCorr true] else #[run]

/-- The anchor a reference-list entry carries in HTML and its citations
link to (`#` prefixed): one naming site, read by the resolver's link
construction and the backend's id emission, so the two cannot drift. -/
public def bibAnchor (key : String) : String := "ref-" ++ key

/-- What an unresolved citation shows for each key: LaTeX's rendering for
an undefined citation. The one definition site backends and census read. -/
public def citeMark : String := "?"

/-- The text an unresolved citation is worth: one mark per key, comma
separated — `\cite{a,b}` with no bibliography shows `?, ?`, one visible
gap per promised entry. -/
public def citeMarks (keys : Array String) : String :=
  String.intercalate ", " (keys.toList.map fun _ => citeMark)

/-- How far a footnote mark's baseline stands above its line's, per mille
of the surrounding size, the mark itself set at the `scriptsize` step of
`sizeScale`. The authority this constant stands in for is the face's own
OS/2 `ySuperscriptYOffset` (OpenType spec, OS/2 table): `Font` does not
parse it yet — it reads sCapHeight and sxHeight only — so one named value,
a third of an em, holds the raise until it does (PLAN § Owed obligations
records the parse). -/
public def markRaise : Nat := 333

/-- How a frame distributes its leftover vertical space: beamer's frame
options `[t]`/`[c]`/`[b]` on `\begin{frame}`. `center` is beamer's default
(user guide §8.1: the `c` option "is the default behavior"). `golden` is
the title page's declaration — beamer's centring composed with moloch's
golden-ratio glue (`golden_composes_center`) — and only `\maketitle`
produces it: a golden frame is the title page, whose content is display
furniture. -/
public inductive VAlign where
  | top
  | center
  | bottom
  | golden
  deriving Repr, BEq, Inhabited

/-- The fixed opening skip before a frame's body, separate from its
distributable space: beamerbaseframe.sty's title box ends with
`\vskip0.25em` (line 126), and `[t]` adds `.2cm` (line 263). Centred
frames add only fil glue (beamerinnerthememoloch.sty:455). Resolve the em
at the frame's body size, even when its first block has larger type.
PDF reads this on ordinary frame openings; HTML projects it on titled,
non-standout frames before distributing spare space. -/
public def frameBodySkip (hasTitle : Bool) (valign : VAlign) : Length :=
  { sp := if valign matches .top then Dim.mm 2 else 0
    em := if hasTitle then 250 else 0 }

/-- The title contributes one quarter of the body size; top alignment
contributes the fixed top skip. Neither depends on the first body's
construct, its paint padding, or how much flexible space remains. -/
public theorem frameBodySkip_exact (hasTitle : Bool) (valign : VAlign)
    (size : Sp) :
    (frameBodySkip hasTitle valign).resolve size 0 =
      (if hasTitle then size / 4 else 0) +
        (if valign matches .top then Dim.mm 2 else 0) := by
  have hquarter : 250 * size / 1000 = size / 4 :=
    Int.mul_ediv_mul_of_pos size 4 (by decide : (0 : Int) < 250)
  cases hasTitle <;> cases valign <;>
    simp [frameBodySkip, Length.resolve, hquarter, Int.add_comm]

/-- moloch's title-page template glue, in thousandths of a fil unit:
`\vspace{0pt plus 1.618fil}` and `\vfil` above the title matter against
`\vspace{0pt plus 1fil}` below it (beamerinnerthememoloch.dtx, the
"golden ratio spacing" of its `title page` template). The template's own
numbers, and *not* the page's distribution: the template sets its glue
inside a frame that contributes centring glue of its own, and the two
lists are one vertical list, so the units add (`golden_composes_center`).
-/
@[expose] public def titlePageTemplateGlue : Nat × Nat := (2618, 1000)

/-- A frame's own distribution composed with a template's glue, both
first-order fil in one vertical list: the units add, at the template's
thousandths. What a page-opening path's declared distribution is — a
template's ratio is never the page's on its own. -/
@[expose] public def composeGlue (frame template : Nat × Nat) : Nat × Nat :=
  (frame.1 * 1000 + template.1, frame.2 * 1000 + template.2)

/-- The shares of a page's leftover vertical space above and below its
content, per declared alignment: the ratio form of beamer's `\vfil`-glue
model — top-flush 0:1 (all leftover below), centring 1:1 (beamer user
guide §8.1: `c` is the default), bottom-flush 1:0, and the title page's
3618:2000 — beamer's centring composed with moloch's title-page glue
(`composeGlue`, `golden_composes_center`). The one table both artifacts
must honour: `Layout.VDist.of` projects it onto the PDF page,
`HtmlDoc.vdistShares` onto the deck's flex spacers, and
`vdist_shares_agree` in Tests states the agreement. -/
@[expose] public def VAlign.shares : VAlign → Nat × Nat
  | .top => (0, 1)
  | .center => (1, 1)
  | .bottom => (1, 0)
  | .golden => composeGlue (1, 1) titlePageTemplateGlue

/-- The title page's split is the enclosing frame's own centring composed
with the template's glue, never the template's numbers alone: a frame
contributes one fil unit on each side (`.center`) and moloch's template
1.618 + 1 above against 1 below, so the page distributes 3618:2000 —
above share 3618/5618. The decomposition is what makes the constant
sourced rather than fitted: both halves are independently sourced (the
frame's centring to beamer's user guide §8.1, the template's glue to
beamerinnerthememoloch.dtx), and reading the template alone is the defect
this states away — it put 2618/3618 of the leftover above and set the
title matter a visible band too low. -/
public theorem golden_composes_center :
    VAlign.golden.shares = composeGlue VAlign.center.shares titlePageTemplateGlue := by
  rfl

namespace Pic

/-- The two line widths the subset strokes: pgf manual §15.3.1 — `thin`,
0.4 pt, is every path's default, `thick` is 0.8 pt. Widths are graphic
state, not geometry: `scale=` never touches them, as in pgf. -/
public def thinWidth : Sp := Dim.pt 2 / 5
public def thickWidth : Sp := Dim.pt 4 / 5

/-- A dash pattern by name; the backends emit the sourced rhythms — pgf
manual §15.3.2: `dashed` is on 3 pt off 3 pt, `dotted` on the line width
off 1 pt (the `densely dotted` rhythm; the subset keeps one dotted form). -/
public inductive Dash where
  | solid
  | dashed
  | dotted
  deriving Repr, BEq, Inhabited

/-- How a border or an edge strokes: colour, width, dash. -/
public structure Stroke where
  color : Color := Color.black
  width : Sp := thinWidth
  dash : Dash := .solid
  deriving Repr, BEq, Inhabited

/-- One segment of a stroked edge, endpoints spelled explicitly (no
current-point state): a straight line, or a cubic Bézier with its two
control points. -/
public inductive PathSeg where
  | line (x1 y1 x2 y2 : Sp)
  | cubic (x1 y1 c1x c1y c2x c2y x2 y2 : Sp)
  deriving Repr, BEq, Inhabited

/-- The declared box of a segment. A cubic lies in the convex hull of its
four control points (de Casteljau), so the join of their boxes bounds
the drawn curve. -/
public def PathSeg.box : PathSeg → (Sp × Sp) × (Sp × Sp)
  | .line x1 y1 x2 y2 => ((min x1 x2, min y1 y2), (max x1 x2, max y1 y2))
  | .cubic x1 y1 c1x c1y c2x c2y x2 y2 =>
    ((min (min x1 c1x) (min c2x x2), min (min y1 c1y) (min c2y y2)),
     (max (max x1 c1x) (max c2x x2), max (max y1 c1y) (max c2y y2)))

/-- An arrow tip as three concrete corner points: a filled triangle
standing in for pgf's curved `latex` tip (a stated approximation — the
extents match pgflibraryarrows' declaration, apex 9 units ahead and back
corners 3 behind at ±3.75, unit 0.28pt + 0.3·line width; the curved
sides do not). Elaboration precomputes the points so neither backend
does geometry. -/
public structure Tip where
  x1 : Sp
  y1 : Sp
  x2 : Sp
  y2 : Sp
  x3 : Sp
  y3 : Sp
  deriving Repr, BEq, Inhabited

/-- Where a label stands relative to its point: TikZ's default anchors
the node's centre there; the placement options put the named side of the
label against the point (pgf manual §17.5.2 — `right` is `anchor=west`,
the label standing right of the point, and so around). -/
public inductive LabelAlign where
  | center
  /-- `right`: the label's west edge on the point. -/
  | west
  /-- `left`. -/
  | east
  /-- `above`: the label's south edge on the point. -/
  | south
  /-- `below`. -/
  | north
  deriving Repr, BEq, Inhabited

/-- The dump spelling of a shape's paint, for the IR goldens. -/
public def paintDump (st : Option Stroke) (fl : Option Color) : String :=
  let stS := match st with
    | some k =>
      let d := match k.dash with
        | .solid => ""
        | .dashed => " dashed"
        | .dotted => " dotted"
      s!" stroke #{Color.hexByte k.color.r}{Color.hexByte k.color.g}\
{Color.hexByte k.color.b} {k.width.toPtString}{d}"
    | none => ""
  match fl with
  | some c => stS ++ s!" fill #{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}"
  | none => stS

/-- One shape of an elaborated picture, in picture coordinates: sp with y
growing upward, as TikZ has it. The elaborator evaluates everything before
the IR — loops unrolled, expressions reduced, colours resolved, `scale=`
applied — so a shape is concrete ink both backends place without reading
the surface again. -/
public inductive Shape where
  /-- A filled rectangle: `(x, y)` one corner, `(x + w, y + h)` the other. -/
  | rect (x y w h : Sp) (color : Color)
  /-- A text label whose box is centred on `(x, y)` — TikZ's default node
  anchor — at `scale` per mille of the body size. The body is inline
  content, so a node's `{$X$}` renders through the math layer exactly as
  it would in a paragraph. -/
  | label (x y : Sp) (content : Array Inline) (color : Color) (scale : Nat)
      (align : LabelAlign)
  /-- A node's circular outline: centre and radius, stroked and/or
  filled. The radius is the declared minimum's half — pgf manual
  §"Shapes" has extent = max(minimum, text + 2·inner sep) per axis, and
  the minimum is the whole answer when it dominates the body, the case
  this subset renders; a larger body stands proud of its border. -/
  | circle (x y r : Sp) (stroke : Option Stroke) (fill : Option Color)
  /-- A node's rectangular outline: `(x, y)` the min corner, `w × h` the
  extents (non-negative by construction), sized like `circle` from the
  declared minimums. -/
  | frame (x y w h : Sp) (stroke : Option Stroke) (fill : Option Color)
  /-- A stroked edge (`\draw (a) -- (b)`): segments in order, optionally
  ending in an arrow tip filled in the stroke's colour. Endpoints are
  concrete — border anchoring already happened at elaboration. -/
  | edge (segs : Array PathSeg) (stroke : Stroke) (tip : Option Tip)
  deriving Repr, BEq, Inhabited

/-- Repaint a shape, keeping its geometry and text: how a picture dims
under an overlay cover. -/
public def Shape.recolor (f : Color → Color) : Shape → Shape
  | .rect x y w h c => .rect x y w h (f c)
  | .label x y t c sc al => .label x y t (f c) sc al
  | .circle x y r st fl =>
    .circle x y r (st.map fun s => { s with color := f s.color }) (fl.map f)
  | .frame x y w h st fl =>
    .frame x y w h (st.map fun s => { s with color := f s.color }) (fl.map f)
  | .edge segs st tip => .edge segs { st with color := f st.color } tip

/-- A box in picture coordinates: min corner, then max corner. -/
public abbrev Box := (Sp × Sp) × (Sp × Sp)

/-- The join of two boxes: the smallest box holding both. -/
public def Box.join (a b : Box) : Box :=
  ((min a.1.1 b.1.1, min a.1.2 b.1.2), (max a.2.1 b.2.1, max a.2.2 b.2.2))

/-- `a` is inside `b`, componentwise. -/
@[expose] public def Box.le (a b : Box) : Prop :=
  b.1.1 ≤ a.1.1 ∧ b.1.2 ≤ a.1.2 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2

/-- Translate a measured interval beside an anchor. A positive direction
puts its lower edge one gap beyond the anchor; a negative direction puts
its upper edge one gap before it. A zero direction centres the interval.
The bounds name the attachment: text ink, advance, or a line box is the
caller's choice, never an incidental font descent. -/
public def Box.axisOffset (anchor lo hi gap direction : Sp) : Sp :=
  if 0 < direction then anchor + gap - lo
  else if direction < 0 then anchor - gap - hi
  else anchor - (lo + hi) / 2

/-- Exact clearance in either direction, and centring within one scaled
point when no direction is requested. Quantified over arbitrary bounds
and gaps: the two axes of a box instantiate the same constraint. -/
public theorem Box.axisOffset_contract (anchor lo hi gap direction : Int) :
    (0 < direction → lo + axisOffset anchor lo hi gap direction = anchor + gap) ∧
    (direction < 0 → hi + axisOffset anchor lo hi gap direction = anchor - gap) ∧
    (direction = 0 →
      2 * anchor ≤ lo + hi + 2 * axisOffset anchor lo hi gap direction ∧
      lo + hi + 2 * axisOffset anchor lo hi gap direction ≤ 2 * anchor + 1) := by
  by_cases hp : 0 < direction
  · simp only [axisOffset, ite_eq_left hp]
    omega
  · by_cases hn : direction < 0
    · simp only [axisOffset, ite_eq_right hp, ite_eq_left hn]
      omega
    · simp only [axisOffset, ite_eq_right hp, ite_eq_right hn]
      omega

/-- Attach a whole box, preserving its internal rhythm. Corner placement
applies the interval constraint to both axes; side placement centres the
unconstrained axis. The result is a translation, not a new measurement. -/
public def Box.attachOffset (box : Box) (anchor direction gap : Sp × Sp) : Sp × Sp :=
  (axisOffset anchor.1 box.1.1 box.2.1 gap.1 direction.1,
   axisOffset anchor.2 box.1.2 box.2.2 gap.2 direction.2)

/-- Both components of the actual attachment satisfy the interval
contract: the requested endpoint is placed exactly, or the doubled centre
is within one scaled point of the anchor's. Gaps remain signed; this is
placement, not a non-overlap claim about arbitrary bounds. -/
public theorem Box.attachOffset_contract (box : Box) (anchor direction gap : Sp × Sp) :
    let offset := attachOffset box anchor direction gap
    let onAxis (a lo hi g d shift : Int) : Prop :=
      (0 < d → lo + shift = a + g) ∧
      (d < 0 → hi + shift = a - g) ∧
      (d = 0 → 2 * a ≤ lo + hi + 2 * shift ∧ lo + hi + 2 * shift ≤ 2 * a + 1)
    onAxis anchor.1 box.1.1 box.2.1 gap.1 direction.1 offset.1 ∧
    onAxis anchor.2 box.1.2 box.2.2 gap.2 direction.2 offset.2 :=
  ⟨axisOffset_contract anchor.1 box.1.1 box.2.1 gap.1 direction.1,
   axisOffset_contract anchor.2 box.1.2 box.2.2 gap.2 direction.2⟩

/-- A label line's measured ink: the width it sets to, and how far its
glyphs reach above and below its baseline. A font question, so it is a
value the measuring side supplies rather than something a shape can
answer — see `LabelMetric`. -/
public structure LabelInk where
  w : Sp := 0
  height : Sp := 0
  depth : Sp := 0
  /-- How far the glyphs themselves reach above and below the baseline: the
  TeX box the text makes (pgf's text box), which a node's border holds. The
  band above places the letters and reads no glyph; this is their reach. -/
  boxHeight : Sp := 0
  boxDepth : Sp := 0
  /-- The face's x-height at the label's size: what `ex` means in a node's
  options, as TeX reads it (fontdimen 5). -/
  ex : Sp := 0
  deriving Repr, BEq, Inhabited

/-- What a label's content sets to at a per-mille size: the measurement
the box of a label needs and the IR cannot make.

**The picture walk has no face, and cannot be given one.** The driver
builds the font set *from* the elaborated document (`\fonts` is a preamble
declaration), so at the moment a node is placed there is nothing to
measure against; only layout, which receives the resolved set, can answer.
So the extent enters as a function here and every statement about it is
universally quantified over the measurement — the box facts hold whatever
the face turns out to be, and each artifact's version is that one fact
projected through the metric it can supply. -/
public abbrev LabelMetric := Array Inline → Nat → LabelInk

/-- Where a label's ink stands around its anchor, given its extents: the
anchor decides which point of the box sits on `(x, y)` (pgf manual §17.5.2
— the `anchor=` key), and this is the one site that says so. Layout sets
each label line by reading it and the bounding box bounds the ink by
reading it, so the box a picture reserves and the box its ink lands in
cannot drift apart. Written arm by arm rather than as offsets, so each
anchor's box reads off the page. -/
private def labelInkSpan (x y : Sp) (align : LabelAlign) (w tall : Sp) : Box :=
  match align with
  | .center => ((x - w / 2, y - tall / 2), (x - w / 2 + w, y - tall / 2 + tall))
  | .west => ((x, y - tall / 2), (x + w, y - tall / 2 + tall))
  | .east => ((x - w, y - tall / 2), (x, y - tall / 2 + tall))
  | .south => ((x - w / 2, y), (x - w / 2 + w, y + tall))
  | .north => ((x - w / 2, y - tall), (x - w / 2 + w, y))

/-- The anchor is inside the ink: a measured box always holds the point it
hangs from, so widening a label from its anchor to its ink can only grow a
hull. The arithmetic is spelled over bare `Int` binders because `omega`
does not read a `Sp`-typed term — the same workaround the `Box` proofs
below record. -/
private theorem labelInkSpan_covers_anchor (x y : Sp) (align : LabelAlign) (w tall : Sp)
    (hw : 0 ≤ w) (ht : 0 ≤ tall) :
    Box.le ((x, y), (x, y)) (labelInkSpan x y align w tall) := by
  have half : ∀ a b : Int, 0 ≤ b → a - b / 2 ≤ a ∧ a ≤ a - b / 2 + b := by
    intro a b h; omega
  have full : ∀ a b : Int, 0 ≤ b → a - b ≤ a := by intro a b h; omega
  have grow : ∀ a b : Int, 0 ≤ b → a ≤ a + b := by intro a b h; omega
  cases align
  · exact ⟨(half x w hw).1, (half y tall ht).1, (half x w hw).2, (half y tall ht).2⟩
  · exact ⟨Int.le_refl x, (half y tall ht).1, grow x w hw, (half y tall ht).2⟩
  · exact ⟨full x w hw, (half y tall ht).1, Int.le_refl x, (half y tall ht).2⟩
  · exact ⟨(half x w hw).1, Int.le_refl y, (half x w hw).2, grow y tall ht⟩
  · exact ⟨(half x w hw).1, full y tall ht, (half x w hw).2, Int.le_refl y⟩

/-- Where a label's measured ink stands around its anchor. Negative
extents are clamped away: a metric that answers nonsense may not shrink
the box below the anchor the shape declares. -/
public def labelInkBox (x y : Sp) (align : LabelAlign) (m : LabelInk) : Box :=
  labelInkSpan x y align (max m.w 0) (max (m.height + m.depth) 0)

/-- **Where a label's baseline sits.** The top of its ink box less its
height — the line placement's own arithmetic, read off one site so the box a
picture reserves and the baseline a line is set on cannot disagree.

This is the number the wobble is about. Under TeX's node centring the
baseline is `−(ht − dp)/2` of the *measured* box, so depth enters with
slope ½ and a word with a descender floats up: 1.155 pt between `candle`
and `misty` in Latin Modern at 10 pt (pgf manual §17.5.1 calls it
"wobbles" and offers `anchor=mid` against it). Here `height` and `depth`
are the face's declared cap height and descent at the run's size, never the
glyphs present (`Layout.label_centre_glyph_free`), so the same arithmetic
is content-blind and the wobble is zero. The reference that remains is a
declared choice, not an accident: the band is cap-to-descent rather than
cap-to-baseline, which seats every label `depth/2` above where trimming to
the alphabetic baseline would (css-inline-3 §6's `text-box-trim`);
`labelBaseline_between` is where that offset is quantified. -/
public def labelBaseline (y : Sp) (align : LabelAlign) (m : LabelInk) : Sp :=
  (labelInkBox 0 y align m).2.2 - m.height

/-- The baseline is the box's, at whatever x the box was measured at: the
placement reads `box top − height` and this says that expression is
`labelBaseline`, so neither can drift from the other without failing here.
Spelled over bare `Int` binders per arm because `omega` does not read an
`Sp`-typed goal — the workaround `labelInkSpan_covers_anchor` records. -/
public theorem labelBaseline_box_exact (x y : Sp) (align : LabelAlign) (m : LabelInk) :
    labelBaseline y align m = (labelInkBox x y align m).2.2 - m.height := by
  cases align <;> rfl

/-- The text's measured TeX box on its resolved baseline, without adding
the anchor or the font band to its vertical extent. Attachments read this
box so a descender, a second line, or a font change cannot eat their gap. -/
public def labelTextBox (x y : Sp) (align : LabelAlign) (m : LabelInk) : Box :=
  let band := labelInkBox x y align m
  let b := labelBaseline y align m
  ((band.1.1, b - m.boxDepth), (band.2.1, b + m.boxHeight))

/-- Translating a label's coordinates translates its whole measured text
box exactly. The shared baseline and ink-box arithmetic commute with the
same offset for every alignment and metric, including rounded dimensions. -/
public theorem labelTextBox_translate_exact (x y : Sp) (align : LabelAlign) (m : LabelInk)
    (offset : Sp × Sp) :
    let box := labelTextBox x y align m
    labelTextBox (x + offset.1) (y + offset.2) align m =
      ((box.1.1 + offset.1, box.1.2 + offset.2),
       (box.2.1 + offset.1, box.2.2 + offset.2)) := by
  cases align <;>
    simp [labelTextBox, labelBaseline, labelInkBox, labelInkSpan,
      Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_comm, Int.add_comm]

/-- **Where a label's glyphs stand**: the TeX box its text makes, on the
baseline the band places — the band's width, and the glyphs' own reach above
and below that baseline (`LabelInk.boxHeight`/`boxDepth`) — held to cover the
anchor it hangs from. This, not the band, is the ink a picture's box holds:
the band is a placement reference, deeper than a word with no descender
sets anything, and pgf's natural box holds a node's text box, not its
font's. -/
@[expose] public def labelGlyphBox (x y : Sp) (align : LabelAlign) (m : LabelInk) : Box :=
  let box := labelTextBox x y align m
  ((box.1.1, min y box.1.2), (box.2.1, max y box.2.2))

/-- The anchor is inside the glyphs' box, as it is inside the band
(`labelInkSpan_covers_anchor`): widening a label from its anchor to its
glyphs can only grow a hull. -/
public theorem labelGlyphBox_covers (x y : Sp) (align : LabelAlign) (m : LabelInk) :
    Box.le ((x, y), (x, y)) (labelGlyphBox x y align m) := by
  have hx := labelInkSpan_covers_anchor x y align (max m.w 0) (max (m.height + m.depth) 0)
    (Int.le_max_right _ _) (Int.le_max_right _ _)
  have lo : ∀ a b : Int, min a b ≤ a := by intro a b; omega
  have hi : ∀ a b : Int, a ≤ max a b := by intro a b; omega
  exact ⟨hx.1, lo _ _, hx.2.2.1, hi _ _⟩

/-- Every measured vertical extent held by the label's metrics remains
inside its glyph box on the resolved baseline. Taking the hull with the
anchor can only enlarge that box, for every alignment. -/
public theorem labelGlyphBox_covers_extent (x y : Sp) (align : LabelAlign) (m : LabelInk)
    (hi lo : Sp) (hhi : hi ≤ m.boxHeight) (hlo : lo ≤ m.boxDepth) :
    (labelGlyphBox x y align m).1.2 ≤ labelBaseline y align m - lo ∧
    labelBaseline y align m + hi ≤ (labelGlyphBox x y align m).2.2 := by
  simp only [labelGlyphBox, labelTextBox]
  have bottom := Int.min_le_right y (labelBaseline y align m - m.boxDepth)
  have top := Int.le_max_right y (labelBaseline y align m + m.boxHeight)
  exact ⟨Int.le_trans bottom (Int.sub_le_sub_left hlo _),
    Int.le_trans (Int.add_le_add_left hhi _) top⟩

/-- **A label's baseline does not read its set width.** So the advances of
the glyphs it sets — which face, which kerning, which characters — cannot
move it vertically: the horizontal measurement and the vertical placement
are separate channels, and only the first is a function of the text. The
companion half, that `height` and `depth` are declared metrics rather than
ink, is `Layout.label_centre_glyph_free`. -/
public theorem labelBaseline_width_id (y w : Sp) (align : LabelAlign) (m : LabelInk) :
    labelBaseline y align { m with w := w } = labelBaseline y align m := by
  cases align <;> rfl

/-- **The uniform seat, quantified.** A centred label's baseline stands
`(depth − height)/2` from its anchor, to within the single scaled point the
box's odd unit is assigned by (1 sp = 1/65536 pt). No glyph term appears, so
this is the *whole* vertical story for a centred label: one number per
(face, size).

Read the other way it is the cost of the cap-to-descent band: against a
band trimmed to the alphabetic baseline the label sits `depth/2` higher —
1.67 pt at 10 pt in Source Serif Pro, 1.46 in Open Sans, 1.32 in Fira Sans.
Uniform, therefore not a wobble; a reference choice, and the one deliberate
difference from css-inline-3 §6's `text-box-edge: cap alphabetic`. -/
public theorem labelBaseline_between (y : Sp) (m : LabelInk)
    (h : 0 ≤ m.height + m.depth) :
    y + (m.depth - m.height) / 2 ≤ labelBaseline y .center m ∧
      labelBaseline y .center m ≤ y + (m.depth - m.height) / 2 + 1 := by
  show y + (m.depth - m.height) / 2
        ≤ y - (max (m.height + m.depth) 0) / 2 + max (m.height + m.depth) 0 - m.height ∧
      y - (max (m.height + m.depth) 0) / 2 + max (m.height + m.depth) 0 - m.height
        ≤ y + (m.depth - m.height) / 2 + 1
  have step : ∀ a b c : Int, 0 ≤ b + c →
      a + (c - b) / 2 ≤ a - (max (b + c) 0) / 2 + max (b + c) 0 - b ∧
      a - (max (b + c) 0) / 2 + max (b + c) 0 - b ≤ a + (c - b) / 2 + 1 := by
    intro a b c hbc; omega
  exact step y m.height m.depth h

/-- The componentwise join of two measurements: what a line carrying both
would set to. A metric-only run — a phantom, whose box is its argument's
and whose ink is nothing — enters exactly here, and `max` is why it can be
inert. -/
public def LabelInk.join (a b : LabelInk) : LabelInk :=
  { w := max a.w b.w, height := max a.height b.height, depth := max a.depth b.depth
    boxHeight := max a.boxHeight b.boxHeight, boxDepth := max a.boxDepth b.boxDepth
    ex := max a.ex b.ex }

/-- **The one surviving channel, bounded — and shut where it matters.** A
label carrying an extra metric box sets between what it set alone and the
join of the two: the phantom can grow the band, never shrink it. And where
the phantom's metrics are already covered by the label's own — which is what
a `\vphantom{y}` written beside a descender-less word *is*, the argument set
in the running face at the running size — the join is the original box and
nothing moves at all.

This is the compatibility guarantee, and note it names no command: it is
idempotence of `max`, so every hand fix whose metrics the label already
declares is inert by construction rather than by a special case. The engine
is stricter still — a picture label's `\vphantom` group is dropped before it
reaches the IR (`Picture.phantomCtrl`), so not even a dominated box arrives —
but that is a surface decision, and this is the fact that holds whatever the
surface does. -/
public theorem phantom_extent_between (x y : Sp) (align : LabelAlign) (m p : LabelInk) :
    Box.le (labelInkBox x y align m) (labelInkBox x y align (m.join p)) ∧
      (p.w ≤ m.w → p.height ≤ m.height → p.depth ≤ m.depth →
        labelInkBox x y align (m.join p) = labelInkBox x y align m) := by
  refine ⟨?_, ?_⟩
  · have mid : ∀ v s t : Int, s ≤ t →
        v - t / 2 ≤ v - s / 2 ∧ v - s / 2 + s ≤ v - t / 2 + t := by
      intro v s t h; omega
    have near : ∀ v s t : Int, s ≤ t → v ≤ v ∧ v + s ≤ v + t := by
      intro v s t h; omega
    have far : ∀ v s t : Int, s ≤ t → v - t ≤ v - s ∧ v ≤ v := by
      intro v s t h; omega
    have gw : max m.w 0 ≤ max (m.join p).w 0 := by
      have jw : ∀ a b : Int, max a 0 ≤ max (max a b) 0 := by intro a b; omega
      exact jw m.w p.w
    have gt : max (m.height + m.depth) 0 ≤ max ((m.join p).height + (m.join p).depth) 0 := by
      have jt : ∀ a b c d : Int, max (a + c) 0 ≤ max (max a b + max c d) 0 := by
        intro a b c d; omega
      exact jt m.height p.height m.depth p.depth
    cases align
    · exact ⟨(mid x _ _ gw).1, (mid y _ _ gt).1, (mid x _ _ gw).2, (mid y _ _ gt).2⟩
    · exact ⟨(near x _ _ gw).1, (mid y _ _ gt).1, (near x _ _ gw).2, (mid y _ _ gt).2⟩
    · exact ⟨(far x _ _ gw).1, (mid y _ _ gt).1, (far x _ _ gw).2, (mid y _ _ gt).2⟩
    · exact ⟨(mid x _ _ gw).1, (near y _ _ gt).1, (mid x _ _ gw).2, (near y _ _ gt).2⟩
    · exact ⟨(mid x _ _ gw).1, (far y _ _ gt).1, (mid x _ _ gw).2, (far y _ _ gt).2⟩
  · intro hw hh hd
    have dom : ∀ a b : Int, b ≤ a → max a b = a := by intro a b h; omega
    have ew : (m.join p).w = m.w := dom m.w p.w hw
    have eh : (m.join p).height = m.height := dom m.height p.height hh
    have ed : (m.join p).depth = m.depth := dom m.depth p.depth hd
    unfold labelInkBox
    rw [ew, eh, ed]

/-- The declared box of a shape, corners sorted. A label's box is its
anchor point — its text extent is a font question layout answers, so
`Shape.inkBox` is the measured form and this is what the IR knows on its
own. A picture's declared box bounds every fill entirely and every label
at its anchor (`box_in_bbox`); the ink of a label stands proud of it,
which is what the measured box exists to close. -/
public def Shape.box : Shape → Box
  | .rect x y w h _ => ((min x (x + w), min y (y + h)), (max x (x + w), max y (y + h)))
  | .label x y _ _ _ _ => ((x, y), (x, y))
  | .circle x y r _ _ =>
    ((min (x - r) (x + r), min (y - r) (y + r)),
     (max (x - r) (x + r), max (y - r) (y + r)))
  | .frame x y w h _ _ =>
    ((min x (x + w), min y (y + h)), (max x (x + w), max y (y + h)))
  | .edge segs _ tip =>
    let base : Box := match tip with
      | some t => ((min t.x1 (min t.x2 t.x3), min t.y1 (min t.y2 t.y3)),
                   (max t.x1 (max t.x2 t.x3), max t.y1 (max t.y2 t.y3)))
      | none => match segs[0]? with
        | some s => s.box
        | none => ((0, 0), (0, 0))
    segs.foldl (fun acc s => Box.join acc s.box) base

public structure Picture where
  shapes : Array Shape := #[]
  /-- The box `\useasboundingbox` declared, corners sorted: the picture's
  size is this box whatever its marks do (pgf manual §15.8, "use as
  bounding box") — ink may stand outside it, and nothing is clipped. -/
  declared : Option Box := none
  /-- Every node's border — its text extent plus `inner sep` — drawn or
  not: pgf adds a node's shape to the natural bounding box whether or not
  the path paints it (§17.2.2), so a diagram of undrawn nodes is one inner
  sep larger on every side than its letters. -/
  borders : Array Box := #[]
  /-- The height the surrounding line's baseline passes through, in picture
  coordinates, when the picture declares one (`baseline=`, pgf manual
  §12.2.1: a length, a coordinate or a node anchor; the bare key is 0pt).
  Otherwise the box's bottom edge stands on the baseline. -/
  baseline : Option Sp := none
  /-- The alternative the author declared on the picture (`alt={...}` or
  `artifact` in its option list, latex-lab-tikz's keys); the one a reader
  gets is `alternative`, which falls back to the picture's own words. -/
  alt : Alt := .undeclared
  deriving Repr, BEq, Inhabited

public def Picture.recolor (p : Picture) (f : Color → Color) : Picture :=
  { p with shapes := p.shapes.map (·.recolor f) }

/-- The fill a shape paints at a point, when it holds the point: a filled
rectangle, a filled circle's disc, a filled frame's box. -/
public def Shape.fillAt (x y : Sp) : Shape → Option Color
  | .rect rx ry w h c =>
    if min rx (rx + w) ≤ x ∧ x ≤ max rx (rx + w) ∧ min ry (ry + h) ≤ y ∧ y ≤ max ry (ry + h)
    then some c else none
  | .circle cx cy r _ fl =>
    if (x - cx) * (x - cx) + (y - cy) * (y - cy) ≤ r * r then fl else none
  | .frame fx fy w h _ fl =>
    if fx ≤ x ∧ x ≤ fx + w ∧ fy ≤ y ∧ y ≤ fy + h then fl else none
  | .label _ _ _ _ _ _ => none
  | .edge _ _ _ => none

/-- The ground a label's ink stands on: the fill of the last shape drawn
before it that paints its anchor — a node's own fill sits under its
label — and `none` where the label stands on whatever the picture stands
on. -/
public def fillUnder (drawn : Array Shape) (x y : Sp) : Option Color :=
  drawn.foldl (fun g s => (s.fillAt x y).or g) none

/-- The inline content each label sets, for the font-scalar walk: every
glyph — text or math — a picture can ask a face for is here. -/
public def Picture.labelContents (p : Picture) : Array (Array Inline) :=
  p.shapes.filterMap fun s => match s with
    | .label _ _ content _ _ _ => some content
    | .rect _ _ _ _ _ => none
    | .circle _ _ _ _ _ => none
    | .frame _ _ _ _ _ _ => none
    | .edge _ _ _ => none

/-- A shape with its label content through `f`; geometry, colour and every
other shape stay. -/
@[expose] public def Shape.mapLabel (f : Array Inline → Array Inline) : Shape → Shape
  | .label x y content c scale align => .label x y (f content) c scale align
  | .rect x y w h c => .rect x y w h c
  | .circle x y r stroke fill => .circle x y r stroke fill
  | .frame x y w h stroke fill => .frame x y w h stroke fill
  | .edge segs stroke tip => .edge segs stroke tip

/-- Every label's content through one inline rewrite: the picture face of
the generic maps (`mapBlocksPic`), for a pass that must reach the text a
label paints as it reaches a caption's. -/
@[expose] public def Picture.mapLabels (f : Array Inline → Array Inline) (p : Picture) :
    Picture :=
  { p with shapes := p.shapes.map (·.mapLabel f) }

/-- A label rewrite rewrites exactly the label contents, in order. -/
private theorem Picture.labelContents_mapLabels (f : Array Inline → Array Inline)
    (p : Picture) : (p.mapLabels f).labelContents = p.labelContents.map f := by
  simp only [Picture.mapLabels, Picture.labelContents, Array.filterMap_map,
    Array.map_filterMap]
  congr 1
  funext s
  cases s <;> rfl

/-- Two label rewrites compose into one. -/
private theorem Picture.mapLabels_comp (f g : Array Inline → Array Inline) (p : Picture) :
    (p.mapLabels g).mapLabels f = p.mapLabels (f ∘ g) := by
  simp only [Picture.mapLabels, Array.map_map]
  congr 2
  funext s
  cases s <;> rfl

/-- The box a shape's **ink** occupies, given a measurement. Every arm but
the label's is the declared box: a fill, an outline and a stroked edge are
their own geometry, and only text has an extent the IR cannot compute — the
glyphs' own box on the baseline the band places (`labelGlyphBox`). -/
@[expose] public def Shape.inkBox (m : LabelMetric) : Shape → Box
  | .label x y content _ scale align => labelGlyphBox x y align (m content scale)
  | s@(.rect _ _ _ _ _) => s.box
  | s@(.circle _ _ _ _ _) => s.box
  | s@(.frame _ _ _ _ _ _) => s.box
  | s@(.edge _ _ _) => s.box

-- The Box and Place proofs state their arithmetic over bare `Int` binders
-- because `omega` does not see through the `Sp` abbreviation (the same
-- workaround `furnitureBand`'s proof records in Layout).

public theorem Box.le_refl (a : Box) : Box.le a a := by
  have h : ∀ x : Int, x ≤ x := fun _ => Int.le_refl _
  exact ⟨h _, h _, h _, h _⟩

public theorem Box.le_join_left (a b : Box) : Box.le a (Box.join a b) := by
  have hmin : ∀ x y : Int, min x y ≤ x := by intro x y; omega
  have hmax : ∀ x y : Int, x ≤ max x y := by intro x y; omega
  exact ⟨hmin _ _, hmin _ _, hmax _ _, hmax _ _⟩

public theorem Box.le_join_right (a b : Box) : Box.le b (Box.join a b) := by
  have hmin : ∀ x y : Int, min x y ≤ y := by intro x y; omega
  have hmax : ∀ x y : Int, y ≤ max x y := by intro x y; omega
  exact ⟨hmin _ _, hmin _ _, hmax _ _, hmax _ _⟩

public theorem Box.le_trans {a b c : Box} (h1 : Box.le a b) (h2 : Box.le b c) : Box.le a c := by
  have h : ∀ x y z : Int, x ≤ y → y ≤ z → x ≤ z := fun _ _ _ => Int.le_trans
  exact ⟨h _ _ _ h2.1 h1.1, h _ _ _ h2.2.1 h1.2.1,
         h _ _ _ h1.2.2.1 h2.2.2.1, h _ _ _ h1.2.2.2 h2.2.2.2⟩

/-- The half-extents a label of this width and height asks of the node it
hangs on: how far its ink reaches either side of the anchor, read off
`labelInkSpan` so this and the box a picture reserves cannot disagree about
where a label's ink stands. An anchored label is not symmetric about its
anchor — a `west` label puts its whole width to the right of it — so each
axis takes the larger reach, which is what a *centred* extent must cover. -/
public def labelHalfExtent (align : LabelAlign) (w tall : Sp) : Sp × Sp :=
  let ((x0, y0), (x1, y1)) := labelInkSpan 0 0 align w tall
  (max (-x0) x1, max (-y0) y1)

/-- The box a node of these half-extents occupies: the centred extent a
relative placement leaves `node distance` between, border to border. -/
@[expose] public def nodeExtentBox (x y a b : Sp) : Box := ((x - a, y - b), (x + a, y + b))

/-- A label's ink is inside the extent its own reach asks for. The
arithmetic is spelled over bare `Int` binders and applied, because `omega`
does not read an `Sp`-typed goal — the workaround `labelInkSpan_covers_anchor`
records, one lemma per anchor shape rather than one per anchor. -/
private theorem labelHalfExtent_covers (align : LabelAlign) (x y w tall : Sp) :
    Box.le (labelInkSpan x y align w tall)
      (nodeExtentBox x y (labelHalfExtent align w tall).1
        (labelHalfExtent align w tall).2) := by
  have mid : ∀ v d : Int,
      v - max (-(0 - d / 2)) (0 - d / 2 + d) ≤ v - d / 2 ∧
      v - d / 2 + d ≤ v + max (-(0 - d / 2)) (0 - d / 2 + d) := by
    intro v d; omega
  have near : ∀ v d : Int,
      v - max (-0) (0 + d) ≤ v ∧ v + d ≤ v + max (-0) (0 + d) := by
    intro v d; omega
  have far : ∀ v d : Int,
      v - max (-(0 - d)) 0 ≤ v - d ∧ v ≤ v + max (-(0 - d)) 0 := by
    intro v d; omega
  cases align
  · exact ⟨(mid x w).1, (mid y tall).1, (mid x w).2, (mid y tall).2⟩
  · exact ⟨(near x w).1, (mid y tall).1, (near x w).2, (mid y tall).2⟩
  · exact ⟨(far x w).1, (mid y tall).1, (far x w).2, (mid y tall).2⟩
  · exact ⟨(mid x w).1, (near y tall).1, (mid x w).2, (near y tall).2⟩
  · exact ⟨(mid x w).1, (far y tall).1, (mid x w).2, (far y tall).2⟩

/-- A wider extent covers more: what makes the declared minimum a floor
rather than an alternative to the measurement. -/
public theorem nodeExtentBox_monotone (x y a b a' b' : Sp) (ha : a ≤ a') (hb : b ≤ b') :
    Box.le (nodeExtentBox x y a b) (nodeExtentBox x y a' b') := by
  have step : ∀ v p q : Int, p ≤ q → v - q ≤ v - p ∧ v + p ≤ v + q := by
    intro v p q h; omega
  exact ⟨(step x a a' ha).1, (step y b b' hb).1, (step x a a' ha).2, (step y b b' hb).2⟩

/-- **The extent a node registers, given a measurement.** The half-extents
every relative placement measures border to border from: the declared
minimum, or the label's own reach where the text stands proud of it. The
minimum alone is what a walk with no face knows, and it is *zero* for a node
body that declared none — which is why `right =of` parted node centres and
long labels landed on top of one another.

One site, so the extent a node registers and the extent a placement reads
are the same number; `nodeExtent_covers` is the fact it exists for. -/
@[expose] public def nodeExtent (m : LabelMetric) (content : Array Inline) (scale : Nat)
    (align : LabelAlign) (declA declB : Sp) : Sp × Sp :=
  let ink := m content scale
  let (a, b) := labelHalfExtent align (max ink.w 0) (max (ink.height + ink.depth) 0)
  (max declA a, max declB b)

/-- **A node's registered extent covers its label's ink.** Whatever face
resolves — the statement is quantified over the measurement, as every box
fact here is — a label standing at a node's anchor is inside the extent that
node places against. This is what makes the exact border arithmetic
(`Picture.placeRight_border_exact` and its three siblings) exact about the
right box: two nodes one `node distance` apart by these borders part the
*text* they set by at least that much, so neither can overlap the other.

The declared minimum is a floor, never a ceiling (`nodeExtentBox_monotone`):
a node declaring more than its text keeps what it declared, which is the pgf
reading — extent = max(minimum, text extent), manual §"Shapes". -/
public theorem nodeExtent_covers (m : LabelMetric) (content : Array Inline) (scale : Nat)
    (align : LabelAlign) (declA declB x y : Sp) :
    Box.le (labelInkBox x y align (m content scale))
      (nodeExtentBox x y (nodeExtent m content scale align declA declB).1
        (nodeExtent m content scale align declA declB).2) := by
  have grow : ∀ p q : Int, p ≤ max q p := by intro p q; omega
  exact Box.le_trans (labelHalfExtent_covers align x y _ _)
    (nodeExtentBox_monotone x y _ _ _ _ (grow _ declA) (grow _ declB))

/-- **Growth moves the border, never the letters.** Enlarging what a node
declares — `minimum width`, `minimum height` — grows the box every relative
placement measures from, and leaves every baseline on the page exactly where
it was. The two halves are stated together because the guarantee is the
pair: the extent is monotone in what was declared
(`nodeExtentBox_monotone` through `nodeExtent`), and the label's placement
does not read the declaration at all.

That second half is a non-occurrence, proved by `rfl` and load-bearing as
`doc_geometry_uniform` is: `labelInkBox` and `labelBaseline` take the
measurement and the anchor and nothing else, so a change that let a declared
minimum reach the letters would fail to compile here. It is the frame/letter
separation TeX cannot offer — under node centring the box *is* the reference,
so growing one moves the other. -/
public theorem centre_independent_of_growth (m : LabelMetric) (content : Array Inline)
    (scale : Nat) (align : LabelAlign) (declA declB declA' declB' x y : Sp)
    (hA : declA ≤ declA') (hB : declB ≤ declB') :
    Box.le (nodeExtentBox x y (nodeExtent m content scale align declA declB).1
             (nodeExtent m content scale align declA declB).2)
        (nodeExtentBox x y (nodeExtent m content scale align declA' declB').1
          (nodeExtent m content scale align declA' declB').2) ∧
      labelBaseline y align (m content scale) = labelBaseline y align (m content scale) ∧
      labelInkBox x y align (m content scale) = labelInkBox x y align (m content scale) := by
  refine ⟨?_, rfl, rfl⟩
  have step : ∀ p q r : Int, p ≤ q → max p r ≤ max q r := by intro p q r h; omega
  exact nodeExtentBox_monotone x y _ _ _ _ (step _ _ _ hA) (step _ _ _ hB)

/-- **What the extent is for: a relative placement parts text.** Two nodes
whose centres stand `sep` apart *plus* both half-extents — which is what
`right =of` computes, and what `Picture.placeRight_border_exact` says
exactly — set label ink that does not overlap, for any positive separation
and whatever face resolves. The defect this closes is the composition
failing at its input: the arithmetic was exact about an extent of zero, so
three labels in a row landed on top of one another.

A separation rather than a containment, so a new shape by the naming
registry's leave: it is the fact `nodeExtent_covers` exists *for*, and it
reads as the containment used twice — A's ink ends inside A's extent, B's
begins inside B's, and the extents are `sep` apart by construction. -/
public theorem nodeExtent_separates (m : LabelMetric) (ca cb : Array Inline)
    (sa sb : Nat) (alignA alignB : LabelAlign) (aA aB bA bB : Sp)
    (x y sep : Sp) (hsep : 0 < sep) :
    (labelInkBox x y alignA (m ca sa)).2.1 <
      (labelInkBox
        (x + (sep + (nodeExtent m ca sa alignA aA aB).1
          + (nodeExtent m cb sb alignB bA bB).1)) y alignB (m cb sb)).1.1 := by
  have ha := (nodeExtent_covers m ca sa alignA aA aB x y).2.2.1
  have hb := (nodeExtent_covers m cb sb alignB bA bB
    (x + (sep + (nodeExtent m ca sa alignA aA aB).1
      + (nodeExtent m cb sb alignB bA bB).1)) y).1
  simp only [nodeExtentBox] at ha hb
  have chain : ∀ p u q s b v a : Int,
      p ≤ u → v + (s + a + b) - b ≤ q → 0 < s → u = v + a → p < q := by
    intro p u q s b v a h1 h2 h3 h4; omega
  exact chain _ _ _ sep _ x _ ha hb hsep rfl

/-- The hull fold over a list of boxes, `List` companion first as every
walk here. Polymorphic in what it reads a box from, so one walk and one set
of containment lemmas serve the declared hull, the measured hull, and a
caller that already holds the boxes. -/
private def boxFoldList {α : Type} (f : α → Box) (acc : Box) : List α → Box
  | [] => acc
  | s :: rest => boxFoldList f (Box.join acc (f s)) rest

/-- The smallest box holding every box in an array. Empty is the empty box
at the origin. -/
public def Box.hull (bs : Array Box) : Box :=
  match bs.toList with
  | [] => ((0, 0), (0, 0))
  | b :: rest => boxFoldList id b rest

/-- The declared hull's fold. -/
private def bboxList (acc : Box) : List Shape → Box := boxFoldList Shape.box acc

/-- The hull of a per-shape box over a picture, read through `Box.hull` so
a caller that needs the boxes themselves — to compare them pairwise, say —
computes them once and folds the same way. -/
public def Picture.boxFold (p : Picture) (f : Shape → Box) : Box :=
  Box.hull (p.shapes.map f)

/-- The picture's bounding box: the join of its shapes' declared boxes. -/
public def Picture.bbox (p : Picture) : Box := p.boxFold Shape.box

/-- Every label's ink box, in shape order: what a pairwise comparison
reads, and what the measured hull folds. One measurement per label. -/
public def Picture.inkBoxes (p : Picture) (m : LabelMetric) : Array Box :=
  p.shapes.map (Shape.inkBox m)

/-- The picture's **ink** box under a measurement: the hull of its shapes'
ink boxes, so a node label's set text is inside it and not merely its
anchor. This is the box a caller must reserve; `bbox` is what the IR knows
with no face. -/
public def Picture.inkBbox (p : Picture) (m : LabelMetric) : Box :=
  Box.hull (p.inkBoxes m)

private theorem boxFoldList_le {α : Type} (f : α → Box) (acc : Box) (xs : List α) :
    Box.le acc (boxFoldList f acc xs) := by
  induction xs generalizing acc with
  | nil => exact Box.le_refl acc
  | cons s rest ih =>
    exact Box.le_trans (Box.le_join_left acc (f s)) (ih (Box.join acc (f s)))

private theorem boxFoldList_mem {α : Type} (f : α → Box) (acc : Box) (xs : List α) (s : α)
    (h : s ∈ xs) : Box.le (f s) (boxFoldList f acc xs) := by
  induction xs generalizing acc with
  | nil => cases h
  | cons t rest ih =>
    cases h with
    | head =>
      exact Box.le_trans (Box.le_join_right acc (f s)) (boxFoldList_le _ _ rest)
    | tail _ hmem => exact ih (Box.join acc (f t)) hmem

private theorem bboxList_le (acc : Box) (xs : List Shape) : Box.le acc (bboxList acc xs) :=
  boxFoldList_le _ acc xs

private theorem bboxList_mem (acc : Box) (xs : List Shape) (s : Shape) (h : s ∈ xs) :
    Box.le s.box (bboxList acc xs) := boxFoldList_mem _ acc xs s h

/-- **The hull covers what it folds**: every box of the array lies inside
the hull. The registered `_covers` shape, and the one fact every hull below
is an instance of. -/
public theorem Box.hull_covers (bs : Array Box) (b : Box) (h : b ∈ bs) :
    Box.le b (Box.hull bs) := by
  have h' : b ∈ bs.toList := by simpa using h
  unfold Box.hull
  split
  · next heq => rw [heq] at h'; cases h'
  · next t rest heq =>
    rw [heq] at h'
    cases h' with
    | head => exact boxFoldList_le _ _ rest
    | tail _ hmem => exact boxFoldList_mem _ _ rest b hmem

/-- The per-shape hull covers every shape's box. -/
public theorem Picture.boxFold_covers (p : Picture) (f : Shape → Box) (s : Shape)
    (h : s ∈ p.shapes) : Box.le (f s) (p.boxFold f) :=
  Box.hull_covers _ (f s) (Array.mem_map_of_mem h)

/-- The picture stays in its declared box: the bounding box contains the
declared box of every shape it emits (labels bound at their anchors, see
`Shape.box`). -/
public theorem Picture.box_in_bbox (p : Picture) (s : Shape) (h : s ∈ p.shapes) :
    Box.le s.box p.bbox := p.boxFold_covers Shape.box s h

/-- **A picture's box contains its ink.** The invariant the engine lacked:
`box_in_bbox` bounds every *shape*, and a label's shape is a point, so the
declared hull of a diagram of node labels is the hull of their anchors —
narrower than the text by half a label at each edge. A caller that
reserves that box paints outside it, and the overrun check that reads it
measures a box which fits while glyphs leave the page.

Stated over an arbitrary measurement, because the measurement is the one
thing the IR cannot supply (`LabelMetric`): whatever face resolves, the
ink of every shape is inside the box computed with that face. Each
artifact's version is this fact projected through the metric it can
answer. -/
public theorem Picture.inkBbox_covers (p : Picture) (m : LabelMetric) (s : Shape)
    (h : s ∈ p.shapes) : Box.le (s.inkBox m) (p.inkBbox m) :=
  Box.hull_covers _ (s.inkBox m) (Array.mem_map_of_mem h)

/-- **The natural box**: what TikZ reserves when nothing is declared — every
mark's ink (`inkBoxes`, so a label's letters and not its anchor) and every
node's border (`borders`: the text extent plus `inner sep`, which pgf's
bounding box includes even for a node no path draws). -/
public def Picture.natural (p : Picture) (m : LabelMetric) : Box :=
  Box.hull (p.inkBoxes m ++ p.borders)

/-- **The box a picture occupies**: the declared box when `\useasboundingbox`
gave one, else the natural box. The one IR value both backends read — the
PDF reserves and places by it, the SVG's `viewBox` is it — so the two
artifacts cannot size one picture two ways (`Pdf.picture_box_agree`,
`HtmlDoc.pictureViewBox_projects`). -/
public def Picture.box (p : Picture) (m : LabelMetric) : Box :=
  p.declared.getD (p.natural m)

/-- **A picture occupies exactly its declared box** (pgf manual §15.8): with
a declaration in force the box is that box, whatever the measurement and
whatever the marks — so a figure that declares room for nodes a later
frame adds keeps its place, and its ink sits where the declaration puts
it, off-centre when the box extends past the ink. -/
public theorem Picture.box_declared_exact (p : Picture) (m : LabelMetric) (b : Box)
    (h : p.declared = some b) : p.box m = b := by
  simp [Picture.box, h]

/-- **A label rewrite its measurement cannot see moves no box** (`_id`):
every ink box, the natural box and so the picture's box stay where they
were. What lets a pass rewrite label content after elaboration placed the
picture — alphabet resolution does — without moving the box placement read. -/
public theorem Picture.mapLabels_box_id (m : LabelMetric) (f : Array Inline → Array Inline)
    (hm : ∀ content scale, m (f content) scale = m content scale) (p : Picture) :
    (p.mapLabels f).box m = p.box m := by
  have hboxes : (p.mapLabels f).inkBoxes m = p.inkBoxes m := by
    simp only [Picture.inkBoxes, Picture.mapLabels, Array.map_map]
    congr 1
    funext s
    cases s <;> simp [Shape.mapLabel, Shape.inkBox, hm]
  simp only [Picture.box, Picture.natural, hboxes]
  rfl

/-- **Where a picture stands on its line**: how far above its box's bottom
edge the declared baseline runs (pgf manual §12.2.1), held inside the box;
with nothing declared, the bottom edge is on the line. The one value both
backends set a picture on its baseline by — the PDF's depth below the line
(`Layout.placePicture`), the SVG's `vertical-align` (`HtmlDoc.pictureSvg`). -/
public def Picture.rise (p : Picture) (m : LabelMetric) : Sp :=
  (p.baseline.map fun yb =>
    max 0 (min ((p.box m).2.2 - (p.box m).1.2) (yb - (p.box m).1.2))).getD 0

/-- The clamp `rise` applies, over bare `Int` so `omega` reads it. -/
private theorem clampRise_between (lo hi yb : Int) (h : lo ≤ hi) :
    0 ≤ max 0 (min (hi - lo) (yb - lo)) ∧ max 0 (min (hi - lo) (yb - lo)) ≤ hi - lo := by
  omega

/-- **The baseline runs through the box**: a picture's rise lies between its
box's bottom edge and its top, whatever it declared — a baseline declared
above the picture is its top edge on the line, one below it its bottom. -/
public theorem Picture.rise_between (p : Picture) (m : LabelMetric)
    (h : (p.box m).1.2 ≤ (p.box m).2.2) :
    0 ≤ p.rise m ∧ p.rise m ≤ (p.box m).2.2 - (p.box m).1.2 := by
  unfold Picture.rise
  cases p.baseline with
  | some yb => exact clampRise_between _ _ _ h
  | none => exact ⟨Int.le_refl 0, Int.sub_nonneg.mpr h⟩

/-- **Otherwise its box covers every mark**: with nothing declared, every
shape's ink and every node's border lies inside the box, whatever face
resolves. `inkBbox_covers` is the ink half of the old box; the borders are
what made TikZ's box one inner sep larger than the engine's. -/
public theorem Picture.box_covers (p : Picture) (m : LabelMetric) (h : p.declared = none) :
    (∀ s ∈ p.shapes, Box.le (s.inkBox m) (p.box m)) ∧
      (∀ b ∈ p.borders, Box.le b (p.box m)) := by
  simp only [Picture.box, h, Option.getD_none, Picture.natural]
  refine ⟨fun s hs => ?_, fun b hb => ?_⟩
  · exact Box.hull_covers _ _ (Array.mem_append_left _ (Array.mem_map_of_mem hs))
  · exact Box.hull_covers _ _ (Array.mem_append_right _ hb)

/-- The measured box loses nothing the declared box held: a shape's own
geometry is its ink box unchanged, and a label's anchor is inside the
measured box its ink occupies, so widening to the ink can only grow the
hull. Every containment `box_in_bbox` gave still holds of `inkBbox`. -/
public theorem Shape.box_le_inkBox (m : LabelMetric) (s : Shape) : Box.le s.box (s.inkBox m) := by
  cases s with
  | label x y content color scale align =>
    exact labelGlyphBox_covers x y align _
  | rect _ _ _ _ _ => exact Box.le_refl _
  | circle _ _ _ _ _ => exact Box.le_refl _
  | frame _ _ _ _ _ _ => exact Box.le_refl _
  | edge _ _ _ => exact Box.le_refl _

/-- Where a picture lands on a page: the map from picture coordinates
(y up) to layout coordinates (y down). The elaborator has already applied
`scale=`, so what is left is a translation and the y reflection — affine
with unit determinant, hence exactly invertible over sp
(`ofPage_toPage`/`toPage_ofPage`), monotone in x and antitone in y
(`toPage_box`): a shape's placed box is the transform of its declared box,
corner for corner, so a diagram cannot silently drift off its slot. -/
public structure Place where
  /-- Page x where the picture's `xmin` lands (its left edge). -/
  x0 : Sp
  /-- Page y where the picture's `ymax` lands (its top edge). -/
  yTop : Sp
  xmin : Sp
  ymax : Sp
  deriving Repr, BEq, Inhabited

@[expose] public def Place.toPage (t : Place) (u : Sp × Sp) : Sp × Sp :=
  (t.x0 + (u.1 - t.xmin), t.yTop + (t.ymax - u.2))

public def Place.ofPage (t : Place) (q : Sp × Sp) : Sp × Sp :=
  (t.xmin + (q.1 - t.x0), t.ymax - (q.2 - t.yTop))

/-- The placement transform loses nothing: every page point recovers its
picture point exactly. -/
public theorem Place.ofPage_toPage (t : Place) (u : Sp × Sp) : t.ofPage (t.toPage u) = u := by
  obtain ⟨ux, uy⟩ := u
  have hx : ∀ a b c : Int, b + (a + (c - b) - a) = c := by intro a b c; omega
  have hy : ∀ m yT q : Int, m - (yT + (m - q) - yT) = q := by intro m yT q; omega
  simp only [toPage, ofPage, Prod.mk.injEq]
  exact ⟨hx _ _ _, hy _ _ _⟩

public theorem Place.toPage_ofPage (t : Place) (q : Sp × Sp) : t.toPage (t.ofPage q) = q := by
  obtain ⟨qx, qy⟩ := q
  have hx : ∀ a b c : Int, b + (a + (c - b) - a) = c := by intro a b c; omega
  have hy : ∀ yT m q : Int, yT + (m - (m - (q - yT))) = q := by intro yT m q; omega
  simp only [toPage, ofPage, Prod.mk.injEq]
  exact ⟨hx _ _ _, hy _ _ _⟩

/-- The transform preserves containment: a picture point inside a declared
box lands inside that box's transform — x keeps its order, y reverses, so
the placed box's top-left corner is the declared box's `(xmin, ymax)`. With
`box_in_bbox` this is why no shape escapes the placed picture. -/
public theorem Place.toPage_box (t : Place) (b : Box) (u : Sp × Sp)
    (hx1 : b.1.1 ≤ u.1) (hx2 : u.1 ≤ b.2.1) (hy1 : b.1.2 ≤ u.2) (hy2 : u.2 ≤ b.2.2) :
    (t.toPage (b.1.1, b.2.2)).1 ≤ (t.toPage u).1
      ∧ (t.toPage u).1 ≤ (t.toPage (b.2.1, b.1.2)).1
      ∧ (t.toPage (b.1.1, b.2.2)).2 ≤ (t.toPage u).2
      ∧ (t.toPage u).2 ≤ (t.toPage (b.2.1, b.1.2)).2 := by
  have hx : ∀ x0 m a b : Int, a ≤ b → x0 + (a - m) ≤ x0 + (b - m) := by
    intro x0 m a b h; omega
  have hy : ∀ yT m a b : Int, a ≤ b → yT + (m - b) ≤ yT + (m - a) := by
    intro yT m a b h; omega
  simp only [toPage]
  exact ⟨hx _ _ _ _ hx1, hx _ _ _ _ hx2, hy _ _ _ _ hy2, hy _ _ _ _ hy1⟩

end Pic

/-- Horizontal alignment of a table column's cells: `l`, `c`, `r`; also the
side a scope sets its boxes on (`slackHalves`). -/
public inductive HAlign where
  | left
  | center
  | right
  deriving Repr, BEq, Inhabited

/-- The side as the `text-align` keyword the scope rules print. -/
@[expose] public def HAlign.align : HAlign → String
  | .left => "left"
  | .center => "center"
  | .right => "right"

/-- How many halves of a line's slack stand before a box its scope sets —
a tabular, a picture, a lone minipage: none flush left, one centred, both
flush right. TeX sets such a box in a line like a word, so the scope's
`\leftskip` and `\rightskip` place it (ltmiscen.dtx: `center` is
`\trivlist\centering`, and `\centering` sets both skips to `\@flushglue`;
`flushright` sets `\leftskip` alone). Both backends read the side through
this one value: the page's offset (`boxOffset`) and the stylesheet's
margins (`HtmlDoc.box_margins_agree`). -/
@[expose] public def HAlign.slackHalves : HAlign → Nat
  | .left => 0
  | .center => 1
  | .right => 2

/-- A box's offset inside the measure it stands in: its side's share of the
slack the box leaves. -/
public def HAlign.boxOffset (h : HAlign) (slack : Int) : Int := slack * h.slackHalves / 2

/-- **A box its scope sets never leaves the measure** (`_between`): with the
slack non-negative, the offset lies between flush left and flush right. -/
public theorem HAlign.boxOffset_between (h : HAlign) (s : Int) (hs : 0 ≤ s) :
    0 ≤ h.boxOffset s ∧ h.boxOffset s ≤ s := by
  cases h <;> simp only [boxOffset, slackHalves] <;> omega

/-- Which edge of the measure a ragged scope's lines hang from: LaTeX's two
ragged settings, named for what is *flush* rather than what is ragged —
`\raggedright` is ragged on the right and flush left, `\raggedleft` the
mirror, and the spellings invite exactly that confusion. Two values, so a
ragged scope cannot claim to be centred: `center` is its own block, and a
centred line leaves equal slack on both sides where a flush line leaves it
all on one. -/
public inductive FlushSide where
  | left
  | right
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The declared side as the `ElementStyle.align` vocabulary both backends
already read — one resolving site, so the page's origin and the
stylesheet's `text-align` cannot name different edges from one IR value
(`ragged_sides_agree`). -/
@[expose] public def FlushSide.align : FlushSide → String
  | .left => "left"
  | .right => "right"

/-- The declared side as the page's line origin: `Layout.Geom.flushRight`'s
value. The layout walk reads this and nothing else about the side, so the
placement arithmetic has one source (`ragged_sides_agree`). -/
public def FlushSide.flushRight : FlushSide → Bool
  | .left => false
  | .right => true

/-- The two readings of one declared side agree: the page hangs a scope's
lines from the right edge exactly when the stylesheet declares the right
edge. These are the only two functions a backend may learn the side
through — Layout reads `flushRight`, the HTML rule reads `align` — so an
artifact cannot align an edge the other does not, whatever either emitter
does downstream. The `backend_gaps_agree` shape: two projections of one IR
value, stated on the IR because both artifacts must honour it. -/
public theorem ragged_sides_agree (s : FlushSide) :
    s.flushRight = true ↔ s.align = "right" := by
  cases s <;> simp [FlushSide.flushRight, FlushSide.align]

/-- The declared side as the side its boxes stand on. -/
@[expose] public def FlushSide.halign : FlushSide → HAlign
  | .left => .left
  | .right => .right

/-- The dump spelling, and the only place a ragged side is named in a
golden. -/
public def FlushSide.label : FlushSide → String
  | .left => "left"
  | .right => "right"

/-- LaTeX's four ragged-setting spellings and the side each makes flush —
the one naming site, so the declaration form, the environment form and the
inline diagnostic cannot disagree about which edge a name asks for.
`\raggedright` and `{flushleft}` are the same setting (ltmiscen.dtx:
`{flushleft}` is a trivlist under `\raggedright`), and `\raggedleft` and
`{flushright}` its mirror. -/
public def raggedSideOf? : String → Option FlushSide
  | "raggedright" | "flushleft" => some .left
  | "raggedleft" | "flushright" => some .right
  | _ => none

/-- A percentage track spelling shared by table targets and box tracks. -/
public def percentCss (permille : Nat) : String :=
  (if permille % 10 == 0 then s!"{permille / 10}"
   else s!"{permille / 10}.{permille % 10}") ++ "%"

/-- The total affine width a flexible table targets in its enclosing
measure. It remains typed until each backend supplies that local measure. -/
public inductive TableTarget where
  | sized (width : Affine Measure)
  deriving Repr, BEq, Inhabited

@[match_pattern, expose] public def TableTarget.frac (permille : Nat) : TableTarget :=
  .sized (Affine.scaleQ permille 1000 (.ref .lineWidth))

@[match_pattern, expose] public def TableTarget.abs (w : Sp) : TableTarget :=
  .sized (.lit { width := .ofSp w })

/-- Resolve a flexible table target against its local horizontal measure. -/
public def TableTarget.resolve (target : TableTarget) (measure : Sp) : Sp :=
  match target with
  | .sized e => max 0 (e.resolveWidth (MeasureValues.horizontal measure 0))

/-- A table column's declared width. `natural` sizes to the widest cell;
`sized` carries the shared affine length until the table measure is known;
`flex` receives an equal share of its target left after fixed columns and
gaps. -/
public inductive ColWidth where
  | natural
  | sized (width : Affine Measure)
  | flex (target : TableTarget)
  deriving Repr, BEq, Inhabited

@[match_pattern, expose] public def ColWidth.frac (permille : Nat) : ColWidth :=
  .sized (Affine.scaleQ permille 1000 (.ref .lineWidth))

@[match_pattern, expose] public def ColWidth.abs (w : Sp) : ColWidth :=
  .sized (.lit { width := .ofSp w })

/-- A box's declared width: `{minipage}`/`\parbox`/`{column}`'s mandatory
argument. `frac` is a factor of the enclosing measure in per mille
(`.45\textwidth`, and a token or document command that spells one), `abs` an
absolute length (`60pt`), and `share` the width a `{column}` leaves
undeclared — an equal part of whatever the declared boxes leave over.

Its own type rather than `ColWidth`, on meaning. A table's `natural` column
sizes *down* to its widest cell; a box's undeclared width grows *up* to fill
the leftover measure. One constructor answering both would make one of the
two readings false at every site, which is the `role`-versus-salvage
argument (PLAN 2026-09-24) in a second place.

`abs` is a length and stays one until layout, rather than being divided into
per mille against the page's measure where it is parsed. A per-mille value
is *relative*, so fixing its reference at elaboration is only right for a
box at the top level: a 60pt box inside a `.45\textwidth` column, converted
against the page and re-applied to the column, comes out at 45% of 60pt. The
reference a width is relative to is known at placement and nowhere earlier —
the `Sourced` entry's finding (PLAN 2026-09-24) one layer over, where
resolving in the wrong layer forced an operator to invent an answer it could
not have. -/
public inductive BoxSize where
  | share
  | sized (width : Affine Measure)
  deriving Repr, BEq, Inhabited

@[match_pattern, expose] public def BoxSize.frac (permille : Nat) : BoxSize :=
  .sized (Affine.scaleQ permille 1000 (.ref .lineWidth))

@[match_pattern, expose] public def BoxSize.abs (w : Sp) : BoxSize :=
  .sized (.lit { width := .ofSp w })

/-- Which point of a box stands on the baseline of the row it is set in —
the `[pos]` a box declares (latex.ltx `\@iiiparbox`: `t` builds a `\vtop`,
whose reference point is its first line's baseline; `b` a `\vbox`, its last
line's; `c` a `\vcenter`, its middle; beamer's `column` adds `T`, the top
edge). A picture's baseline is its bottom edge unless it declares one
(`Pic.Picture.baseline`). `top` is also what a box that declares nothing
gets: the engine's row sets undeclared boxes top-aligned, where LaTeX
centres a minipage and beamer its columns — a standing divergence. -/
public inductive BoxPos where
  | top
  | first
  | center
  | last
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a box in a row declares: its width and the point it stands on the
row's baseline by. The type kept the width's name so the row's walks stay
untouched; `share`, `frac` and `abs` build an undeclared-position box. -/
public structure BoxWidth where
  size : BoxSize
  pos : BoxPos := .top
  deriving Repr, BEq, Inhabited

@[match_pattern, expose] public def BoxWidth.share : BoxWidth := ⟨.share, .top⟩
@[match_pattern, expose] public def BoxWidth.sized (width : Affine Measure) : BoxWidth := ⟨.sized width, .top⟩
@[match_pattern, expose] public def BoxWidth.frac (permille : Nat) : BoxWidth :=
  ⟨.frac permille, .top⟩
@[match_pattern, expose] public def BoxWidth.abs (w : Sp) : BoxWidth :=
  ⟨.abs w, .top⟩

/-- The declared width against a known measure: the width the box is set at.
One resolving site, read by the page's column arithmetic, so a box's measure
is a function of its declaration and the measure it stands in and of nothing
else. A declared width past the enclosing measure is clamped to it: a box
cannot be wider than what contains it, and a document that asks is answered
by the measure rather than by ink off the page. `share` resolves to nothing
here — the leftover is not a function of one column — and the caller divides
it (`Layout`'s `shareW`). -/
public def BoxWidth.resolve (w : BoxWidth) (measure : Sp) : Option Sp :=
  match w.size with
  | .share => none
  | .sized e =>
    let values := MeasureValues.horizontal measure 0
    some (min measure (max 0 (e.resolveWidth values)))

/-- The declared width as a CSS grid track, structured: the same three
readings the page resolves, before they are spelled
(`boxWidth_tracks_agree`). Structured rather than a string, so the
agreement between the two backends' readings is a statement about values
and not about formatting. -/
public inductive Track where
  | free
  | percent (permille : Nat)
  | length (l : Sp)
  | affine (e : Affine Measure)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The track a declared width takes: a fraction is a percentage of the
grid's own width, which is the enclosing measure; an absolute length is that
length; a shared column takes a free fraction of the leftover, which is what
`1fr` means. -/
public def BoxWidth.trackOf (w : BoxWidth) : Track :=
  match w.size with
  | .share => .free
  | .sized e => .affine e

/-- One normalized CSS term from an affine box track. -/
private inductive TrackTerm where
  | length (l : Dim.Length)
  | measure (m : Measure) (num : Int) (den : Nat)

private def affineTrackTerms (e : Affine Measure) : Array TrackTerm := Id.run do
  let rec go (num : Int) (den : Nat) (out : Array TrackTerm) :
      Affine Measure → Array TrackTerm
    | .lit g => out.push (.length (g.width.scale num den))
    | .ref m => out.push (.measure m num den)
    | .scale n d e => go (num * n) (den * d) out e
    | .add a b => go num den (go num den out a) b
    | .sub a b => go (-num) den (go num den out a) b
  return go 1 1 #[] e

private def milliDecimal (n : Int) : String :=
  let sign := if n < 0 then "-" else ""
  let n := n.natAbs
  let whole := n / 1000
  let wholeText := toString whole
  let frac := n % 1000
  if frac == 0 then sign ++ wholeText
  else
    let digits := ((toString (1000 + frac)).drop 1).toString
    let digits := if digits.endsWith "00" then (digits.dropEnd 2).toString
      else if digits.endsWith "0" then (digits.dropEnd 1).toString else digits
    sign ++ wholeText ++ "." ++ digits

private def TrackTerm.css (horizontalUnit : String) : TrackTerm → Array String
  | .length l =>
    (if l.sp == 0 then #[] else #[l.sp.toPtString ++ "pt"]) ++
    (if l.em == 0 then #[] else #[milliDecimal l.em ++ "em"]) ++
    (if l.ex == 0 then #[] else #[milliDecimal l.ex ++ "ex"])
  | .measure m num den =>
    let unit := if m == .textHeight then "dvh" else horizontalUnit
    #[milliDecimal (num * 100000 / den) ++ unit]

private def affineTrackCss (e : Affine Measure) (horizontalUnit : String) : String :=
  let terms := (affineTrackTerms e).flatMap (TrackTerm.css horizontalUnit)
  match terms[0]? with
  | none => "0pt"
  | some first =>
    let body := (terms.extract 1 terms.size).foldl (fun out term =>
      if term.startsWith "-" then out ++ " - " ++ (term.drop 1).toString
      else out ++ " + " ++ term) first
    if terms.size == 1 then body else "calc(" ++ body ++ ")"

/-- One track, spelled. The only site a grid track's units are written, read
by the HTML backend. -/
public def Track.css : Track → String
  | .free => "1fr"
  | .percent p => percentCss p
  | .length l => l.toPtString ++ "pt"
  | .affine e => affineTrackCss e "%"

/-- An affine local measure in a property whose percentages would use the
wrong axis (font size, line height, block size): `cqi` is the nearest
query container's inline measure. -/
public def Track.contextCss (e : Affine Measure) : String :=
  affineTrackCss e "cqi"

/-- Spell a flexible table target from the same affine value layout resolves. -/
public def TableTarget.css : TableTarget → String
  | .sized e => Track.css (.affine e)

/-- Does this declaration name a width at all? The question the census and
the diagnostics ask, so `share` is named once rather than tested as a
constructor at each site. -/
public def BoxWidth.declared (w : BoxWidth) : Bool :=
  match w.size with
  | .share => false
  | .sized _ => true

/-- Is this the leftover's track — the one whose width is not the box's own
declaration but what the declared boxes leave? -/
public def Track.isFree : Track → Bool
  | .free => true
  | .percent _ | .length _ | .affine _ => false

/-- The page's resolution and the stylesheet's track are two readings of one
declared width, and they agree on which declarations name a width: a
fraction and a length resolve against any measure and take a sized track, a
shared column resolves to nothing and takes the free track. The
`backend_gaps_agree` shape — stated on the IR because both artifacts must
honour it, with `HtmlDoc.gridTracks` and `Layout`'s column arithmetic as its
two projections. -/
public theorem boxWidth_tracks_agree (w : BoxWidth) (measure : Sp) :
    (w.resolve measure).isSome = w.declared ∧
      w.trackOf.isFree = !w.declared := by
  rcases w with ⟨s, _⟩
  cases s <;> exact ⟨rfl, rfl⟩

/-- One column of a table, from the `tabular` column spec. A `p` column
wraps its cells at the declared width; `l`/`c`/`r` set each cell as one
unbreakable line. -/
public structure ColSpec where
  width : ColWidth
  align : HAlign
  /-- A wrapping column's paragraphs set ragged on `align`'s side: its
  `>{…}`/`<{…}` modifier declared `\raggedright`, `\raggedleft` or
  `\centering` (array manual §1). A bare `p` cell justifies — its `\vtop`
  runs `\@arrayparboxrestore`, which zeroes `\leftskip` and `\rightskip`
  (latex.ltx) — and a declaration in the modifier sets those skips again
  inside the cell, so `>{\raggedright}p` sets ragged where `p` justifies. -/
  ragged : Bool := false
  deriving Repr, BEq, Inhabited

/-- Relative table-track hints, in permille of the flexible target. Natural
columns measure their own content; sized columns with the target's reference
have its relative width, and flexible columns split the remaining share.
Unresolved expressions retain their affine track. These are structural hints,
not final physical widths: padding, natural content, and spanning cells enter
the backend's sizing algorithm separately. -/
public def tableColShares (cols : Array ColSpec) (target : TableTarget) : Array (Option Nat) :=
  match target with
  | .sized te =>
    match te.refPermille with
    | none => cols.map fun _ => none
    | some (tm, tperm) =>
      if tperm == 0 then cols.map fun _ => none
      else
        let count := cols.foldl (fun n c =>
          if c.width matches .flex _ then n + 1 else n) 0
        let sizedSum := cols.foldl (fun s c => match c.width with
          | .sized e => match e.refPermille with
            | some (m, p) => if m == tm then s + p * 1000 / tperm else s
            | none => s
          | .natural | .flex _ => s) 0
        let flexShare := if count == 0 then 0 else (1000 - min 1000 sizedSum) / count
        cols.map fun c => match c.width with
          | .natural => none
          | .sized e => e.refPermille.bind fun (m, p) =>
            if m == tm then some (p * 1000 / tperm) else none
          | .flex _ => some flexShare

/-- `tableColShares` answers one share per column. -/
public theorem tableColShares_count_exact (cols : Array ColSpec) (target : TableTarget) :
    (tableColShares cols target).size = cols.size := by
  unfold tableColShares
  repeat' split
  all_goals simp

/-- A natural column is excluded from the target split: it carries no share
(`none`), the typed statement of "naturals are left to `auto`". -/
public theorem tableColShares_natural_exact (cols : Array ColSpec) (target : TableTarget)
    (j : Nat) (c : ColSpec) (hget : cols[j]? = some c) (hc : c.width = .natural) :
    (tableColShares cols target)[j]? = some none := by
  unfold tableColShares
  repeat' split
  all_goals simp [hget, hc]

/-- Flexible tracks receive equal relative hints. This does not claim equality
of final widths after each backend measures content and applies span constraints. -/
public theorem tableColShares_flex_contract (cols : Array ColSpec) (target : TableTarget)
    (i j : Nat) (ci cj : ColSpec) (ti tj : TableTarget)
    (hi : cols[i]? = some ci) (hj : cols[j]? = some cj)
    (hwi : ci.width = .flex ti) (hwj : cj.width = .flex tj) :
    (tableColShares cols target)[i]? = (tableColShares cols target)[j]? := by
  unfold tableColShares
  repeat' split
  all_goals simp [hi, hj, hwi, hwj]

/-- A horizontal rule (or declared row gap) inside a table, booktabs'
vocabulary: `top` and `bottom` draw at `heavyRuleWidth`, `mid` at
`lightRuleWidth`, and each carries its documented padding
(`aboveTopSep`/`aboveRuleSep` over it, `belowRuleSep`/`belowBottomSep`
under). `cmid` is `\cmidrule`: `cmidRuleWidth` across columns `a`–`b`
(1-based, inclusive), each end trimmed by `cmidRuleKern` when its flag is
set. `gap` is `\addlinespace` (and `\\[len]`): no ink, declared space. -/
public inductive TableRule where
  | top
  | mid
  | bottom
  | cmid (a : Nat) (b : Nat) (trimL : Bool) (trimR : Bool)
  | gap (space : SymGlue)
  deriving Repr, BEq, Inhabited

/-- `\multicolumn{n}{spec}{…}`: the cell at `col` (0-based) of row `row`
spans `n` columns and sets by its own column `spec` (its alignment, and a
`p{…}` width when it declares one). The `n − 1` cells it covers stay in
`rows`, empty, so rectangularity holds as before and every text walk reads
the spanning text once. Its width follows TeX's rule for a spanned entry
(tex.web §801, $w_j=\max_{i≤j}(w_{ij}-\sum_{i≤k<j}(t_k+w_k))$): a span
enters no single column's maximum, and when it is wider than the columns it
covers plus their gaps, the excess goes to the last covered column. -/
public structure ColSpan where
  row : Nat
  col : Nat
  n : Nat
  spec : ColSpec
  deriving Repr, BEq, Inhabited

/-- The `\multicolumn` head standing at cell `(i, j)`, if any. -/
public def cellSpan? (spans : Array ColSpan) (i j : Nat) : Option ColSpan :=
  spans.find? fun s => s.row == i && s.col == j

/-- The spec a cell sets by, the one resolving site both backends read
(`Layout.cellSide`, `HtmlDoc.cellSideClassOf`): a `\multicolumn` head's own
spec, else its column's, else — a cell past the declared columns — a
natural left one. The spec alone decides: a tabular sets each entry in a box
of its own — an `l`/`c`/`r` entry an `\hfil`-padded `\hbox`, a `p` entry a
`\vtop` whose `\@arrayparboxrestore` zeroes `\leftskip` and `\rightskip`
(latex.ltx) — so the side of the scope the table stands in never reaches a
cell. -/
public def cellSpec (cols : Array ColSpec) (spans : Array ColSpan) (i j : Nat) : ColSpec :=
  match cellSpan? spans i j with
  | some s => s.spec
  | none => cols[j]?.getD { width := .natural, align := .left }

/-- The row index of the first `mid` rule in document order, if any: the
List companion of the header scan below, so the two facts about it are
inductions. -/
public def firstMidRow : List (Nat × TableRule) → Option Nat
  | [] => none
  | (k, .mid) :: _ => some k
  | _ :: rest => firstMidRow rest

/-- booktabs' head, as one IR fact both backends read: the rows before the
first `\midrule` (booktabs.dtx §Rules: "\midrule … separates the header
from the body"). A table with no mid rule declares no header; a mid rule
written before the first row (`\hline`'s frame) heads nothing; a mid
rule index beyond the rows clamps, so the count is a prefix length of
`rows`. `cmid` and `gap` never count — a `\cmidrule` groups columns and
`\addlinespace` is air. The HTML backend ships exactly this prefix as
`<thead>`/`<th>` (`HtmlDoc.th_iff_header_row`); the tagged-PDF `/TH` cells
read the same number. -/
public def tableHeaderRows (rows : Array (Array (Array Inline)))
    (rules : Array (Nat × TableRule)) : Nat :=
  ((firstMidRow rules.toList).map fun k => min k rows.size).getD 0

public theorem firstMidRow_eq_none_of_no_mid (rules : List (Nat × TableRule))
    (h : ∀ p ∈ rules, p.2 ≠ .mid) : firstMidRow rules = none := by
  induction rules with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, r⟩ := p
    have hp := h (k, r) (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, q.2 ≠ .mid := fun q hq => h q (List.mem_cons_of_mem _ hq)
    cases r with
    | mid => exact absurd rfl hp
    | top => exact ih hrest
    | bottom => exact ih hrest
    | cmid a b l rt => exact ih hrest
    | gap s => exact ih hrest

/-- The header count is a prefix length of `rows`: never below zero (a
`Nat`), never past the last row. -/
public theorem tableHeaderRows_between (rows : Array (Array (Array Inline)))
    (rules : Array (Nat × TableRule)) :
    0 ≤ tableHeaderRows rows rules ∧ tableHeaderRows rows rules ≤ rows.size := by
  refine ⟨Nat.zero_le _, ?_⟩
  unfold tableHeaderRows
  cases firstMidRow rules.toList with
  | none => exact Nat.zero_le _
  | some k => exact Nat.min_le_right _ _

/-- No mid rule, no header: a `\toprule`/`\bottomrule` frame, a
`\cmidrule`, or an `\addlinespace` alone never promotes a row. -/
public theorem tableHeaderRows_zero_of_no_mid (rows : Array (Array (Array Inline)))
    (rules : Array (Nat × TableRule)) (h : ∀ p ∈ rules, p.2 ≠ .mid) :
    tableHeaderRows rows rules = 0 := by
  unfold tableHeaderRows
  rw [firstMidRow_eq_none_of_no_mid rules.toList
    (fun p hp => h p (Array.mem_toList_iff.mp hp))]
  rfl

/-- What a float wraps: `{figure}` or `{table}`, or a `{subfigure}`/
`{subtable}` box inside one (`sub`). The kinds differ in name and in which
counter numbers them (`numberFloats`); the caption and separation
machinery is one. -/
public inductive FloatKind where
  | figure
  | table
  | sub
  /-- An `{algorithm}` float: numbered by its own counter, captioned with
  the locale's algorithm word (`Locale.algorithm`, algorithm2e's
  `\algorithmcfname`). -/
  | algorithm
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What an algorithm's input/output line declares (algorithm2e's
`\SetKwInput` defaults: `\KwIn`/`\KwOut`/`\KwData`/`\KwResult`,
algorithm2e.sty §defaults; algorithmicx's `\Require`/`\Ensure` land on
`input`/`output`). `named` is a document-defined `\SetKwInOut` label —
the author's own word, carried as declared. -/
public inductive AlgIo where
  | input
  | output
  | data
  | result
  | named (label : String)
  deriving Repr, BEq, Inhabited

/-- The block forms an algorithm line can open, closed: algorithm2e's
`\SetKwFor`/`\SetKwIF`/`\SetKwRepeat` defaults and algorithmicx's
`\For`…`\EndFor` family both parse onto these. The opener selects the
keyword pair the backends generate (`AlgWords`); a closer carries its
opener so `repeat` can close on `until` with its condition while every
other block closes on `end`. -/
public inductive AlgOpen where
  | forLoop
  | forEach
  | whileLoop
  | ifThen
  | elseIf
  | elseBranch
  | repeatLoop
  | function
  | procedure
  deriving Repr, BEq, Inhabited

/-- One pseudocode line's kind. The keywords a kind implies are generated
text from the locale keyword table (`algWords`), like caption prefixes —
never stored in the line, so the census reads declarations only. -/
public inductive AlgKind where
  | statement
  | io (kind : AlgIo)
  | opener (o : AlgOpen)
  | closer (o : AlgOpen)
  | ret
  deriving Repr, BEq, Inhabited

/-- One pseudocode line: its nesting depth, its kind, the author's content
(a `\For` condition, a statement's text), and an optional end-of-line
comment (`\tcc`/`\tcp`, algorithmicx `\Comment`). Content and comment are
document text and censused; the kind's keywords are generated. -/
public structure AlgLine where
  depth : Nat
  kind : AlgKind
  content : Array Inline
  comment : Option (Array Inline)
  deriving Repr, BEq, Inhabited

/-- The algorithm keyword table for one language: the words the backends
generate around a line's declared content. Sourced from algorithm2e's own
keyword defaults — English from `\algocf@defaults@common`
(`\SetKwFor{For}{for}{do}{end for}`, `\SetKwIF{If}{ElseIf}{Else}{if}{then}
{else if}{else}{end if}`, `\SetKwRepeat{Repeat}{repeat}{until}`,
`\SetKwInput{KwIn}{Input}` and family, `\SetKw{Return}{return}`), French
and German from the sty's `french`/`german` keyword blocks, and the
function/procedure words from the language options' `\@algocf@procname`/
`\@algocf@funcname`. Closers are the `shortend` form ("end"), the
package's own default option set (`\ExecuteOptions{…,lined,shortend}`). -/
public structure AlgWords where
  forKw : String
  foreachKw : String
  whileKw : String
  doKw : String
  ifKw : String
  thenKw : String
  elseIfKw : String
  elseKw : String
  repeatKw : String
  untilKw : String
  endKw : String
  returnKw : String
  inputKw : String
  outputKw : String
  dataKw : String
  resultKw : String
  functionKw : String
  procedureKw : String
  deriving Repr, BEq, Inhabited

/-- The keyword table a locale tag selects — en, fr, de, per the sources
on `AlgWords`; any other tag reads English, exactly the caption-word
fallback W0368 already names for the locale record itself. -/
public def algWords (tag : String) : AlgWords :=
  match (tag.splitOn "-").headD tag with
  | "fr" =>
    { forKw := "pour", foreachKw := "pour chaque", whileKw := "tant que"
      doKw := "faire", ifKw := "si", thenKw := "alors"
      elseIfKw := "sinon si", elseKw := "sinon", repeatKw := "répéter"
      untilKw := "jusqu'à", endKw := "fin", returnKw := "retourner"
      inputKw := "Entrées", outputKw := "Sorties", dataKw := "Données"
      resultKw := "Résultat", functionKw := "Fonction"
      procedureKw := "Procédure" }
  | "de" =>
    { forKw := "für", foreachKw := "für jedes", whileKw := "solange"
      doKw := "tue", ifKw := "wenn", thenKw := "dann"
      elseIfKw := "sonst wenn", elseKw := "sonst", repeatKw := "wiederhole"
      untilKw := "bis", endKw := "Ende", returnKw := "zurück"
      inputKw := "Eingabe", outputKw := "Ausgabe", dataKw := "Daten"
      resultKw := "Ergebnis", functionKw := "Funktion"
      procedureKw := "Prozedur" }
  | _ =>
    { forKw := "for", foreachKw := "foreach", whileKw := "while"
      doKw := "do", ifKw := "if", thenKw := "then"
      elseIfKw := "else if", elseKw := "else", repeatKw := "repeat"
      untilKw := "until", endKw := "end", returnKw := "return"
      inputKw := "Input", outputKw := "Output", dataKw := "Data"
      resultKw := "Result", functionKw := "Function"
      procedureKw := "Procedure" }

/-- Every word a keyword table can generate, for the font-coverage
precompute: the faces must cover the generated keywords exactly as they
cover generated caption prefixes. -/
public def AlgWords.all (w : AlgWords) : List String :=
  [w.forKw, w.foreachKw, w.whileKw, w.doKw, w.ifKw, w.thenKw, w.elseIfKw,
   w.elseKw, w.repeatKw, w.untilKw, w.endKw, w.returnKw, w.inputKw,
   w.outputKw, w.dataKw, w.resultKw, w.functionKw, w.procedureKw]

/-- The opener's keyword pair: the word before the condition and the word
after it (`for … do`, `if … then`; `else` and `repeat` stand alone). -/
public def AlgOpen.words (w : AlgWords) : AlgOpen → String × Option String
  | .forLoop => (w.forKw, some w.doKw)
  | .forEach => (w.foreachKw, some w.doKw)
  | .whileLoop => (w.whileKw, some w.doKw)
  | .ifThen => (w.ifKw, some w.thenKw)
  | .elseIf => (w.elseIfKw, some w.thenKw)
  | .elseBranch => (w.elseKw, none)
  | .repeatLoop => (w.repeatKw, none)
  | .function => (w.functionKw, none)
  | .procedure => (w.procedureKw, none)

/-- The io line's label word. A `named` label is the author's declared
word, kept as declared. -/
public def AlgIo.word (w : AlgWords) : AlgIo → String
  | .input => w.inputKw
  | .output => w.outputKw
  | .data => w.dataKw
  | .result => w.resultKw
  | .named label => label

/-- The opener's dump spelling, for goldens. -/
public def AlgOpen.name : AlgOpen → String
  | .forLoop => "for"
  | .forEach => "foreach"
  | .whileLoop => "while"
  | .ifThen => "if"
  | .elseIf => "elseif"
  | .elseBranch => "else"
  | .repeatLoop => "repeat"
  | .function => "function"
  | .procedure => "procedure"

/-- The io kind's dump spelling, for goldens. -/
public def AlgIo.name : AlgIo → String
  | .input => "input"
  | .output => "output"
  | .data => "data"
  | .result => "result"
  | .named label => s!"named {label.quote}"

/-- The line kind's dump spelling, for goldens. -/
public def AlgKind.name : AlgKind → String
  | .statement => "statement"
  | .io k => s!"io {k.name}"
  | .opener o => s!"open {o.name}"
  | .closer o => s!"close {o.name}"
  | .ret => "return"

/-- The muted role's one resolving chain (`Design.ofDoc` reads the same
chain): the palette's `muted`, else its `fg`, else black — quieted
secondary ink. Spelled once so a walk reading the epoch palette in force
(algorithm comments, line numbers) resolves exactly as the document
design does. -/
public def mutedOf (pal : Palette) : Color :=
  (pal.find? "muted").getD ((pal.find? "fg").getD Color.black)

/-- One algorithm line as display inlines — the one site both backends
read, so the page and the HTML list item spell a line identically
(`algorithm_lines_agree` is the statement). Keywords set bold
(algorithm2e's `\KwSty` default `\textbf`); the comment sets in the muted
role between algorithm2e's own `/* … */` fences (`\tcc`'s default
comment style); `semis` closes statement, io and return lines with the
`;` algorithm2e prints for `\;` unless `\DontPrintSemicolon`. -/
public def AlgLine.rendered (w : AlgWords) (semis : Bool) (muted : Color)
    (l : AlgLine) : Array Inline := Id.run do
  let bold (s : String) : Inline := .styled .bold #[.text s]
  let mut out : Array Inline := #[]
  let mut semi := false
  match l.kind with
  | .statement =>
    out := l.content
    -- A statement whose content is only anchors (a `\label` line under
    -- the caption) shows no stray semicolon: the anchor ships, invisibly.
    semi := !l.content.all (· matches Inline.label _)
  | .io k =>
    out := #[bold (k.word w ++ ":"), .text " "] ++ l.content
    semi := true
  | .opener o =>
    let (lead, trail) := o.words w
    out := #[bold lead]
    unless l.content.isEmpty do
      out := out.push (.text " ") ++ l.content
    if let some t := trail then
      out := out ++ #[.text " ", bold t]
  | .closer o =>
    if o matches .repeatLoop then
      out := #[bold w.untilKw]
      unless l.content.isEmpty do
        out := out.push (.text " ") ++ l.content
      semi := true
    else
      out := #[bold w.endKw]
  | .ret =>
    out := #[bold w.returnKw]
    unless l.content.isEmpty do
      out := out.push (.text " ") ++ l.content
    semi := true
  if semi && semis then
    out := out.push (.text ";")
  if let some c := l.comment then
    unless out.isEmpty do
      out := out.push (.text " ")
    out := out.push (.colored muted (some "muted")
      (#[Inline.text "/* "] ++ c ++ #[Inline.text " */"]))
  return out

/-- Pad each table row to `n` cells with empty cells, the door elaboration
takes to the rectangularity `.table` declares. The same statement shape as
the alignment grid's `MRows.pad_rectangular` (one property, two
consumers), restated here because a table's cell is `Array Inline`, not a
math list. -/
public def padTableRows (rows : Array (Array (Array Inline))) (n : Nat) :
    Array (Array (Array Inline)) :=
  rows.map fun r => r ++ Array.replicate (n - r.size) #[]

/-- Padding conserves content exactly: each padded row is the original's
cells followed by empties — nothing dropped, nothing reordered. -/
public theorem padTableRows_cells (rows : Array (Array (Array Inline))) (n i : Nat)
    (h : i < rows.size) :
    (padTableRows rows n)[i]'(by simpa [padTableRows] using h)
      = rows[i] ++ Array.replicate (n - rows[i].size) #[] := by
  simp [padTableRows]

/-- A padded grid is rectangular: every row of `padTableRows rows n` has
exactly `n` cells when none had more — the invariant every walk over
`.table` trusts (`cols.size` is every row's size), sourced from the same
need as the alignment grid's: a column's alignment point is one x for
every row. -/
public theorem padTableRows_rectangular (rows : Array (Array (Array Inline))) (n : Nat)
    (h : ∀ r ∈ rows, r.size ≤ n) :
    ∀ r ∈ padTableRows rows n, r.size = n := by
  intro r hr
  rw [padTableRows, Array.mem_map] at hr
  obtain ⟨r0, hmem, rfl⟩ := hr
  have hle := h r0 hmem
  simp [Array.size_append]
  omega

/-- A pinned-to-the-viewport placement for a web element: CSS
`position: fixed` with a declared corner and offset (CSS Positioned Layout
Module Level 3 §3.3: a fixed-positioned box is attached to the viewport).
A printed page has no viewport, so the PDF and the markdown twin ignore a
pin by construction — their walks read the nav's body only (said once
here, not per consumer). `reveal` keeps the element hidden until the page
has scrolled past `revealBy` (undeclared: one viewport). The engine's
reveal changes opacity and visibility only — a fade, not motion, so it
needs no reduced-motion form (WCAG 2.2 SC 2.3.3 covers motion animation);
a declared `motion` style key stays the way to animate it, with its guard.
An undeclared offset is 0 — the exact corner — which is the identity, not
a design constant; declare one to stand off the edge. -/
public structure Pin where
  /-- `true` pins to the top edge, `false` to the bottom. -/
  top : Bool
  /-- `true` pins to the left edge, `false` to the right. -/
  left : Bool
  offset : SymGlue := {}
  reveal : Bool := false
  revealBy : Option SymGlue := none
  deriving Repr, BEq, Inhabited

/-- What a `{nav}` landmark declares about itself, beside its body.
`label` names the landmark instance (`aria-label`): a landmark role used
more than once on a page needs a unique label per instance (W3C ARIA
Authoring Practices, Landmark Regions), and W0325 counts only unlabeled
navs. `pin` is the pinned placement above. -/
public structure NavSpec where
  label : Option String := none
  pin : Option Pin := none
  deriving Repr, BEq, Inhabited

/-- One reference-list entry, resolved: its key (the HTML anchor and what
`\cite` spells), the marker the style shows beside it (the position for a
numeric style, nothing for author-year lists, which mark no entries), and
its content formatted per the style. `Bib.apply` builds these; a backend
only structures them. -/
public structure BibItem where
  key : String
  marker : Option String
  content : Array Inline
  deriving Repr, BEq, Inhabited

/-- The titled block's kind, closed: beamer's three block environments
(`{block}`, `{alertblock}`, `{exampleblock}` — beamer user guide §12.3,
"Highlighting"), and tcolorbox's box, which its lowering sets through the
same surface (`Tcolorbox.lower`). The kind selects the role pair the title
resolves through (`titledLook`, the box the plain block's: `roleStem`)
and the box the block stands in: beamer's two colour boxes for the three,
tcolorbox's frame for the box — a poster and a deck set the same node at
different base sizes. -/
public inductive TitledKind where
  | block
  | alert
  | example
  | box
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The kind's one spelling: the HTML class suffix, one naming site for both
backends and the dump. -/
public def TitledKind.name : TitledKind → String
  | .block => "block"
  | .alert => "alert"
  | .example => "example"
  | .box => "box"

/-- The role-key stem the kind's colours resolve through (`alerttitlefg`):
tcolorbox's box takes the plain block's roles, where its lowering declares
its colours. -/
public def TitledKind.roleStem : TitledKind → String
  | .block | .box => "block"
  | .alert => "alert"
  | .example => "example"

/-- The token grammar a listing's declared language must fit before either
text artifact may carry it: an ASCII lowercase letter, then lowercase
letters, digits, `+`, `#`, `-`, `.` — `python`, `c++`, `c#`, `objective-c`.
Small on purpose: the token lands in an HTML class attribute and in a
CommonMark fence info string (§4.5: no backtick), and a spelling outside
the grammar — listings' `[LaTeX]TeX` dialect form, a space, a brace — is
named at elaboration and reaches neither, never as raw attribute text. -/
public def listingLangOk (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest =>
    c.isLower && rest.all fun d =>
      d.isLower || d.isDigit || d == '+' || d == '#' || d == '-' || d == '.'

/-- A listing language the grammar admits: the IR cannot hold a token
`listingLangOk` rejects, so every construction is validated by its type.
`listingLang?` is the one site that mints one from an author's spelling. -/
public abbrev ListingLang := { s : String // listingLangOk s = true }

/-- An author's language spelling normalized to the token both artifacts
carry: trimmed, ASCII-lowercased (`Python` and `python` name one language,
as listings' case-insensitive `language=` key does), and admitted only when
the grammar holds — `none` names the spelling the caller diagnoses. -/
public def listingLang? (raw : String) : Option ListingLang :=
  let s := raw.trimAscii.toString.toLower
  if h : listingLangOk s = true then some ⟨s, h⟩ else none

/-- The Pygments styles a listing may select, each painted from its own
table (`PygmentsStyleData`, resolved by `PygmentsStyle`), independent of
lexical classification. Pygments style names are case-sensitive;
unsupported names remain a frontend option diagnostic, never an implicit
default selection. -/
public inductive ListingStyle where
  | default
  | friendly
  deriving Repr, BEq, Inhabited

/-- The style's Pygments name, the one spelling a document selects it by. -/
public def ListingStyle.name : ListingStyle → String
  | .default => "default"
  | .friendly => "friendly"

public def ListingStyle.all : List ListingStyle := [.default, .friendly]

public theorem ListingStyle.all_complete (s : ListingStyle) : s ∈ ListingStyle.all := by
  cases s <;> simp [ListingStyle.all]

public def ListingStyle.ofName? (name : String) : Option ListingStyle :=
  let name := name.trimAscii.toString
  ListingStyle.all.find? (·.name == name)

/-- What a code listing declares beside its content — the delta between
`{verbatim}` and listings' `{lstlisting}` / minted's `{minted}` (listings
manual: the `caption` key, lstmisc's `numbers` key; minted's `linenos`).
`caption` carries the resolved number with the declared text: every
captioned listing numbers, assigned at elaboration in flow order exactly
as equation numbers are (listings steps `\thelstlisting` per captioned
listing); a captionless listing is `none`, unnumbered. The number rides
beside the declared text, never inside it — the "Listing n: " prefix is
backend furniture spelled at `Ir.listingCaption`, one site for both
artifacts. `numbers` is `numbers=left` / `linenos`: each line's number as
furniture beside it, generated ink outside the census as a list's markers
are. `language` is listings' `language=` key or minted's mandatory
argument, normalized (`listingLang?`): one fact the HTML `code` element's
class and the markdown fence's info string both project (`htmlClass`,
`fenceInfo`, `listing_language_agree`). `highlight` holds Pygments token
types, assigned once during elaboration; both backends consume the same
segments. A bare `{verbatim}` is the default value everywhere. -/
public structure ListingSpec where
  /-- Authentic source start for diagnostics on listing lines and tokens.
  It does not participate in highlighting, sizing, or backend emission. -/
  source : Option Span := none
  caption : Option (Nat × Array Inline) := none
  numbers : Bool := false
  language : Option ListingLang := none
  /-- Both backends pass this value to the one shared token painter. -/
  style : ListingStyle := .default
  /-- One segment array per normalized source line. Empty means plain text.
  `tokenLines` validates the text before either backend consumes this cache. -/
  highlight : Array (Array ListingHighlight.Token) := #[]
  /-- Resolved size declaration, using the ordinary size resolving sites.
  Bare `verbatim` inherits the ambient size in force (LaTeX's
  `\verbatim@font` is `\normalfont\ttfamily`: mono family, no size change);
  minted/listings inherit it too unless their options select a named LaTeX
  step. The default is the body size — the neutral ambient — so a spec
  built with no elaboration context never forces a size of its own. -/
  fontSize : Style := .size "normalsize"
  /-- FancyVerb/listings default: eight columns between tab stops. -/
  tabSize : Nat := 8
  /-- FancyVerb/listings default: source lines do not wrap. -/
  breakLines : Bool := false
  /-- Every code line carries a `\strut`, so its box is that strut's at
  least, whatever its glyphs: minted's lines under `breaklines`, which
  fvextra sets each as `\parbox[t]{…}{\noindent\strut … \strut}`
  (`\FV@ListProcessLine@Break`). Its unbroken lines are bare `\hbox`es,
  their glyphs' boxes, as verbatim's are. A colour box around the code ends
  on the last line's box. -/
  lineStrut : Bool := false
  deriving Repr, BEq, Inhabited

/-- The declared language as the bare token, `none` when none is declared:
the one IR fact both text projections below read. -/
public def ListingSpec.langToken (spec : ListingSpec) : Option String :=
  spec.language.map (·.val)

/-- The HTML projection of the declared language: the `code` element's
class under the HTML standard's own convention (§4.5.15 `code`: a class
prefixed `language-` names the computer language). `none` when no language
is declared — the element then carries no class at all. -/
public def ListingSpec.htmlClass (spec : ListingSpec) : Option String :=
  spec.langToken.map ("language-" ++ ·)

/-- The markdown projection of the declared language: the fenced code
block's info string (CommonMark §4.5), empty when no language is declared —
the fence then opens bare. -/
public def ListingSpec.fenceInfo (spec : ListingSpec) : String :=
  spec.langToken.getD ""

/-- One declared language, two projections of one IR value: a declared
token reaches the HTML class as `language-<token>` and the markdown info
string as the token itself; an absent language reaches neither. Both
backends read `htmlClass` and `fenceInfo` and nothing else, so an artifact
that carried a language the other did not is unrepresentable. -/
public theorem listing_language_agree (spec : ListingSpec) :
    (spec.language = none → spec.htmlClass = none ∧ spec.fenceInfo = "") ∧
    (∀ l, spec.language = some l →
      spec.htmlClass = some ("language-" ++ l.val) ∧ spec.fenceInfo = l.val) := by
  constructor
  · intro h
    simp [ListingSpec.htmlClass, ListingSpec.fenceInfo, ListingSpec.langToken, h]
  · intro l h
    simp [ListingSpec.htmlClass, ListingSpec.fenceInfo, ListingSpec.langToken, h]

public inductive Block where
  | para (content : Array Inline)
  /-- A heading. `number` is the section's resolved number ("2", "2.1",
  "A.2" after `\appendix`), assigned at elaboration in flow order — article
  numbers unstarred levels 1–3 (classes.dtx §Sectioning, secnumdepth 3);
  slides and card documents, and every starred form, carry `none`. The
  number rides beside the title, never inside it, so a backend renders it
  as its own structural piece (classes.dtx's `\@seccntformat`: number then
  `\quad`) and the HTML anchor still derives from the title text alone —
  numbering a section must not move its anchor. -/
  | section (level : HeadingLevel) (starred : Bool) (number : Option String) (title : Array Inline)
  | list (ordered : Bool) (items : Array (Array Block))
  | center (body : Array Block)
  /-- Unjustified setting for a scope, hanging from the side it declares.
  Flush left is `\flushleft` and `\raggedright`'s meaning (ltmiscen.dtx:
  `{flushleft}` is a trivlist under `\raggedright`); flush right is
  `{flushright}`/`\raggedleft`'s. The lines break ragged on the other edge;
  with `center` these are the alignments a page can declare per block, and
  the side rides here because line placement resolves an origin
  (`Layout.Geom.flushRight`) that a direction-free node could not name. -/
  | ragged (flush : FlushSide) (body : Array Block)
  /-- `\block[before = <len>]{...}`: content with declared space above.
  The glue rides as `Sourced` so a token-declared gap reaches the HTML
  with the name a reader would override (`var(--subtitlegap, …)`); a
  computed or class-default gap carries `none`. -/
  | spaced (before : Sourced SymGlue) (body : Array Block)
  /-- The block half of `Inline.role`: a document-defined command whose
  expansion is block content (`\entry{...}` producing whole paragraphs)
  keeps its authored name the same way — `<div class="u-name">` in HTML,
  a transparent group everywhere else. -/
  | role (name : String) (body : Array Block)
  /-- One hyperlink over block-shaped content. HTML's anchor has a
  transparent content model and may wrap flow content, but may contain no
  interactive descendant; elaboration refuses that nesting before this node
  is built. The paged backend records one rectangle over the body's placed
  ink on each page the body reaches, since a PDF annotation belongs to one
  page. -/
  | link (target : String) (body : Array Block)
  /-- `{quote}`/`{quotation}`: a quotation set off from the text by
  indenting both margins by the list indent — classes.dtx defines both as
  `\list{}{\rightmargin\leftmargin}`, so the right edge moves in exactly as
  far as the left. The two environments differ only in
  `\listparindent` (`quotation` indents each paragraph's first line
  1.5 em); the engine sets no paragraph indent anywhere yet, so that
  distinction has nothing to bind to and one node carries both. HTML sets
  it as `<blockquote>`, markdown as `> ` lines. -/
  | quote (body : Array Block)
  /-- `{abstract}`: article's unnumbered titled block — `\small`, a centred
  bold "Abstract" heading, then the body on quotation margins (article.cls
  §abstract: `\small`, `\begin{center}{\bfseries\abstractname}\end{center}`,
  `\quotation`). Its own node rather than a `.quote`, because the backends
  express it differently: HTML sets a `<section class="abstract">` with a
  heading — exactly the region a reader's tooling looks for — while the PDF
  keeps the class's quotation shape. -/
  | abstract (body : Array Block)
  /-- beamer's titled block (`{block}`/`{alertblock}`/`{exampleblock}`,
  user guide §12.3): the `{title}` group on the `\begin` line, block
  content under it. An empty title is beamer's untitled block — no title
  bar, the body alone. The title's colours resolve through the kind's
  role pair (`titledLook`, following beamer's own parent chain:
  beamercolorthemedefault.sty defines `block title` on structure,
  `block title alerted` on alerted text, `block title example` on
  example text, `block body` empty); a declared `<kind>titlebg` turns
  the title into a colour bar, exactly the frame-title rule. -/
  | titled (kind : TitledKind) (title : Array Inline) (body : Array Block)
  /-- A numbered display equation: `{equation}` under amsmath's numbering
  conventions (amsldoc §3 — `equation` numbers, `equation*` and `\[` do
  not, `\nonumber`/`\notag` opts a numbered form out). `number` is the
  rendered tag, parentheses included (`(1)`), assigned per document at
  elaboration, or an author's `\tag` elaborated as text the way amsmath's
  `\tagform@` sets it (`\hbox{\normalfont(#1)}`: markup and math inside it
  are ink, never source); `content` is the formula — or its source-text
  degradation — preceded by the `\label` anchors the environment carried.
  The number is structural in both backends: right-aligned beside the
  centred formula on the page, its own element in HTML, never text glued
  into the formula. The unnumbered forms keep the plain centred-paragraph
  shape. -/
  | equation (number : Array Inline) (content : Array Inline)
  /-- `{verbatim}` content, kept literally: lines, spaces, and all. Both
  backends set it in the mono face and neither reflows it. `covered` is the
  dim colour painted by the overlay shade — code pending its step must read
  as covered like any other text; `none` everywhere else. `spec` is what a
  listing environment declares beside the content (`ListingSpec`): the
  numbered caption and the line-number flag. -/
  | verbatim (covered : Option Color) (content : String) (spec : ListingSpec)
  /-- Pseudocode as a value: the lines of an `{algorithm}`/`{algorithmic}`
  environment, algorithm2e and algorithmicx parsed onto this one node.
  Lines are rich text with math and generated bold keywords, nested by
  `depth`; the keywords are the locale table's (`algWords`), generated by
  `AlgLine.rendered` — the one site both backends read. `numbered` is
  algorithm2e's `\LinesNumbered` (off by default) or algorithmic's `[1]`;
  `semis` prints the `;` each `\;` terminates (on by default,
  `\DontPrintSemicolon` clears it) — both from algorithm2e's own default
  option set (`\ExecuteOptions{english,plain,resetcount,titlenotnumbered,
  lined,shortend}`, algorithm2e.sty). The node usually stands inside a
  `.float` of kind `.algorithm`, which carries the caption and the
  number; a bare `{algorithmic}` stands alone, uncaptioned. -/
  | algorithm (numbered : Bool) (semis : Bool) (lines : Array AlgLine)
  /-- Side-by-side boxes (`{columns}`/`{column}`, and the one-box forms
  `{minipage}` and `\parbox`): each carries its declared width as a
  `BoxWidth` — a fraction of the enclosing measure, an absolute length, or
  `share` for a `{column}` that declares none and takes an equal part of the
  leftover. Boxes are top-aligned; the alignment options are not modelled
  (PLAN, M5). -/
  | columns (cols : Array (BoxWidth × Array Block))
  /-- Overlay blocks crisp on steps `n` through `last` (`\item<2->`,
  `\pause`): the block form of `Inline.step`, with the same dim-not-hide
  semantics. -/
  | onSteps (spec : OverlaySpec) (body : Array Block)
  /-- Block-level overlay alternation: the block form of `Inline.alt`, with
  the same select-one-per-step semantics, the same page-order storage, and
  the same reasons. -/
  | altSteps (spec : OverlaySpec) (firstPage : Array Block)
      (otherPage : Array Block)
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
  (E0334), and `keepFor_covers` is the conservation theorem that makes the
  diagnostic sufficient: with every conditional answered, no declared text
  leaf is dropped by every backend. -/
  | only (targets : Array String) (body : Array Block)
  /-- `{nav}`: a navigation landmark — a group of links for page or site
  navigation, not a widget. HTML emits it as the `<nav>` element (the
  `navigation` landmark, W3C ARIA Authoring Practices, Landmark Regions);
  the PDF page and the markdown twin have no landmark to mark, so both keep
  the body as a transparent group. -/
  | nav (spec : NavSpec) (body : Array Block)
  /-- beamer's `\logo`, met in the body: a stateful declaration — the pages
  from here on carry this content at their lower-right corner, and an empty
  content clears it (`\logo{}` after a frame is how a deck scopes a logo to
  one frame). The preamble form is `Doc.logo`, the initial state. -/
  | logo (content : Array Inline)
  /-- `\pagebreak`/`\newpage`: a declared page boundary. The PDF opens a
  fresh page (two adjacent boundaries never make a blank one — the builder
  closes only pages that hold something); HTML and markdown are continuous
  media with no page to break, so both keep nothing, and the node ships no
  ink of its own. -/
  | pagebreak
  /-- One slide. First-class and never flattened into article paragraphs:
  HTML makes it a `<section>` of the deck, the PDF handout gives it a page.
  An empty title is a bare frame. `standout` is beamer's `[standout]`: the
  frame inverts (`standoutfg` on `standoutbg`, defaulting to the inverse of
  the page), centres, and sets Large bold. `valign` is the frame's declared
  vertical distribution (`[t]`/`[c]`/`[b]`; `center` unless declared).
  `breakable` is beamer's `[allowframebreaks]`: the author has declared
  that content taller than one page continues on the next, so a
  continuation page of this frame is not a loss to report; a frame
  without it that continues is (`Layout.spill_accounts`). -/
  | frame (title : Array Inline) (standout : Bool) (valign : VAlign) (breakable : Bool)
      (body : Array Block)
  /-- `\framefoot{...}` (beamer's `frame footer` template): the footer note
  the frames from here on carry in the chrome footer's left slot, beside
  the frame number. Empty content clears it back to the chrome default. -/
  | framefoot (content : Array Inline)
  /-- Body `\palette`: a stateful declaration in flow order, carrying the
  full palette state in force from here on (preamble + theme + every body
  declaration up to and including this one — elaboration merges, backends
  only replay). Flow scope, no brace revert: the engine's `\centering`
  choice, and what `\logo`/`.framefoot` already do. Layout swaps the
  accumulator's palette (and the default ink derived from it) at the
  block; HTML opens an epoch container redefining the changed custom
  properties. The node ships no ink of its own. -/
  | setPalette (pal : Palette)
  /-- Body `\tokens` (`\setlength` mid-document): the token state in force
  from here on, the same stateful door as `.setPalette`. -/
  | setTokens (tokens : Tokens)
  /-- A full-measure horizontal rule: the title page's separator. `name` is
  the palette entry the colour came from, when it had one, as `.colored`;
  the thickness is symbolic so a token may state it in em, and `Sourced`
  so the token's name travels with it — the colour's name always did,
  which is why `separator` was readable from a stylesheet and
  `separatorheight` was not. -/
  | rule (color : Color) (name : Option String) (thickness : Sourced SymGlue)
  /-- An elaborated `tikzpicture` subset: concrete shapes in picture
  coordinates, everything evaluated at elaboration (loops unrolled,
  expressions reduced, colours resolved, `scale=` applied). Layout places
  the box and transforms shapes through `Pic.Place`; a construct outside
  the subset never reaches here — it is diagnosed by name where it stood
  (W0334/E0333), so nothing a picture declares goes silently missing. -/
  | picture (pic : Pic.Picture)
  /-- `{tabular}`: a formal table, booktabs-shaped by construction — three
  rule weights with their padding, no vertical rules ever ("Never, ever use
  vertical rules", booktabs.dtx §The layout of formal tables; a `|` in the
  spec warns and is not drawn). `rows` is rectangular: elaboration pads a
  short row and widens the grid for a long one, warning either way (W0337),
  so every walk below may trust `cols.size`. `rules` are drawn before the
  content row of their index (`rows.size` = after the last); order within
  one index is document order. `padLeft`/`padRight` are the outer
  `tabColSep` pads, deleted by `@{}` as in LaTeX. `spans` are the
  `\multicolumn` cells (`ColSpan`); the cells they cover are empty in `rows`. -/
  | table (cols : Array ColSpec) (padLeft : Bool) (padRight : Bool)
      (rows : Array (Array (Array Inline))) (rules : Array (Nat × TableRule))
      (spans : Array ColSpan)
  /-- `{figure}`/`{table}`: a captioned object. A single-pass engine has
  nowhere for a float to float, so it stands where written, centred, set
  off from the text by `floatsep` with its caption bound `captionsep` from
  it (`caption_gaps_rhythm` holds the defaults to the rhythm). `capAbove`
  is source order: a `\caption` written before the content stands above
  it, the convention for tables. An empty caption is a bare float. `num`
  is the float's number among captioned floats of its kind — none until
  `numberFloats` assigns it, and none forever for a captionless float:
  LaTeX steps the counter in `\caption` (classes.dtx, `\caption` calls
  `\refstepcounter`), so a float without one bears no number. A `.sub`
  float's `num` is its letter index within its parent (subcaption:
  `\thesubfigure` is `(\alph{subfigure})`). -/
  | float (kind : FloatKind) (num : Option Nat) (capAbove : Bool) (body : Array Block)
      (caption : Array Inline)
  /-- `\bibliography{src}`: the reference list, standing where the command
  was written. Elaboration emits the marker with no items — the `.bib`
  beside the document is the driver's effect (`bibRefs`, the `imageRefs`
  shape) — and `Bib.apply` fills `items` with the cited entries in the
  style's order. `style` is the declared `\bibliographystyle`, kept as
  written so resolution can select the record (W0353 names an unknown one
  and falls back). An unfilled marker ships nothing: the missing file was
  already a diagnostic. -/
  | bibliography (src : String) (style : Option String) (items : Array BibItem)
  deriving Repr, BEq, Inhabited

/-- Single-interval construction; union nodes use `onSteps` directly. -/
@[match_pattern, expose] public def Block.step (n : Nat) (last : Option Nat) (body : Array Block) : Block :=
  .onSteps ⟨n, last, []⟩ body

/-- Single-interval alternation, with the same page-order storage. -/
@[match_pattern, expose] public def Block.alt (n : Nat) (last : Option Nat)
    (firstPage otherPage : Array Block) : Block :=
  .altSteps ⟨n, last, []⟩ firstPage otherPage

/-- Block alternatives use the same source-order bridge as inline ones. -/
public def Block.alternate (spec : OverlaySpec) (active otherwise : Array Block) : Block :=
  let (firstPage, otherPage) := spec.pageOrder active otherwise
  .altSteps spec firstPage otherPage

/-- Classify a display region without treating source annotations as
content. `none` means another semantic inline was present; `some seen`
records whether a formula was found among labels and empty annotations.
Only diagnostic wrappers are traversed: a style or link still changes the
semantic shape, so the general all-descendants fold is not this reader. -/
-- conserves: none — a classifier; emits no document text.
public def displayParts : List Inline → Bool → Option Bool
  | [], seen => some seen
  | .formula true _ _ :: rest, _ | .math true _ :: rest, _ => displayParts rest true
  | .label _ :: rest, seen => displayParts rest seen
  | .located _ body :: rest, seen =>
    (displayParts body.toList seen).bind (displayParts rest)
  | _ :: _, _ => none
termination_by xs _ => sizeOf xs
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    have hb : sizeOf body = 1 + sizeOf body.toList := rfl
    omega

/-- A source wrapper around an arbitrary region leaves its display reading
unchanged, including nested annotations, labels and empty bodies. -/
public theorem displayParts_location_exact (span : Span) (body : Array Inline) (seen : Bool) :
    displayParts [.located span body] seen = displayParts body.toList seen := by
  simp only [displayParts]
  cases displayParts body.toList seen <;> simp [displayParts]

/-- Is this inline a display formula — `\[…\]`, `{equation*}`, an
alignment — whether modelled or carried as source? -/
public def Inline.isDisplayFormula (x : Inline) : Bool :=
  displayParts [x] false == some true

/-- The environments `\@trivlist` spaces with `\partopsep` in vertical
mode, as this engine sets them: a list, a quote, and the kernel's theorem,
which is `\trivlist` itself (amsthm's spellings open with `\par`, so their
mode is always vertical, and their space reads none of it: `thmSkips`). -/
public def Block.partopsepEnv : Block → Bool
  | .list .. | .quote _ => true
  | .role n _ => n == thmSpaceRole .kernel
  | _ => false

/-- A block whose end leaves TeX's `\@endpe` set (ltlists.dtx `\endtrivlist`,
`\@doendpe`): a list, a quote, or any theorem-like trivlist. When a display
opens a paragraph right after one — in vertical mode, possibly across a
`\vspace` or a blank line but no intervening paragraph of text — the opening
`\everypar` takes the indent box back, so TeX sets no empty line. One level
of the in-paragraph wrapper (`inParagraphRole`) is seen through, as that is
how a list opened mid-paragraph stands in the block stream. -/
public def Block.leavesEndPe : Block → Bool
  | .list .. | .quote _ => true
  | .role n body =>
    (thmSpaceOf? n).isSome ||
      (n == inParagraphRole && match body with
        | #[.list ..] | #[.quote _] => true
        | #[.role m _] => (thmSpaceOf? m).isSome
        | _ => false)
  | _ => false

/-- A list or a quote marked as opened inside a paragraph
(`inParagraphRole`). Anything else stands as it is. -/
public def inParagraph (b : Block) : Block :=
  if b.partopsepEnv then .role inParagraphRole #[b] else b

/-- A block that is a page-model mark: an empty block in a
`pageMarkerRole`. -/
@[expose] public def pageMarkerBlock : Block → Bool
  | .role n body => body.isEmpty && pageMarkerRole n
  | _ => false

/-- Mark the block an environment arm pushed past `k` as opened inside a
paragraph (`inParagraph`) when `inPar` says the paragraph flushed just
before it had text; the census stands (`markInParagraph_text`). -/
public def markInParagraph (inPar : Bool) (k : Nat) (blocks : Array Block) : Array Block :=
  match inPar && blocks.size == k + 1, blocks.back? with
  | true, some b => blocks.pop.push (inParagraph b)
  | false, _ => blocks
  | true, none => blocks

/-- Did flushing the open paragraph leave one with text — anything but
label anchors, which ship no ink and keep TeX in vertical mode — as the
last of `after`, past the `k` blocks that stood before? -/
public def flushedText (k : Nat) (after : Array Block) : Bool :=
  k < after.size &&
    match after.back? with
    | some (.para content) => !content.all (· matches .label _)
    | _ => false

/-- A description item's first paragraph read at its label (`descLabelRole`,
whose body closes with the `\labelsep` separator): the label and the text
after it; `none` for any other paragraph. The one reading both backends
use, so the page's run-in label and HTML's `<dt>` are the same inlines. -/
public def descLabel? (content : Array Inline) : Option (Array Inline × Array Inline) :=
  match content[0]? with
  | some (Inline.role n label) =>
    if n == descLabelRole then some (label, content.extract 1 content.size) else none
  | _ => none

/-- A centred block's body that is one display formula and nothing else,
labels aside — the shape `\[…\]` and the unnumbered display environments
elaborate to (`.center #[.para content]`), and the one reading both
backends share when they open the display skips around it: `Layout`'s
display arm pays `displayAbove`/`displayBelow` as its own space, and the
HTML backend emits the `.display` element the base sheet's display rules
address. A display formula standing among text (a caption's, an item
label's) is inline content and opens nothing here — as a numbered
`.equation` is its own block and opens the same skips at its own arm. -/
public def displayContent? (body : Array Block) : Option (Array Inline) :=
  match body.toList with
  | [.para content] =>
    if displayParts content.toList false == some true then
      some content
    else none
  | _ => none

/-- The display reading is a projection of the body: what it returns is the
centred paragraph's own content, so the leaves both backends set are the
leaves `Struct` counts — no content is invented or dropped at the seam. -/
public theorem displayContent_projects (body : Array Block) (content : Array Inline)
    (h : displayContent? body = some content) : body.toList = [.para content] := by
  unfold displayContent? at h
  split at h
  · rename_i heq
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact heq
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A display: the unnumbered shape (`displayContent?`) or a numbered
equation. -/
public def Block.isDisplay : Block → Bool
  | .center body => (displayContent? body).isSome
  | .equation .. => true
  | _ => false

/-- The context a display block carries (`DisplayCtx.role`) with the display
itself; an unwrapped display carries the default. -/
public def displayCtxOf (b : Block) : DisplayCtx × Block :=
  match b with
  | .role n body => match DisplayCtx.ofRole? n, body.toList with
    | some c, [d] => (c, d)
    | _, _ => ({}, b)
  | _ => ({}, b)

/-- Record where the display an arm pushed past `k` stands in its paragraph
(`DisplayCtx`): whether the paragraph flushed just before it had text,
whether a paragraph break follows, and whether it opens right after an
environment end (`afterEnv`, the `\@endpe` state). A display in the default
context stays unwrapped; anything else pushed stands as it is. -/
public def markDisplay (inPar parEnd afterEnv : Bool) (k : Nat) (blocks : Array Block) : Array Block :=
  match blocks.size == k + 1, blocks.back? with
  | true, some b =>
    let (c, d) := displayCtxOf b
    if !d.isDisplay then blocks else
    let c := { c with inPar, parEnd, afterEnv }
    blocks.pop.push (if c == {} then d else .role c.role #[d])
  | _, _ => blocks

/-- The frames the deck numbers: every `.frame` except a golden title page.
The title is front matter; a standout is content whose footer is hidden,
so it advances the same counter as any other content frame. Footer
visibility is selected separately by `Chrome.frameFootBand`. The k-th
countable frame in document order bears number k — the fold below —
and a non-countable frame bears none. -/
public def Block.countable : Block → Bool
  | .frame _ _ valign _ _ => !(valign matches .golden)
  | _ => false

/-- Count of `true` in a mask: the numbering's denominator. -/
public def countTrue : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + countTrue rest

/-- The numbering fold: masked positions take k+1, k+2, …; the rest take
none. One definition site for every frame number the engine ever shows —
both backends read this array, and nothing else counts. -/
public def numbersFrom (k : Nat) : List Bool → List (Option Nat)
  | [] => []
  | b :: rest =>
    if b then some (k + 1) :: numbersFrom (k + 1) rest
    else none :: numbersFrom k rest

/-- The somes of the fold are exactly `1..countTrue`: the numbering is
monotone and gapless, whatever the mask. -/
public theorem numbers_gapless (k : Nat) (bs : List Bool) :
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
public theorem numbers_le_total (bs : List Bool) (n : Nat)
    (h : n ∈ (numbersFrom 0 bs).filterMap id) : n ≤ countTrue bs := by
  rw [numbers_gapless] at h
  have := List.mem_range'.mp h
  omega

/-- The last number is the total: the denominator is reached. -/
public theorem last_number_is_total (bs : List Bool) (h : 0 < countTrue bs) :
    ((numbersFrom 0 bs).filterMap id).getLast? = some (countTrue bs) := by
  obtain ⟨m, hm⟩ : ∃ m, countTrue bs = m + 1 :=
    ⟨countTrue bs - 1, (Nat.succ_pred_eq_of_pos h).symm⟩
  rw [numbers_gapless, hm, List.range'_concat, List.getLast?_concat]
  exact congrArg some (by omega)

/-- A position is numbered exactly when its mask bit is set. -/
public theorem numbersFrom_isSome (k : Nat) (bs : List Bool) (i : Nat) :
    ((numbersFrom k bs)[i]?.getD none).isSome = (bs[i]?.getD false) := by
  induction bs generalizing k i with
  | nil => rfl
  | cons b rest ih =>
    cases i with
    | zero => cases b <;> simp [numbersFrom]
    | succ n => cases b <;> simp [numbersFrom, ih]

public theorem numbersFrom_length (k : Nat) (bs : List Bool) :
    (numbersFrom k bs).length = bs.length := by
  induction bs generalizing k with
  | nil => rfl
  | cons b rest ih => cases b <;> simp [numbersFrom, ih]

/-- One footnote mark's number against the counter: an override
(`\footnote[n]{...}`) is itself and steps nothing — LaTeX's own semantics,
where the optional argument sets the mark without `\stepcounter` (source2e,
ltmiscen.dtx `\@xfootnote`) — and an ordinary mark takes the next value.
The elaborator's per-mark step; `footnoteMarksFrom` is its fold and
`footnote_numbers_gapless` its contract. -/
public def footnoteMark (k : Nat) (override : Option Nat) : Nat × Nat :=
  match override with
  | some n => (n, k)
  | none => (k + 1, k + 1)

/-- The footnote numbering fold: `footnoteMark` over the marks' overrides
in flow order — what running the elaborator's step over a whole document
assigns. -/
public def footnoteMarksFrom (k : Nat) : List (Option Nat) → List Nat
  | [] => []
  | o :: rest => (footnoteMark k o).1 :: footnoteMarksFrom (footnoteMark k o).2 rest

/-- Footnote marks in flow order are gapless: over any override pattern,
the unoverridden marks number `k+1, k+2, …` exactly — `numbers_gapless`
instantiated at the footnote counter's step. An override never steps, so
`\footnote{a}\footnote[7]{b}\footnote{c}` numbers 1, 7, 2. -/
public theorem footnote_numbers_gapless (k : Nat) (os : List (Option Nat)) :
    ((os.zip (footnoteMarksFrom k os)).filterMap fun p =>
        if p.1.isSome then none else some p.2) =
      List.range' (k + 1) (countTrue (os.map (·.isNone))) := by
  have h : ∀ k, ((os.zip (footnoteMarksFrom k os)).filterMap fun p =>
      if p.1.isSome then none else some p.2) =
    (numbersFrom k (os.map (·.isNone))).filterMap id := by
    induction os with
    | nil => intro k; rfl
    | cons o rest ih =>
      intro k
      cases o <;> simp [footnoteMarksFrom, footnoteMark, numbersFrom, ih]
  rw [h, numbers_gapless]

/-- The countable mask of a document body: the fold's instantiation. -/
private def frameMask (body : Array Block) : List Bool :=
  body.toList.map Block.countable

/-- The frame number each top-level block bears: `some k` for the k-th
countable frame, `none` for everything else. THE numbering — the chrome
footer, the progress bar, and the HTML deck all index this array; a new
count consumer reads it, never counts for itself. -/
public def frameNumbers (body : Array Block) : Array (Option Nat) :=
  (numbersFrom 0 (frameMask body)).toArray

/-- The numbering's denominator: how many countable frames the body has. -/
public def frameCount (body : Array Block) : Nat :=
  countTrue (frameMask body)

/-- T2, numbered iff countable: position i bears a number exactly when
block i is a countable frame. -/
public theorem frameNumbers_numbered_iff_countable (body : Array Block) (i : Nat) :
    ((frameNumbers body)[i]?.getD none).isSome =
      ((body[i]?.map Block.countable).getD false) := by
  have h := numbersFrom_isSome 0 (frameMask body) i
  simpa [frameNumbers, frameMask, List.getElem?_map] using h

/-- T3, monotone and gapless: the numbers assigned, in document order, are
exactly `1, 2, …, frameCount`. -/
public theorem frameNumbers_gapless (body : Array Block) :
    (frameNumbers body).toList.filterMap id =
      List.range' 1 (frameCount body) := by
  simpa [frameNumbers, frameCount] using numbers_gapless 0 (frameMask body)

/-- T4a: every number the engine can show is ≤ the denominator — the
`min`/`max` clamps around a progress fraction cannot fire. -/
public theorem frameNumbers_le_count (body : Array Block) (n : Nat)
    (h : n ∈ (frameNumbers body).toList.filterMap id) : n ≤ frameCount body := by
  exact numbers_le_total (frameMask body) n (by simpa [frameNumbers] using h)

/-- T4b: the denominator is reached — the last numbered frame bears
`frameCount` itself, so a full deck ends at n/n, never n−1/n. -/
public theorem frameNumbers_last_is_count (body : Array Block)
    (h : 0 < frameCount body) :
    ((frameNumbers body).toList.filterMap id).getLast? =
      some (frameCount body) := by
  simpa [frameNumbers, frameCount] using
    last_number_is_total (frameMask body) (by simpa [frameCount] using h)

public theorem frameNumbers_size (body : Array Block) :
    (frameNumbers body).size = body.size := by
  simp [frameNumbers, frameMask, numbersFrom_length]

-- Float numbering. LaTeX steps a float's counter inside `\caption`
-- (classes.dtx: `\caption` is `\refstepcounter` then `\@makecaption`), so
-- a captionless float bears no number; and this engine's floats never
-- float, so document order IS first-appearance order. `numberFloats` is
-- the one assignment site: elaboration writes `none`, this pass fills the
-- numbers, and both backends only replay what the node carries.

/-- The counters `numberFloats` threads: captioned figures, captioned
tables, and — reset at every float body, restored after it — captioned
subfloats, so a letter is an index within its own parent. -/
private structure FloatCtr where
  fig : Nat := 0
  tab : Nat := 0
  sub : Nat := 0
  alg : Nat := 0
  deriving Repr, BEq

private def FloatCtr.get : FloatCtr → FloatKind → Nat
  | c, .figure => c.fig
  | c, .table => c.tab
  | c, .sub => c.sub
  | c, .algorithm => c.alg

private def FloatCtr.bump : FloatCtr → FloatKind → FloatCtr
  | c, .figure => { c with fig := c.fig + 1 }
  | c, .table => { c with tab := c.tab + 1 }
  | c, .sub => { c with sub := c.sub + 1 }
  | c, .algorithm => { c with alg := c.alg + 1 }

mutual

/-- The numbering walk: every captioned float takes the next number of its
kind, in document order. A float's body letters its own subfloats from one
(`sub` resets on entry and is restored after), while the figure and table
counters thread straight through, so a nested float keeps document order.
A note is a side channel that never ships a float, so it does not consume
a number. -/
private def numberFloatList (c : FloatCtr) (out : Array Block) :
    List Block → FloatCtr × Array Block
  | [] => (c, out)
  | b :: rest =>
    let (c2, b2) := numberFloatOne c b
    numberFloatList c2 (out.push b2) rest

private def numberFloatOne (c : FloatCtr) : Block → FloatCtr × Block
  | .para content => (c, .para content)
  -- an equation holds no float; its number is its own
  | .equation n content => (c, .equation n content)
  | .section l st num title => (c, .section l st num title)
  | .list o items =>
    let (c2, items2) := numberFloatItems c #[] items.toList
    (c2, .list o items2)
  | .center body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .center body2)
  | .ragged s body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .ragged s body2)
  | .quote body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .quote body2)
  | .abstract body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .abstract body2)
  | .titled kind title body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .titled kind title body2)
  | .role n body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .role n body2)
  | .link target body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .link target body2)
  | .spaced g body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .spaced g body2)
  | .columns cols =>
    let (c2, cols2) := numberFloatCols c #[] cols.toList
    (c2, .columns cols2)
  | .onSteps spec body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .onSteps spec body2)
  | .altSteps spec firstPage otherPage =>
    let (c2, active2) := numberFloatList c #[] firstPage.toList
    let (c3, otherwise2) := numberFloatList c2 #[] otherPage.toList
    (c3, .altSteps spec active2 otherwise2)
  | .only targets body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .only targets body2)
  | .nav spec body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .nav spec body2)
  | .frame t s v br body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .frame t s v br body2)
  | .note body => (c, .note body)
  | .verbatim k s sp => (c, .verbatim k s sp)
  | .logo content => (c, .logo content)
  | .framefoot content => (c, .framefoot content)
  | .setPalette p => (c, .setPalette p)
  | .setTokens tk => (c, .setTokens tk)
  | .pagebreak => (c, .pagebreak)
  | .rule col nm th => (c, .rule col nm th)
  | .picture p => (c, .picture p)
  | .table cols pl pr rows rules spans => (c, .table cols pl pr rows rules spans)
  -- Lines hold inlines: no float can nest in an algorithm.
  | .algorithm n sm lines => (c, .algorithm n sm lines)
  -- A reference list is not a float: it consumes no number and holds none.
  | .bibliography src style items => (c, .bibliography src style items)
  | .float kind _ capAbove body caption =>
    let cAfter := if caption.isEmpty then c else c.bump kind
    let num := if caption.isEmpty then none else some (c.get kind + 1)
    let (cBody, body2) := numberFloatList { cAfter with sub := 0 } #[] body.toList
    (⟨cBody.fig, cBody.tab, cAfter.sub, cBody.alg⟩, .float kind num capAbove body2 caption)

private def numberFloatItems (c : FloatCtr) (out : Array (Array Block)) :
    List (Array Block) → FloatCtr × Array (Array Block)
  | [] => (c, out)
  | item :: rest =>
    let (c2, item2) := numberFloatList c #[] item.toList
    numberFloatItems c2 (out.push item2) rest

private def numberFloatCols (c : FloatCtr) (out : Array (BoxWidth × Array Block)) :
    List (BoxWidth × Array Block) → FloatCtr × Array (BoxWidth × Array Block)
  | [] => (c, out)
  | (w, body) :: rest =>
    let (c2, body2) := numberFloatList c #[] body.toList
    numberFloatCols c2 (out.push (w, body2)) rest

end

/-- Assign every float its number: the pass elaboration hands the finished
body to, once, before any backend reads it. -/
public def numberFloats (xs : Array Block) : Array Block :=
  (numberFloatList {} #[] xs.toList).2

/-- Numbering leaves a lone paragraph and all of its inline content unchanged. -/
public theorem numberFloats_para_exact (xs : Array Inline) :
    numberFloats #[.para xs] = #[.para xs] := by
  rfl

mutual

/-- The numbers the walk assigned to captioned floats of kind `k`, in
document order — the collector `numberFloats_exact` judges the walk by.
For `.sub` it reads a body's own letters: it does not descend into a
nested float's body, whose letters belong to that float. For `.figure`
and `.table` it descends everywhere the walk threads its counters. -/
public def floatNumsList (k : FloatKind) (out : List Nat) : List Block → List Nat
  | [] => out
  | b :: rest => floatNumsList k (floatNumsOne k out b) rest

private def floatNumsOne (k : FloatKind) (out : List Nat) : Block → List Nat
  | .para _ => out
  | .equation _ _ => out
  | .section _ _ _ _ => out
  | .list _ items => floatNumsItems k out items.toList
  | .center body => floatNumsList k out body.toList
  | .ragged _ body => floatNumsList k out body.toList
  | .quote body => floatNumsList k out body.toList
  | .abstract body => floatNumsList k out body.toList
  | .titled _ _ body => floatNumsList k out body.toList
  | .role _ body => floatNumsList k out body.toList
  | .link _ body => floatNumsList k out body.toList
  | .spaced _ body => floatNumsList k out body.toList
  | .columns cols => floatNumsCols k out cols.toList
  | .onSteps _ body => floatNumsList k out body.toList
  | .altSteps _ firstPage otherPage =>
    floatNumsList k (floatNumsList k out firstPage.toList) otherPage.toList
  | .only _ body => floatNumsList k out body.toList
  | .nav _ body => floatNumsList k out body.toList
  | .frame _ _ _ _ body => floatNumsList k out body.toList
  | .note _ => out
  | .verbatim _ _ _ => out
  | .logo _ => out
  | .framefoot _ => out
  | .setPalette _ => out
  | .setTokens _ => out
  | .pagebreak => out
  | .rule _ _ _ => out
  | .picture _ => out
  | .table _ _ _ _ _ _ => out
  | .algorithm _ _ _ => out
  | .bibliography _ _ _ => out
  | .float kind num _ body _ =>
    let out := match num with
      | some n => if kind = k then out ++ [n] else out
      | none => out
    if k = .sub then out else floatNumsList k out body.toList

private def floatNumsItems (k : FloatKind) (out : List Nat) :
    List (Array Block) → List Nat
  | [] => out
  | item :: rest => floatNumsItems k (floatNumsList k out item.toList) rest

private def floatNumsCols (k : FloatKind) (out : List Nat) :
    List (BoxWidth × Array Block) → List Nat
  | [] => out
  | (_, body) :: rest => floatNumsCols k (floatNumsList k out body.toList) rest

end

private theorem floatNumsList_append (k : FloatKind) (out : List Nat)
    (l1 l2 : List Block) :
    floatNumsList k out (l1 ++ l2) = floatNumsList k (floatNumsList k out l1) l2 := by
  induction l1 generalizing out with
  | nil => simp [floatNumsList]
  | cons b rest ih => simp [floatNumsList, ih]

private theorem range'_glue (s m n : Nat) :
    List.range' s m ++ List.range' (s + m) n = List.range' s (m + n) :=
  List.range'_append_1 ..

mutual

/-- The numbering is exact: processing `bs` from counters `c` advances the
`k` counter by some `n` and assigns exactly the numbers
`c.get k + 1, …, c.get k + n` to the captioned `k`-floats, in document
order. Instantiated at the top (`numberFloats_exact`) this is the fact
`\ref` resolves against: a float's number is the index of its first
appearance among captioned floats of its kind — floats never float here,
so document order is appearance order. -/
private theorem numberFloatList_exact (k : FloatKind) (c : FloatCtr) (acc : Array Block)
    (out : List Nat) (bs : List Block) :
    ∃ n, ((numberFloatList c acc bs).1).get k = c.get k + n ∧
      floatNumsList k out ((numberFloatList c acc bs).2).toList
        = floatNumsList k out acc.toList ++ List.range' (c.get k + 1) n := by
  match bs with
  | [] => exact ⟨0, by simp [numberFloatList], by simp [numberFloatList]⟩
  | b :: rest =>
    obtain ⟨m, hcm, hnm⟩ :=
      numberFloatOne_exact k c (floatNumsList k out acc.toList) b
    obtain ⟨n, hcn, hnn⟩ := numberFloatList_exact k (numberFloatOne c b).1
      (acc.push (numberFloatOne c b).2) out rest
    refine ⟨m + n, ?_, ?_⟩
    · show ((numberFloatList (numberFloatOne c b).1
        (acc.push (numberFloatOne c b).2) rest).1).get k = _
      rw [hcn, hcm, Nat.add_assoc]
    · show floatNumsList k out ((numberFloatList (numberFloatOne c b).1
        (acc.push (numberFloatOne c b).2) rest).2).toList = _
      rw [hnn, Array.toList_push, floatNumsList_append]
      simp only [floatNumsList]
      rw [hnm, hcm, List.append_assoc,
        show c.get k + m + 1 = (c.get k + 1) + m by omega, range'_glue]

private theorem numberFloatOne_exact (k : FloatKind) (c : FloatCtr) (out : List Nat)
    (b : Block) :
    ∃ n, ((numberFloatOne c b).1).get k = c.get k + n ∧
      floatNumsOne k out (numberFloatOne c b).2
        = out ++ List.range' (c.get k + 1) n := by
  match b with
  | .para _ | .equation _ _ | .section _ _ _ _ | .note _ | .verbatim _ _ _ | .logo _
  | .algorithm _ _ _
  | .bibliography _ _ _
  | .framefoot _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ =>
    exact ⟨0, by simp [numberFloatOne], by simp [numberFloatOne, floatNumsOne]⟩
  | .list o items =>
    obtain ⟨n, hc, hn⟩ := numberFloatItems_exact k c #[] out items.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsItems] using hn⟩
  | .center body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .ragged _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .quote body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .abstract body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .titled _ _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .role _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .link _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .spaced _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .columns cols =>
    obtain ⟨n, hc, hn⟩ := numberFloatCols_exact k c #[] out cols.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsCols] using hn⟩
  | .onSteps _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .altSteps _ firstPage otherPage =>
    obtain ⟨m, hcm, hnm⟩ := numberFloatList_exact k c #[] out firstPage.toList
    obtain ⟨p, hcp, hnp⟩ := numberFloatList_exact k
      (numberFloatList c #[] firstPage.toList).1 #[]
      (floatNumsList k out (numberFloatList c #[] firstPage.toList).2.toList)
      otherPage.toList
    refine ⟨m + p, ?_, ?_⟩
    · show ((numberFloatList (numberFloatList c #[] firstPage.toList).1 #[]
        otherPage.toList).1).get k = _
      rw [hcp, hcm, Nat.add_assoc]
    · show floatNumsList k (floatNumsList k out
        ((numberFloatList c #[] firstPage.toList).2).toList)
        ((numberFloatList (numberFloatList c #[] firstPage.toList).1 #[]
          otherPage.toList).2).toList = _
      rw [hnp]
      simp only [floatNumsList]
      rw [hnm]
      simp only [floatNumsList]
      rw [hcm, List.append_assoc,
        show c.get k + m + 1 = (c.get k + 1) + m by omega, range'_glue]
  | .only _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .nav _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .frame _ _ _ _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .float kind _ capAbove body caption =>
    by_cases hcap : caption.isEmpty
    · -- No caption: no number, no bump; the body still numbers its own
      -- figures and tables, and its letters are its own affair.
      obtain ⟨n, hc, hn⟩ :=
        numberFloatList_exact k { c with sub := 0 } #[] out body.toList
      cases k with
      | sub =>
        refine ⟨0, ?_, ?_⟩
        · simp [numberFloatOne, hcap, FloatCtr.get]
        · simp [numberFloatOne, floatNumsOne, hcap]
      | figure =>
        refine ⟨n, ?_, ?_⟩
        · simpa [numberFloatOne, hcap, FloatCtr.get] using hc
        · simpa [numberFloatOne, floatNumsOne, floatNumsList, hcap,
            FloatCtr.get] using hn
      | table =>
        refine ⟨n, ?_, ?_⟩
        · simpa [numberFloatOne, hcap, FloatCtr.get] using hc
        · simpa [numberFloatOne, floatNumsOne, floatNumsList, hcap,
            FloatCtr.get] using hn
      | algorithm =>
        refine ⟨n, ?_, ?_⟩
        · simpa [numberFloatOne, hcap, FloatCtr.get] using hc
        · simpa [numberFloatOne, floatNumsOne, floatNumsList, hcap,
            FloatCtr.get] using hn
    · cases k with
      | sub =>
        -- The collector reads only this float's own letter; the walk
        -- restores the outer sub counter after the body.
        cases kind with
        | sub =>
          refine ⟨1, ?_, ?_⟩
          · simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump]
          · simp [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              List.range'_succ]
        | figure =>
          refine ⟨0, ?_, ?_⟩
          · simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump]
          · simp [numberFloatOne, floatNumsOne, hcap]
        | table =>
          refine ⟨0, ?_, ?_⟩
          · simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump]
          · simp [numberFloatOne, floatNumsOne, hcap]
        | algorithm =>
          refine ⟨0, ?_, ?_⟩
          · simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump]
          · simp [numberFloatOne, floatNumsOne, hcap]
      | figure =>
        cases kind with
        | figure =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .figure
            { c.bump .figure with sub := 0 } #[] (out ++ [c.get .figure + 1])
            body.toList
          refine ⟨n + 1, ?_, ?_⟩
          · have := hc
            simp only [FloatCtr.get, FloatCtr.bump] at this ⊢
            simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump, this]
            omega
          · have := hn
            simp only [FloatCtr.get, FloatCtr.bump] at this
            simp [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList, this, List.append_assoc]
            rw [List.range'_succ]
        | table =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .figure
            { c.bump .table with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | sub =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .figure
            { c.bump .sub with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | algorithm =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .figure
            { c.bump .algorithm with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
      | table =>
        cases kind with
        | table =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .table
            { c.bump .table with sub := 0 } #[] (out ++ [c.get .table + 1])
            body.toList
          refine ⟨n + 1, ?_, ?_⟩
          · have := hc
            simp only [FloatCtr.get, FloatCtr.bump] at this ⊢
            simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump, this]
            omega
          · have := hn
            simp only [FloatCtr.get, FloatCtr.bump] at this
            simp [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList, this, List.append_assoc]
            rw [List.range'_succ]
        | figure =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .table
            { c.bump .figure with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | sub =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .table
            { c.bump .sub with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | algorithm =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .table
            { c.bump .algorithm with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
      | algorithm =>
        cases kind with
        | algorithm =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .algorithm
            { c.bump .algorithm with sub := 0 } #[] (out ++ [c.get .algorithm + 1])
            body.toList
          refine ⟨n + 1, ?_, ?_⟩
          · have := hc
            simp only [FloatCtr.get, FloatCtr.bump] at this ⊢
            simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump, this]
            omega
          · have := hn
            simp only [FloatCtr.get, FloatCtr.bump] at this
            simp [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList, this, List.append_assoc]
            rw [List.range'_succ]
        | figure =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .algorithm
            { c.bump .figure with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | table =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .algorithm
            { c.bump .table with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | sub =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .algorithm
            { c.bump .sub with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn

private theorem numberFloatItems_exact (k : FloatKind) (c : FloatCtr)
    (acc : Array (Array Block)) (out : List Nat) (items : List (Array Block)) :
    ∃ n, ((numberFloatItems c acc items).1).get k = c.get k + n ∧
      floatNumsItems k out ((numberFloatItems c acc items).2).toList
        = floatNumsItems k out acc.toList ++ List.range' (c.get k + 1) n := by
  match items with
  | [] => exact ⟨0, by simp [numberFloatItems], by simp [numberFloatItems]⟩
  | item :: rest =>
    obtain ⟨m, hcm, hnm⟩ := numberFloatList_exact k c #[]
      (floatNumsItems k out acc.toList) item.toList
    obtain ⟨n, hcn, hnn⟩ := numberFloatItems_exact k
      (numberFloatList c #[] item.toList).1
      (acc.push (numberFloatList c #[] item.toList).2) out rest
    refine ⟨m + n, ?_, ?_⟩
    · show ((numberFloatItems (numberFloatList c #[] item.toList).1
        (acc.push (numberFloatList c #[] item.toList).2) rest).1).get k = _
      rw [hcn, hcm, Nat.add_assoc]
    · show floatNumsItems k out ((numberFloatItems (numberFloatList c #[] item.toList).1
        (acc.push (numberFloatList c #[] item.toList).2) rest).2).toList = _
      rw [hnn, Array.toList_push]
      have happ : ∀ (l1 : List (Array Block)) (o : List Nat) (x : Array Block),
          floatNumsItems k o (l1 ++ [x])
            = floatNumsList k (floatNumsItems k o l1) x.toList := by
        intro l1 o x
        induction l1 generalizing o with
        | nil => simp [floatNumsItems]
        | cons y rest ih => simp [floatNumsItems, ih]
      rw [happ]
      simp only [floatNumsList] at hnm
      rw [hnm, hcm, List.append_assoc,
        show c.get k + m + 1 = (c.get k + 1) + m by omega, range'_glue]

private theorem numberFloatCols_exact (k : FloatKind) (c : FloatCtr)
    (acc : Array (BoxWidth × Array Block)) (out : List Nat)
    (cols : List (BoxWidth × Array Block)) :
    ∃ n, ((numberFloatCols c acc cols).1).get k = c.get k + n ∧
      floatNumsCols k out ((numberFloatCols c acc cols).2).toList
        = floatNumsCols k out acc.toList ++ List.range' (c.get k + 1) n := by
  match cols with
  | [] => exact ⟨0, by simp [numberFloatCols], by simp [numberFloatCols]⟩
  | (w, body) :: rest =>
    obtain ⟨m, hcm, hnm⟩ := numberFloatList_exact k c #[]
      (floatNumsCols k out acc.toList) body.toList
    obtain ⟨n, hcn, hnn⟩ := numberFloatCols_exact k
      (numberFloatList c #[] body.toList).1
      (acc.push (w, (numberFloatList c #[] body.toList).2)) out rest
    refine ⟨m + n, ?_, ?_⟩
    · show ((numberFloatCols (numberFloatList c #[] body.toList).1
        (acc.push (w, (numberFloatList c #[] body.toList).2)) rest).1).get k = _
      rw [hcn, hcm, Nat.add_assoc]
    · show floatNumsCols k out ((numberFloatCols (numberFloatList c #[] body.toList).1
        (acc.push (w, (numberFloatList c #[] body.toList).2)) rest).2).toList = _
      rw [hnn, Array.toList_push]
      have happ : ∀ (l1 : List (BoxWidth × Array Block)) (o : List Nat)
          (x : BoxWidth × Array Block),
          floatNumsCols k o (l1 ++ [x])
            = floatNumsList k (floatNumsCols k o l1) x.2.toList := by
        intro l1 o x
        induction l1 generalizing o with
        | nil => simp [floatNumsCols]
        | cons y rest ih => simp [floatNumsCols, ih]
      rw [happ]
      simp only [floatNumsList] at hnm
      rw [hnm, hcm, List.append_assoc,
        show c.get k + m + 1 = (c.get k + 1) + m by omega, range'_glue]

end

/-- The numbering fact `\ref` resolves against, over the engine's own
pass: the numbers `numberFloats` assigns to captioned floats of kind `k`,
read in document order, are exactly `1, 2, …` up to the walk's own count —
gapless, starting at one, in first-appearance order. -/
public theorem numberFloats_exact (k : FloatKind) (xs : Array Block) :
    floatNumsList k [] (numberFloats xs).toList
      = List.range' 1 (floatNumsList k [] (numberFloats xs).toList).length := by
  obtain ⟨n, _, hn⟩ := numberFloatList_exact k {} #[] [] xs.toList
  have h0 : (({} : FloatCtr)).get k = 0 := by cases k <;> rfl
  have hnums : floatNumsList k [] (numberFloats xs).toList = List.range' 1 n := by
    simpa [numberFloats, floatNumsList, h0] using hn
  rw [hnums, List.length_range']

/-- A subfloat's letter is its index within its own parent: every float
body enters the walk with the sub counter reset to zero (the `.float` arm
of `numberFloatOne`), so the letters assigned inside it — read shallowly,
a nested float's letters belonging to that float — are exactly `1, 2, …`
(subcaption: `\thesubfigure` is `(\alph{subfigure})`, an index within the
parent figure). -/
private theorem numberFloats_sub_letters (c : FloatCtr) (body : Array Block) :
    floatNumsList .sub []
        ((numberFloatList { c with sub := 0 } #[] body.toList).2).toList
      = List.range' 1
        (((numberFloatList { c with sub := 0 } #[] body.toList).1).get .sub) := by
  obtain ⟨n, hc, hn⟩ :=
    numberFloatList_exact .sub { c with sub := 0 } #[] [] body.toList
  have h0 : (({ c with sub := 0 } : FloatCtr)).get .sub = 0 := by rfl
  rw [h0] at hc hn
  simpa [floatNumsList, hc] using hn

/-- A subfloat's letter: `\alph` (1 → a, …, 26 → z). LaTeX's `\alph`
errors past 26; past it this engine sets the number itself — degraded,
never silent, and a 27-subfigure float has larger problems. -/
public def subLetter (n : Nat) : String :=
  if 1 ≤ n && n ≤ 26 then String.ofList [Char.ofNat (96 + n)] else s!"{n}"

/-- The caption's number prefix, derived from the node — the one
definition site both backends read, so the PDF and the HTML spell a
float's number identically. Sourced: article's `\@makecaption` sets
`\fnum@figure: text` with `\fnum@figure` = `\figurename~\thefigure`
(classes.dtx §\@makecaption), and subcaption's `\thesubfigure` is
`(\alph{subfigure})` followed by a space (subcaption.dtx, the default
`labelformat=parens`, `labelsep=space`). `\figurename`/`\tablename` are
locale data (babel's ini captions), so the prefix takes the document's
locale. A captionless float carries no number and no prefix. -/
public def captionPrefix (loc : Locale) (kind : FloatKind) (num : Option Nat) : Option String :=
  num.map fun n =>
    match kind with
    | .figure => s!"{loc.figure} {n}: "
    | .table => s!"{loc.table} {n}: "
    | .algorithm => s!"{loc.algorithm} {n}: "
    | .sub => s!"({subLetter n}) "

/-- A caption with its number prefix set in front: what a backend hands
its text machinery. The prefix is furniture the backend adds, like a list
marker — the IR's caption stays the declared text, so the census reads
declarations, not renderings. -/
public def numberedCaption (loc : Locale) (kind : FloatKind) (num : Option Nat)
    (caption : Array Inline) : Array Inline :=
  match captionPrefix loc kind num with
  | some p => (Inline.text p :: caption.toList).toArray
  | none => caption

/-- The float type a caption setting may be scoped to, as the caption
package names it (`\captionsetup[table]{...}`, caption manual §4): a
kind's own tokens carry this prefix (`tablecaptionsep`). subcaption's two
sub types are the engine's one sub kind. -/
public def FloatKind.captionScope : FloatKind → String
  | .figure => "figure"
  | .table => "table"
  | .sub => "sub"
  | .algorithm => "algorithm"

/-- The kind a caption package float type names, if the engine has it:
subcaption's scope for every sub-caption (`sub`, caption manual, subcaption
§2) and its two sub types are the engine's one sub kind. -/
public def FloatKind.ofCaptionType? : String → Option FloatKind
  | "figure" => some .figure
  | "table" => some .table
  | "sub" | "subfigure" | "subtable" => some .sub
  | "algorithm" => some .algorithm
  | _ => none

/-- A caption token as one float kind reads it: the kind's own
(`tablecaptionsep`, what `\captionsetup[table]` or a venue's table-only
`\abovecaptionskip` declares), else the document's (`captionsep`). The one
resolving site both backends read, so a setting scoped to tables never
reaches a figure. -/
public def captionTokenOf (tokens : Tokens) (kind : FloatKind) (key : String) : Option SymGlue :=
  tokens.find? (kind.captionScope ++ key) <|> tokens.find? key

/-- Where a document tells the caption package a float type's captions
stand, so it can place their two skips (caption manual §2.2, `position`;
caption3.sty `\DeclareCaptionPosition`). `auto` is the package's default
(caption3.sty `\SetCaptionDefault{position}{auto}`): a caption with nothing
before it in its float (`\prevdepth` still at the list's start,
`\caption@autoposition`) is taken for a top one, which is the engine's
`capAbove`. The kernel's `\@makecaption` (article.cls) places the skips as
`bottom` does. -/
public inductive CaptionPos where
  | top
  | bottom
  | auto
  deriving Repr, BEq, Inhabited

/-- A position as caption3.sty spells it: `top`, `t`, `above`; `bottom`,
`b`, `below`; `auto`, `a`. -/
public def CaptionPos.ofKey? : String → Option CaptionPos
  | "top" | "t" | "above" => some .top
  | "bottom" | "b" | "below" => some .bottom
  | "auto" | "a" => some .auto
  | _ => none

/-- `\caption@iftop`: is a caption standing on `capAbove`'s side placed as
a top one? -/
public def CaptionPos.placedTop : CaptionPos → Bool → Bool
  | .top, _ => true
  | .bottom, _ => false
  | .auto, capAbove => capAbove

/-- The position a float kind's captions are placed for: the kind's own
declaration (`\captionsetup[table]{position=…}`, `tableposition=`), else
the document's (`\captionsetup{position=…}`, keyed `""`), else `auto`. -/
public def captionPosOf (decl : Array (String × CaptionPos)) (kind : FloatKind) : CaptionPos :=
  (((decl.find? (·.1 == kind.captionScope)) <|> (decl.find? (·.1 == ""))).map (·.2)).getD .auto

/-- LaTeX's two caption skips (article.cls §\@makecaption, which sets
`\abovecaptionskip` above a caption and `\belowcaptionskip` below it):
`above` is the engine's `captionsep`, its default the rhythm quantum
standing in for the class's 10pt (`captionSepDefault`); `below` is the
`belowcaptionskip` token, its default the class's own 0pt. -/
public inductive CaptionSkip where
  | above
  | below
  deriving Repr, BEq, Inhabited

/-- The tokens a skip reads for a float kind, in lookup order: the kind's
own before the document's, `captionTokenOf`'s order. -/
public def CaptionSkip.keys (s : CaptionSkip) (kind : FloatKind) : List String :=
  let base := match s with
    | .above => "captionsep"
    | .below => "belowcaptionskip"
  [kind.captionScope ++ base, base]

/-- A skip's declared value for a float kind, if the document declares one. -/
public def CaptionSkip.find? (s : CaptionSkip) (tokens : Tokens) (kind : FloatKind) : Option SymGlue :=
  (s.keys kind).findSome? tokens.find?

/-- A skip's value where the document declares none. -/
public def CaptionSkip.default (s : CaptionSkip) (size : Sp) : SymGlue :=
  match s with
  | .above => captionSepDefault size
  | .below => {}

/-- **A caption's two skips, by the side it stands on and the side it is
placed for**: the skip between the caption and its object, then the one on
its text side. caption.sty's `\caption@makecaption` sets `\belowcaptionskip`
above and `\abovecaptionskip` below a caption placed as a top one, and the
kernel's order (`\abovecaptionskip` above, `\belowcaptionskip` below) for
a bottom one; so the object faces `\abovecaptionskip` exactly when the
caption stands where it is placed for. The one resolving site both
backends read: `Layout`'s float arm and `HtmlDoc`'s caption rules. -/
public def captionSides (pos : CaptionPos) (capAbove : Bool) : CaptionSkip × CaptionSkip :=
  if pos.placedTop capAbove == capAbove then (.above, .below) else (.below, .above)

/-- Undeclared — the package's `auto`, and the engine's default — a
caption's object faces `\abovecaptionskip` (`captionsep`) whichever side it
stands on, and its text side `\belowcaptionskip`: the gap binds a caption
to what it captions. -/
public theorem captionSides_auto_exact (capAbove : Bool) :
    captionSides .auto capAbove = (.above, .below) := by
  cases capAbove <;> rfl

/-- A declared position fixes the skips to the caption's own edges, so a
caption on the other side of its object reads them crosswise: under the
kernel's order (`bottom`) a caption above a table has `\belowcaptionskip`,
not `\abovecaptionskip`, between it and the table. -/
public theorem captionSides_declared_exact (pos : CaptionPos) (h : pos ≠ .auto) :
    captionSides pos true = (captionSides pos false).swap := by
  cases pos <;> first | rfl | exact absurd rfl h

/-- A listing caption with its number prefix set in front: the
figure-caption shape (`captionPrefix`'s own spelling, classes.dtx
§\@makecaption) with the locale's listing word — "Listing 1: text" —
the one site both backends spell a listing's number from, so the PDF and
the HTML cannot drift. The prefix is furniture the backend adds, exactly
as `numberedCaption`'s is: the IR keeps the declared text alone. -/
-- conserves: none — the prefix is furniture the backend adds at emission,
-- never a rewrite of the stored document: the IR's caption census stays
-- the declared text alone, exactly as `numberedCaption`'s does.
public def listingCaption (loc : Locale) (n : Nat) (caption : Array Inline) : Array Inline :=
  (Inline.text s!"{loc.listing} {n}: " :: caption.toList).toArray

/-- Verbatim content, line-split: the newline after `\begin{verbatim}` and
the blank tail before `\end{verbatim}` delimit — every trailing blank line
goes, not one — and everything between is content, interior blank lines
included. -/
public def verbatimLines (s : String) : Array String := Id.run do
  let s := if s.startsWith "\n" then (s.drop 1).toString
    else if s.startsWith "\r\n" then (s.drop 2).toString else s
  let mut lines := ((s.splitOn "\n").map fun l =>
    if l.endsWith "\r" then (l.dropEnd 1).toString else l).toArray
  repeat
    match lines.back? with
    | some last => if last.trimAscii.isEmpty then lines := lines.pop else break
    | none => break
  return lines

/-- The one source-preserving reader of listing classification. Metadata may
come from elaboration or a program constructing IR directly: a stale or
malformed cache must never delete, insert or reorder code. Such a cache falls
back to ordinary text. No backend lexes or reconstructs the source. -/
public def ListingSpec.tokenLines (spec : ListingSpec) (source : String) :
    Array (Array ListingHighlight.Token) :=
  if spec.highlight.map ListingHighlight.lineText = verbatimLines source then
    spec.highlight
  else
    (verbatimLines source).map fun line => #[{ text := line }]

/-- Every listing a backend reads has exactly the normalized source lines,
regardless of the cached token classes. This IR statement is the common
text-preservation premise of the PDF and HTML projections. -/
public theorem listing_source_exact (spec : ListingSpec) (source : String) :
    (spec.tokenLines source).map ListingHighlight.lineText = verbatimLines source := by
  unfold ListingSpec.tokenLines
  split
  · assumption
  · simp [Array.map_map, Function.comp_def, ListingHighlight.lineText]

/-- A listing segment's layout spelling and next display column. TAB
advances to the next stop, including a full stop at an exact boundary.
The caller resets the column at each source newline and may thread it
through highlighted segments; neither stored source nor token text changes.
No-wrap spaces, and the first indentation space, are unbreakable. -/
public def ListingSpec.layoutText (spec : ListingSpec) (column : Nat) (s : String) :
    String × Nat :=
  s.foldl (fun (out, col) c =>
    let space := if spec.breakLines && col > 0 then ' ' else '\u00a0'
    if c == '\t' then
      let width := max 1 spec.tabSize
      let count := width - col % width
      (out ++ String.ofList (List.replicate count space), col + count)
    else (out.push (if c == ' ' then space else c), col + 1)) ("", column)

/-- Verbatim content as inline text: tabs follow the declared stops,
spaces follow the wrapping policy, source lines join by forced breaks,
and a blank line keeps one no-break space so it still sets a line. -/
public def verbatimInlines (s : String) (spec : ListingSpec := {}) : Array Inline := Id.run do
  let mut out : Array Inline := #[]
  for line in verbatimLines s do
    unless out.isEmpty do
      out := out.push (.linebreak {})
    let kept := (spec.layoutText 0 line).1
    out := out.push (.text (if kept.isEmpty then "\u00a0" else kept))
  return out

/-- Where a heading rule stands against the heading's baseline. `xHeight`
is the engine's own placement — raised half the heading face's measured
x-height at its size, like a dash (Hochuli, Detail in Typography: a rule
relates to the type it cuts). `baseline` is TeX's `\hrule`: zero depth,
bottom edge on the baseline — what a `\sectionlinesformat` rule draws. -/
public inductive RulePosition where
  | xHeight
  | baseline
  deriving Repr, BEq, Inhabited, DecidableEq

/-- How far above the baseline a heading rule's bottom edge stands, from
its position and the heading face's x-height at the heading's size. The
one resolving site: `Layout` reads it into `Seg.rule`'s raise and the
HTML stylesheet's translate is its other projection. -/
public def RulePosition.raise : RulePosition → Sp → Sp
  | .xHeight, xh => xh / 2
  | .baseline, _ => 0

/-- The two positions are exact: a baseline rule is raised by nothing, an
x-height rule by half the x-height — the statement both backends project. -/
public theorem heading_rule_position_exact (xh : Int) :
    RulePosition.raise .baseline xh = 0 ∧ RulePosition.raise .xHeight xh = xh / 2 :=
  ⟨rfl, rfl⟩

/-- The declared datum a title-page slot sets: the five parts `\maketitle`
reads back, which beamer's inserts name (beamerbasetitle.sty:
`\inserttitle`, `\insertsubtitle`, `\insertauthor`, `\insertinstitute`,
`\insertdate`). -/
public inductive TitleDatum where
  | title
  | subtitle
  | author
  | institute
  | date
  deriving Repr, BEq, DecidableEq, Inhabited

public def TitleDatum.name : TitleDatum → String
  | .title => "title"
  | .subtitle => "subtitle"
  | .author => "author"
  | .institute => "institute"
  | .date => "date"

/-- The literal spelling of each declared title datum. -/
public theorem TitleDatum.name_exact (datum : TitleDatum) :
    datum.name = (match datum with
      | .title => "title"
      | .subtitle => "subtitle"
      | .author => "author"
      | .institute => "institute"
      | .date => "date") := by
  cases datum <;> rfl

public def TitleDatum.ofName? : String → Option TitleDatum
  | "title" => some .title
  | "subtitle" => some .subtitle
  | "author" => some .author
  | "institute" => some .institute
  | "date" => some .date
  | _ => none

public theorem TitleDatum.ofName_name (d : TitleDatum) : TitleDatum.ofName? d.name = some d := by
  cases d <;> rfl

/-- A point of a box, by pgf's compass names (TikZ manual §17.5.1, the
rectangle shape's anchors): the page's own points are the same names on
the page's box (`current page.south west`, §17.13.2). -/
public inductive BoxPoint where
  | center
  | north
  | south
  | east
  | west
  | northEast
  | northWest
  | southEast
  | southWest
  deriving Repr, BEq, DecidableEq, Inhabited

public def BoxPoint.ofName? : String → Option BoxPoint
  | "center" => some .center
  | "north" => some .north
  | "south" => some .south
  | "east" => some .east
  | "west" => some .west
  | "north east" => some .northEast
  | "north west" => some .northWest
  | "south east" => some .southEast
  | "south west" => some .southWest
  | _ => none

public def BoxPoint.name : BoxPoint → String
  | .center => "center"
  | .north => "north"
  | .south => "south"
  | .east => "east"
  | .west => "west"
  | .northEast => "north east"
  | .northWest => "north west"
  | .southEast => "south east"
  | .southWest => "south west"

public theorem BoxPoint.ofName_name (p : BoxPoint) : BoxPoint.ofName? p.name = some p := by
  cases p <;> rfl

/-- Where the point stands across its box, as a split of the box's width:
`(left, right)` shares on either side of it — the vocabulary `VAlign.shares`
distributes leftover space in, read here over an extent instead. -/
public def BoxPoint.hshares : BoxPoint → Nat × Nat
  | .west | .northWest | .southWest => (0, 1)
  | .center | .north | .south => (1, 1)
  | .east | .northEast | .southEast => (1, 0)

/-- Where the point stands down its box: `(above, below)` shares of its
height, the same pair a frame's vertical distribution declares — `north` is
`VAlign.top`'s, `west` `VAlign.center`'s, `south` `VAlign.bottom`'s. -/
public def BoxPoint.vshares : BoxPoint → Nat × Nat
  | .north | .northWest | .northEast => (0, 1)
  | .center | .west | .east => (1, 1)
  | .south | .southWest | .southEast => (1, 0)

/-- The offset of a point `(a, b)` shares into an extent: `e * a / (a + b)`,
zero for the empty split. The one arithmetic both backends call: the page
places a slot by it (`Layout.slotShift`) and the stylesheet writes its
percentages from it (`HtmlDoc.titleSlotCss`). That the stylesheet puts each
axis's share on the right property is tested (`titleSlotShipChecks`), not
proved. -/
public def shareOf (s : Nat × Nat) (e : Int) : Int :=
  if s.1 + s.2 = 0 then 0 else e * s.1 / (s.1 + s.2)

/-- **The stage's percentage is the page's point** (`_agree`), as
arithmetic: for every compass point, the share taken at the stylesheet's
hundred-thousandth scale and applied to an extent is the page's share of
that extent. What it does not say is which property the stylesheet writes
each share into; `titleSlotShipChecks` tests that, slot by slot, over the
stylesheet the typed tree ships. -/
public theorem pagePoint_agree (p : BoxPoint) (e : Int) :
    shareOf p.hshares e = shareOf p.hshares 100000 * e / 100000 ∧
    shareOf p.vshares e = shareOf p.vshares 100000 * e / 100000 := by
  cases p <;> simp [shareOf, BoxPoint.hshares, BoxPoint.vshares] <;> omega

/-- A title slot pinned to its page: which point of its box (`anchor`)
stands at which point of the page (`pagePoint`), moved by the shifts —
TikZ's own node placement (`anchor=`, `at (current page.<point>)`,
`[xshift=…, yshift=…]`; TikZ manual §17.5.1, §13.2). `yshift` keeps TikZ's
sense, positive up. `innerSep` is the space between the text and the box's
border, pgf's `inner sep` (§17.2.2); undeclared it is pgf's own
`0.3333em`, of the body font the node's options are read in. -/
public structure TitlePlace where
  anchor : BoxPoint
  pagePoint : BoxPoint
  xshift : Option SymGlue := none
  yshift : Option SymGlue := none
  innerSep : Option SymGlue := none
  deriving Repr, BEq, Inhabited

/-- pgf's own `inner sep`, `0.3333em` (TikZ manual §17.2.2, the
`inner sep` key's initial value), at the em it is read in: a template
node's options are read in the surrounding font, the body's. The same
value as `Picture.innerSepDefault`, which the picture subset reads. -/
public def pgfInnerSep (em : Sp) : Sp := em * 3333 / 10000

/-- pgf's rectangular-node anchor clearance, the initial `outer sep`:
half the initial 0.4 pt line width (pgf manual §17.2.3). It expands anchor
points but is not padding; the text box still carries only `inner sep`. -/
public def pgfOuterSep : Sp := Dim.pt 1 / 5

/-- One independently styled part of a title slot. `datum` selects document
metadata; with no datum, `content` is literal slot content. `newLine` starts
this part below the preceding present part, and `before` is the additional
vertical gap there. A missing or empty datum omits this part and its gap.
Font, alignment, absolute size and its baseline skip belong to the part,
while width and placement belong once to the containing slot. -/
public structure TitlePart where
  datum : Option TitleDatum
  content : Array Inline := #[]
  font : Option (Array Inline) := none
  align : Option String := none
  size : Option SymGlue := none
  leading : Option SymGlue := none
  newLine : Bool := false
  before : Option SymGlue := none
  deriving Repr, BEq, Inhabited

/-- One box of a declared title page: its ordered, independently styled
optional parts, its measure, and where the one box stands. A title page
that declares slots is the slots: a declared datum no part names is not
set, as a beamer title-page template that never inserts it does not set it. -/
public structure TitleSlot where
  parts : Array TitlePart := #[]
  width : Option SymGlue := none
  place : Option TitlePlace := none
  deriving Repr, BEq, Inhabited

/-- Build the one slot owned by a source node. This is the construction
door the node-to-slot conservation statement ranges over. -/
public def TitleSlot.ofNodeParts (parts : Array TitlePart) (width : Option SymGlue)
    (place : Option TitlePlace) : TitleSlot :=
  { parts := parts, width := width, place := place }

/-- **One node's ordered parts stay in its one slot** (`_exact`): node
translation changes neither their order nor their identity. -/
public theorem TitleSlot.ofNodeParts_exact (parts : Array TitlePart) (width : Option SymGlue)
    (place : Option TitlePlace) :
    (TitleSlot.ofNodeParts parts width place).parts = parts := by
  rfl

/-- The box-owned projection both backends consume: width and placement,
never a part's style. -/
public def TitleSlot.box (slot : TitleSlot) : Option SymGlue × Option TitlePlace :=
  (slot.width, slot.place)

/-- **A translated node's box projects unchanged** (`_projects`): the
layout and HTML backends read this one pair, so part styling cannot split
or move the node's box. -/
public theorem TitleSlot.ofNodeParts_projects (parts : Array TitlePart) (width : Option SymGlue)
    (place : Option TitlePlace) :
    (TitleSlot.ofNodeParts parts width place).box = (width, place) := by
  rfl

/-- The role a title slot's block rides in, by the slot's index: the class
hook both backends already read (`Block.role`), so the one IR value that
says where slot `i` stands is found from the block that shows it. -/
public def titleSlotRole (i : Nat) : String := s!"titlepage-slot-{i}"

/-- The role one styled part rides inside its slot. The slot role owns the
box; this nested inline role preserves the part in the typed HTML tree and
names any absolute size in the layout's existing size ladder. -/
public def titlePartRole (slot part : Nat) : String := s!"titlepage-slot-{slot}-part-{part}"

/-- The slot a role name shows, among a title page's declared slots: the
one lookup both backends make from the block to the value that places it. -/
public def titleSlotOf (slots : Array TitleSlot) (n : String) : Option TitleSlot :=
  (slots.zipIdx.find? fun (_, i) => titleSlotRole i == n).map (·.1)

/-- The part an inline role shows. Both backends use this lookup for the
part's exact size and baseline skip; a role that names no part stays an
authored, metric-transparent role. -/
public def titlePartOf (slots : Array TitleSlot) (n : String) : Option TitlePart :=
  slots.zipIdx.findSome? fun (slot, i) =>
    slot.parts.zipIdx.findSome? fun (part, k) =>
      if titlePartRole i k == n then some part else none

/-- How an element kind looks, from `\style{element}{...}`. Every field a
backend used to hard-code is here instead, so a design lives in the document.
`font` is a template: the inline wrappers a declaration like
`{\large\sffamily\bfseries\primary}` elaborates to, with an empty body where
the element's own content goes. -/
public structure ElementStyle where
  font : Option (Array Inline) := none
  before : Option SymGlue := none
  after : Option SymGlue := none
  /-- A rule filling the rest of the heading's line, in this palette colour. -/
  rule : Option (Color × Option String) := none
  /-- Where `rule` stands against the baseline; undeclared, `xHeight`. -/
  rulePosition : Option RulePosition := none
  /-- `rule`'s thickness; undeclared, the engine's em-relative weight
  (`Layout.headingRuleWeight`) in print and one device pixel on screen. -/
  ruleThickness : Option SymGlue := none
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
  /-- A full-measure rule above the element, this thick, in the ink colour:
  the NeurIPS-lineage top title bar (`\@toptitlebar`, `\hrule height 4\p@`
  above `\@title`). Read at the title block (`titleBars`); the venue
  contributes the weight — the four skips below are the document's own
  declarations, and where none stands the engine's rhythm places the bar
  (`titleBarGap`/`titleBarSkip`). -/
  ruleAbove : Option SymGlue := none
  /-- Declared space above `ruleAbove`; undeclared, `titleBarSkip`. -/
  ruleAboveSkip : Option SymGlue := none
  /-- Declared space between `ruleAbove` and the element's first line;
  undeclared, `titleBarGap`. -/
  ruleAboveGap : Option SymGlue := none
  /-- A full-measure rule below the element, this thick: the bottom title
  bar (`\@bottomtitlebar`, `\hrule height 1\p@`). -/
  ruleBelow : Option SymGlue := none
  /-- Declared space between the element's last line and `ruleBelow`;
  undeclared, `titleBarGap`. -/
  ruleBelowGap : Option SymGlue := none
  /-- Declared space below `ruleBelow`, before what follows (the author
  block); undeclared, `titleBarSkip`. -/
  ruleBelowSkip : Option SymGlue := none
  /-- The author line's font template, read at the title block: the
  NeurIPS-lineage `\bf` inside the author `tabular`, or a document's own
  `\style{titlepage}{ author-font = ... }`. -/
  authorFont : Option (Array Inline) := none
  /-- The author line's minimum height above its baseline — the lineage's
  `\rule{\z@}{24\p@}` strut, giving the name room instead of its bare cap
  height. The engine's value is `titleAuthorStrut`, a rhythm multiple. -/
  authorStrut : Option SymGlue := none
  /-- The size step the element's body sets at, read by the abstract only
  (`abstractBodySize`): article.cls declares `\small` over the whole
  environment, and a redefinition that declares none leaves its body at
  the size in force, `\normalsize`. -/
  bodySize : Option String := none
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
  /-- The ink a link kind's text is set in (`link`, `url`, `cite`), where the
  document declares one: hyperref's `linkcolor`, `urlcolor` and `citecolor`
  under `colorlinks`. Read at the one site each kind's link is built
  (`linkInk`); undeclared, a link keeps the running colour. -/
  color : Option (Color × Option String) := none
  /-- The title page's declared slots (`TitleSlot`), read by the title page
  only: a title page that declares any sets exactly its slots, each where
  it is pinned. Empty is the built-in title page. -/
  slots : Array TitleSlot := #[]
  deriving Repr, BEq, Inhabited

/-- What of the `titlepage` style the title heading itself takes: every key
but the ones that place a heading's line — a heading rule fills the line a
heading leaves, and an indent narrows it, and either takes a centred title
off its centre — and the list keys, which a heading has no items for. The
title page's own rules are `ruleAbove`, `ruleBelow` and `separator`
(`Elab.titleBlocks`). Both artifacts read the title through this one
projection (`Layout.collectTitle`, the HTML `h1`), so neither places the
title by a key the other ignores: the HTML once drew a heading rule the page
never drew, and the flex row that drew it set a centred title flush left.
What no site then reads is `titleUnreadKeys`. -/
public def titleHeadingStyle (st : ElementStyle) : ElementStyle :=
  { st with rule := none, rulePosition := none, ruleThickness := none, indent := none,
            marker := none, gap := none, bodySize := none }

/-- The `\style` keys no engine site reads on the title page, named where
they are declared (W0104) rather than dropped in silence. -/
public def titleUnreadKeys : List String :=
  ["rule", "rule-position", "rule-thickness", "marker", "indent", "gap", "body-size"]

/-- Elements a document may style. Section levels are `section`, `subsection`,
`subsubsection`; lists are `itemize` and `enumerate` — those two style every
nesting level, and `itemize2`..`itemize4` / `enumerate2`..`enumerate4`
override one level, the way `\labelitemii` or `\setlist[itemize,2]` does;
`frametitle`, `sectionpage`, `standout`, and `titlepage` are the slides
furniture (their `font` is read; `titlepage` also reads `align` and
`separator`; the other keys have no meaning there yet); `logo` reads
`align` only — where the logo stands in the furniture band (`logoAlign`,
both backends). Beyond this list, a
`\define`d name is styleable too (the elaborator admits it once the
`\define` stands): the role's rhythm rides `before`/`after` on the page,
and the whole style addresses the `u-<name>` class hook in HTML. -/
public def styleableElements : List String :=
  ["section", "subsection", "subsubsection", "heading1", "heading5", "heading6",
   "abstract", "itemize", "enumerate",
   "itemize2", "itemize3", "itemize4", "enumerate2", "enumerate3", "enumerate4",
   "frametitle", "sectionpage", "standout", "titlepage", "nav", "logo",
   "link", "url", "cite"]

public structure Styles where
  entries : Array (String × ElementStyle) := #[]
  deriving Repr, BEq, Inhabited

public def Styles.find? (s : Styles) (element : String) : Option ElementStyle :=
  (s.entries.find? (·.1 == element)).map (·.2)

/-- A link's body in its kind's declared ink (`ElementStyle.color`: `link`
for a cross-reference, `url` for a URL, `cite` for a citation mark), what
hyperref's `colorlinks` sets: `\Hy@colorlink` colours the link's own text,
never the brackets or words around it. Undeclared, the body as it stands. -/
public def Styles.linkInk (s : Styles) (kind : String) (body : Array Inline) : Array Inline :=
  match (s.find? kind).bind (·.color) with
  | some (c, n) => #[.colored c n body]
  | none => body

/-- Replace-on-redeclare, one entry per element — the same install mechanism
as `Palette.declare`/`Tokens.declare`. A `\style` block edits keys of the
element's existing entry first; what is declared here is the whole record. -/
public def Styles.declare (s : Styles) (element : String) (st : ElementStyle) : Styles :=
  { entries := (s.entries.filter (·.1 != element)).push (element, st) }

/-- The abstract heading's style is the section heading's, centred: a
reference, not a copy, so a venue or theme that restyles sections carries
the abstract heading with it — the class's own relation (the NeurIPS
lineage sets both headings `\large\bf`, differing only in alignment:
section `\raggedright`, Abstract centred; article.cls sets both in the
bold face). An explicit `\style{abstract}` key wins per key;
`abstract_heading_follows_section` is the equation. Undeclared on both
sides, `font` is `none` and each backend keeps its class-sourced default. -/
public def abstractHeadingStyle (styles : Styles) : ElementStyle :=
  let sec := (styles.find? "section").getD {}
  let own := (styles.find? "abstract").getD {}
  { own with
    font := own.font <|> sec.font
    align := own.align <|> some "center" }

/-- With no explicit `\style{abstract}`, the abstract heading's font equals
the section heading's, and it centres — by construction of the derivation,
which is what keeps the two headings from drifting when a venue or theme
restyles sections. -/
public theorem abstract_heading_follows_section (styles : Styles)
    (h : styles.find? "abstract" = none) :
    (abstractHeadingStyle styles).font =
      ((styles.find? "section").getD {}).font ∧
    (abstractHeadingStyle styles).align = some "center" := by
  simp [abstractHeadingStyle, h]

/-- The abstract body's size step: the one resolving site both backends
read. Undeclared, article.cls §abstract's `\small`, which it declares over
the whole environment before the heading. -/
public def abstractBodySize (styles : Styles) : String :=
  ((styles.find? "abstract").bind (·.bodySize)).getD "small"

/-- What a chrome footer slot shows, resolved per page by the backends: the
title of the current top-level section, or the index of the page's own frame
(one number for all pages of a stepped frame). Data, not content: a theme
names the datum and the engine supplies the value, so a bundle stays a table
and no backend learns a theme's name. -/
public inductive ChromeSlot where
  | sectionTitle
  | frameNumber
  /-- The `n / N` form: moloch's `numbering=fraction`, beamer's
  `[totalframenumber]` template (beamerouterthememoloch.dtx:156-188). -/
  | frameFraction
  deriving Repr, BEq, Inhabited

public def ChromeSlot.label : ChromeSlot → String
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
public def ChromeSlot.priority : ChromeSlot → Nat
  | .frameNumber => 0
  | .frameFraction => 1
  | .sectionTitle => 2

public theorem ChromeSlot.priority_injective : ∀ a b : ChromeSlot,
    a.priority = b.priority → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [priority]

/-- A `\framefoot` note is the author's own content: it outranks every
furniture datum. -/
public def notePriority : Nat := 3

/-- Which side of a furniture band a slot occupies. The position is the
declaration; a band holds at most one slot per side. -/
public inductive BandSide where
  | left
  | right
  deriving Repr, BEq, DecidableEq, Inhabited

public def BandSide.idx : BandSide → Nat
  | .left => 0
  | .right => 1

/-- One slot of a furniture band, as both backends consume it: the declared
side, the resolved content, and the declared priority. A band slot always
ships ink — an empty slot is absent from the band, not a case its
neighbours see. -/
public structure BandSlot where
  side : BandSide
  content : Array Inline
  priority : Nat
  label : String
  deriving Repr, BEq, Inhabited

/-- The band's paint order: declared priority first, side as the tiebreak.
Over a band's slots this order is total with no ties — a band holds one
slot per side (`rank_ne_of_side_ne`) — so the slot painted under, the one
that yields on a collision, is a fact of the declaration. -/
public def BandSlot.rank (s : BandSlot) : Nat := 2 * s.priority + s.side.idx

public theorem BandSlot.rank_ne_of_side_ne (a b : BandSlot) (h : a.side ≠ b.side) :
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
public def ChromeSlot.render (s : ChromeSlot) (sectionTitle : Array Inline)
    (n total : Nat) : Array Inline :=
  match s with
  | .sectionTitle => sectionTitle
  | .frameNumber => #[.text (toString n)]
  | .frameFraction => #[.text s!"{n} / {total}"]

/-- Page furniture a theme (or the document, via `\chrome`) declares: the
slide footer's two slots. A document's own `\runningfoot` overrides the
whole footer; a slot left undeclared is empty. Redeclaring `\chrome`
merges per slot, and a theme's chrome installs through the same per-slot
merge (`Theme.apply`) — a theme fills the slots the document left empty,
and naming one slot never clears its sibling. -/
public structure Chrome where
  footerLeft : Option ChromeSlot := none
  footerRight : Option ChromeSlot := none
  /-- Restore an explicit note on a standout frame. Undeclared
  keeps the class's plain standout; `some false` explicitly disables it. -/
  standoutNote : Option Bool := none
  deriving Repr, BEq, Inhabited

public def Chrome.hasFooter (c : Chrome) : Bool :=
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
public def Chrome.footSlots (c : Chrome) (frameFoot : Option (Array Inline))
    (sectionTitle : Array Inline) (n total : Nat) :
    Array Inline × Array Inline :=
  let slot (s : ChromeSlot) : Array Inline := s.render sectionTitle n total
  let left := match frameFoot with
    | some xs => xs
    | none => (c.footerLeft.map slot).getD #[]
  (left, (c.footerRight.map slot).getD #[])

/-- One band slot when its content ships ink, none when it is empty: an
absent slot is how "the empty left slot" stops being a case at all. -/
public def bandSlotIf (side : BandSide) (content : Array Inline)
    (priority : Nat) (label : String) : Array BandSlot :=
  if content.isEmpty then #[] else #[{ side, content, priority, label }]

public theorem mem_bandSlotIf {s : BandSlot} {side : BandSide}
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
public def Chrome.footBand (c : Chrome) (frameFoot : Option (Array Inline))
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
different pairs. A deleted one-line renderer once carried this as its own
equation; the statement below carries it now. -/
public theorem Chrome.footBand_projects (c : Chrome) (ff : Option (Array Inline))
    (sec : Array Inline) (n total : Nat) {s : BandSlot}
    (h : s ∈ c.footBand ff sec n total) :
    (s.side = .left ∧ s.content = (c.footSlots ff sec n total).1) ∨
    (s.side = .right ∧ s.content = (c.footSlots ff sec n total).2) := by
  unfold footBand at h
  rw [Array.mem_append] at h
  rcases h with h | h
  · exact .inl (mem_bandSlotIf h)
  · exact .inr (mem_bandSlotIf h)

/-- The frame's band, selected once for both backends. Moloch's standout
option normally clears the footline. Restoring its plain template only
when `frame footer` is nonempty restores that note, never a section datum
or a number (beamerinnerthememoloch.sty,
`KV@beamerframe@standout`; beamerouterthememoloch.sty, `footline/plain`). -/
public def Chrome.frameFootBand (c : Chrome) (ff : Option (Array Inline))
    (sec : Array Inline) (n : Option Nat) (total : Nat) (standout : Bool) :
    Option (Array BandSlot) :=
  if standout then
    if c.standoutNote.getD false && !(ff.getD #[]).isEmpty then
      some (bandSlotIf .left (ff.getD #[]) notePriority "the \\framefoot note")
    else none
  else
    n.bind fun k =>
      if c.hasFooter || ff.isSome then some (c.footBand ff sec k total) else none

/-- A standout band contains only a restored explicit note, independently
of its frame number. Neither chrome datum reaches either backend, and an
empty or disabled note has no band. -/
public theorem Chrome.standoutFootBand_exact (c : Chrome) (ff : Option (Array Inline))
    (sec : Array Inline) (n : Option Nat) (total : Nat) :
    c.frameFootBand ff sec n total true =
      if c.standoutNote.getD false && !(ff.getD #[]).isEmpty then
        some (bandSlotIf .left (ff.getD #[]) notePriority "the \\framefoot note")
      else none := by
  simp [frameFootBand]

/-- A band's inline content read left to right — the reading order, as
distinct from the paint order (`BandSlot.rank`). -/
public def bandInlines (b : Array BandSlot) : Array Inline :=
  (b.filter (·.side == .left) ++ b.filter (·.side == .right)).flatMap
    (·.content)

/-- The right slot is a function of its own declaration: neither the left
slot's declaration nor a `\framefoot` note in force can move or change it —
the empty-left case cannot move the number. -/
public theorem Chrome.footSlots_right_ignores_left (c c' : Chrome)
    (ff ff' : Option (Array Inline)) (sec : Array Inline) (n total : Nat)
    (h : c.footerRight = c'.footerRight) :
    (c.footSlots ff sec n total).2 = (c'.footSlots ff' sec n total).2 := by
  simp [footSlots, h]

/-- And the left slot of its own: the right slot's declaration never reaches
it. -/
public theorem Chrome.footSlots_left_ignores_right (c c' : Chrome)
    (ff : Option (Array Inline)) (sec : Array Inline) (n total : Nat)
    (h : c.footerLeft = c'.footerLeft) :
    (c.footSlots ff sec n total).1 = (c'.footSlots ff sec n total).1 := by
  simp [footSlots, h]

/-- Where moloch's footline template stands on the page, and how much of
the page it takes from the frame (beamerouterthememoloch.sty:113-125,
`\defbeamertemplate{footline}{plain}`). beamer sets a footline as wide as
the paper (beamerbaseframecomponents.sty:128, `\textwidth=\paperwidth`) in
the `footline` font; the template's colour box insets its slots from the
paper's side edges and closes with `\vskip4pt`, and the box stands on the
paper's bottom edge — so the slots' baseline is the band's depth plus
`raise` above that edge. beamer ends a frame's text area `sep` above the
band's top (`\footheight` is the band's height and depth plus 4 pt). Both
backends read `step`; the rest is the paged artifact's geometry. -/
public structure Footline where
  step : String
  left : Sp
  right : Sp
  raise : Sp
  sep : Sp
  deriving Repr

public def footline : Footline :=
  { step := "tiny"      -- beamerfontthemedefault.sty:67 and :19, footline: parent={tiny structure}, size=\tiny
    left := Dim.pt 4    -- beamerouterthememoloch.sty:115, leftskip=4pt
    right := Dim.pt 5   -- beamerouterthememoloch.sty:116, rightskip=5pt
    raise := Dim.pt 4   -- beamerouterthememoloch.sty:123, \vskip4pt
    sep := Dim.pt 4 }   -- beamerbaseframecomponents.sty:167, \advance\footheight by 4pt

mutual

/-- The walk of `fillTemplate`. Exhaustive over `Inline` by design: any
body-carrying wrapper may hold the template's hole, and a leaf carries no
body to fill. A new constructor must answer here or the build breaks —
never add a wildcard arm (AGENTS.md, the obligation table). -/
private def fillOne (content : Array Inline) : Inline → Inline
  | .styled st body =>
    .styled st (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .colored c n body =>
    .colored c n (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .located span body =>
    .located span (fillList content body.toList).toArray
  | .role n body =>
    .role n (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .decorated kind body =>
    .decorated kind (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .link u body =>
    .link u (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .onSteps spec body =>
    .onSteps spec (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec
      (if firstPage.isEmpty then content else (fillList content firstPage.toList).toArray)
      (if otherPage.isEmpty then content else (fillList content otherPage.toList).toArray)
  | .text s => .text s
  | .math d src => .math d src
  -- a formula's body is math atoms, an image carries no inline body:
  -- neither can hold the template's hole
  | .formula d src body => .formula d src body
  | .image src size alt => .image src size alt
  | .icon s l => .icon s l
  | .label k => .label k
  | .ref k p t tg => .ref k p t tg
  | .fill => .fill
  | .hspace g keep => .hspace g keep
  | .rule w h r => .rule w h r
  | .strut h => .strut h
  | .italicCorr m => .italicCorr m
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak e => .linebreak e
  -- a citation carries no inline body: it cannot hold the template's hole
  | .cite t ks => .cite t ks
  -- a footnote's body is the note's own text, never a template hole
  | .footnote n body => .footnote n body

private def fillList (content : Array Inline) : List Inline → List Inline
  | [] => []
  | x :: rest => fillOne content x :: fillList content rest

end

/-- Fill a font template's hole with content. The hole is the innermost empty
body; a template with no hole (plain content) is returned unchanged, which
is what a marker is. -/
-- conserves: none — a splice, not a walk of one tree: the output census is
-- the template's plus the content's, conservation of neither alone; the
-- styled-heading and marker tests pin the behaviour.
public def fillTemplate (template content : Array Inline) : Array Inline :=
  if template.isEmpty then content else (fillList content template.toList).toArray

/-- The size a font template sets its content at: the outermost `.size`
wrapper's step of the base, else the base itself. Both shipped frametitle
templates are `{\large\bfseries}` (`Theme.boldFont`), so the frame-title
bar's strut reads its size from here rather than from a glyph pass. -/
public def templateSize (base : Sp) (tpl : Array Inline) : Sp :=
  if let some (Inline.styled (Style.size s) _) := (tpl[0]? : Option Inline)
  then scaleStep base s else base

/-- The token resolves to the strut it is defined as: at the slides
class's `\large` title step, `frametitlepadding` and `frameTitleStrut`
agree — the dtx's one value, spelled once as a token and once as the
kernel's strut. Per-base `decide`, with `titleAuthorStrut`'s caveat:
em-resolution floors, so the general equality is false off the shipped
bases. -/
public theorem frameTitlePadding_exact :
    frameTitlePadding.width.resolve (scaleStep slidesFontSize "large") 0 =
      frameTitleStrut (scaleStep slidesFontSize "large") := by
  decide

/-- The kernel's page models: how content maps onto the surfaces the paged
backends draw. Three today; `report`'s chapter-opens-a-page is the one
candidate fourth. HTML is continuous scroll whatever the model —
scroll-vs-page is per medium, the model per document. -/
public inductive PageModel where
  /-- Content flows into a sequence of pages (`article`'s model). -/
  | flow
  /-- A frame is a page boundary; overlays produce steps (`slides`). -/
  | frame
  /-- Fixed faces, no flow: trim sizes and a print safe zone (`card`). -/
  | face
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The page-count bound a class implies, when it implies one: a literal
(`resume`: fits one page) or the document's own declared faces (`card`). -/
public inductive PagesBound where
  | lit (op : CmpOp) (n : Int)
  | faces
  deriving Repr, BEq

/-- A document class is a record over one of the kernel's page models:
defaults, furniture flags, implied assertions, build intent — values only,
no code. A class that needs layout code rather than fields here is asking
for a new page model and that is a kernel discussion, not a class. -/
public structure ClassRecord where
  model : PageModel
  /-- The class's body-size default, when it declares one (`slides`:
  beamer's documented 11 pt, user guide §18.2.1). -/
  fontSize : Option Sp := none
  /-- The class's paragraph-separation default, when it declares one.
  `resume` declares zero: the LaTeX résumé lineage (moderncv.cls keeps the
  standard classes' zero `\parskip`) spaces entries by declared rhythm,
  not by paragraph skips — the same value compat injects when a foreign
  résumé class is rewritten, so the native spelling and the rewritten one
  agree. `slides` declares zero too, and for the same reason the source
  does: beamer sets `\parskip` to `0pt` (beamerbasemisc.sty, with its
  `plus 1pt` stretch commented out), so a frame spends nothing between
  paragraphs. A frame is a fixed stage rather than a run of pages, so the
  quantum an article spends per paragraph accumulates against a height
  that cannot grow: it is what pushed content that fits beamer's stage
  past this engine's, and a spilt frame costs a continuation page
  (W0384). -/
  parskip : Option Dim.SymGlue := none
  /-- Where the class's list spacing comes from (`listSkips`): the size
  file of the standard classes, or beamer's own list family for a deck
  and a poster (beamerposter loads beamer). -/
  lists : ListLineage := .sizeFile
  /-- The preamble sets text in the sans family: beamer's `\familydefault`
  is `\sfdefault`, so a package loaded with a deck or a poster measures its
  lengths in Latin Modern Sans, where the standard classes' and moderncv's
  preambles set Latin Modern Roman (`PreambleFace`). -/
  preambleSans : Bool := false
  /-- Headings number by default; `\section*` opts out either way.
  `article` numbers (classes.dtx `\@startsection` with counters); a résumé
  is scanned, not cross-referenced, so `resume` does not (moderncv.cls
  sets its sections unnumbered), and `webpage` follows the web, whose
  headings carry no numbering convention. -/
  numberHeadings : Bool := false
  /-- The measure is judged against the readable band (W0201): continuous
  prose classes only — slides are display text, a card one face of it. -/
  measureBand : Bool := false
  /-- Running head, foot and logo are legal furniture (a card carries
  none: one face of display text, not a page of a run). -/
  runningFurniture : Bool := true
  /-- Pages carry the physical page number, centred in the foot, unless
  the document declares otherwise: LaTeX's `plain` page style — the
  kernel's `\ps@plain` sets the foot to `\hfil\thepage\hfil` (ltpage.dtx)
  and article.cls initialises `\pagestyle{plain}` (classes.dtx §Initial
  values) — so an article's pages number themselves. `resume` does not:
  the class already asserts one page, and a number on a known-single page
  navigates nothing. `webpage` is HTML-primary and its print twin follows
  the web, which numbers no pages; `slides` numbers frames through the
  chrome (the deliberately separate sequence); a card is not a run. -/
  pageNumbers : Bool := false
  /-- The chrome band and the slides furniture styles draw. -/
  chrome : Bool := false
  /-- The class draws the `\title` family as a page-top headline band —
  poster furniture (the gemini lineage's headline template draws the
  declarations without a `\maketitle`); every other class waits for
  `\maketitle`. -/
  headline : Bool := false
  /-- Implied contract, checked against the shipped pages exactly as a
  declared `\assert` is; a document declaring an assertion of the same
  form is intent and takes control. The help beside each value is the
  failure guidance E0330 prints. -/
  pagesBound : Option PagesBound := none
  /-- Failure guidance for a `.lit` pages bound (`.faces` builds its own:
  it names the counted faces). -/
  pagesHelp : String := ""
  /-- `textInArea` implied, with its failure guidance. -/
  inkInArea : Option String := none
  /-- `minXHeight` implied: the floor and its failure guidance. -/
  xHeightFloor : Option (Sp × String) := none
  /-- The face's trade trim size (width × height), when the class fixes
  one: a face is trimmed to a declared physical size, and the default is
  the trade's, never a guess — the card's ISO/IEC 7810 ID-1, the
  poster's ISO 216 A0. A declared `\page` geometry overrides. -/
  trimDefault : Option (Sp × Sp) := none
  /-- The face's print safe zone: the default margins, inside which a
  drifting trim cannot cut. Print-shop guidance asks 3–5 mm on a card
  (the engine takes the conservative 5); beamerposter sets 1 cm side
  margins on a poster (`\geometry{hmargin=1cm}`). -/
  safeMargin : Option Sp := none
  /-- Build intent when the document's `\output` names no formats. -/
  formats : Array String := #[]
  /-- The markdown twin's default file name, when the class has one
  (`webpage`: `llms.txt`, the llmstxt.org convention the twin exists
  for). A document's own `md = "..."` overrides. -/
  mdName : Option String := none
  deriving Repr, BEq

/-- The document's class, closed: `article`, `slides`, `card`, `resume`,
`webpage`, or `poster`. A class an `ofString?` does not answer is E0309 at the one
parse site and never enters the IR, so every class-dependent decision
downstream is a total decision over this type — a misspelled class in
engine code is a compile error, and a new class does not build until
`name`, `ofString?`, `record`, and every exhaustive match over the type
answer it. -/
public inductive DocClass where
  | article
  | slides
  | card
  /-- Structurally an article — the flow model — with the résumé genre's
  contract implied: fits one page, ink inside the margins, nothing below
  the legibility floor. -/
  | resume
  /-- Structurally an article; HTML-primary, the PDF the print
  stylesheet's analogue. Declares its own build intent (html + md). -/
  | webpage
  /-- One fixed, printed, trimmed surface at a large base — the face
  model's second class. beamerposter's own mechanics decided the model:
  the package sets a real paper size and replaces the size ladder with
  absolute values; nothing frame-model survives (no overlays on a printed
  sheet, no stage, no per-frame pagination). Column and block vocabulary
  is content structure, shared with decks, orthogonal to the model. -/
  | poster
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The class's one spelling — the `\documentclass` argument and the dump
header alike. -/
public def DocClass.name : DocClass → String
  | .article => "article"
  | .slides => "slides"
  | .card => "card"
  | .resume => "resume"
  | .webpage => "webpage"
  | .poster => "poster"

/-- The class a `\documentclass` argument names, if any: the inverse of
`name`, and the one door a class enters the IR through. -/
public def DocClass.ofString? : String → Option DocClass
  | "article" => some .article
  | "slides" => some .slides
  | "card" => some .card
  | "resume" => some .resume
  | "webpage" => some .webpage
  | "poster" => some .poster
  | _ => none

public theorem DocClass.ofString?_name (c : DocClass) : ofString? c.name = some c := by
  cases c <;> rfl

/-- Each class as its record — one shape for all five, so a new class is
one constructor and one row here, and anything a row cannot say is a page
model question. Sources: slides' 11 pt is beamer's (user guide §18.2.1);
the card's floor is the fluent-reading angular x-height at hand-held
distance, 1.4 mm at 40 cm (Legge & Bigelow 2011), and `resume` shares it —
a résumé is read at the same distance; `resume`'s one-page bound is the
genre's own contract (the reason one asks for a résumé and not a CV);
`webpage`'s build intent is html plus the markdown twin, the llms.txt
convention (llmstxt.org), with the print twin opt-in — the class carries
what to build the way `\documentclass` already carries the page model. -/
@[expose] public def DocClass.record : DocClass → ClassRecord
  | .article =>
    { model := .flow
      numberHeadings := true
      measureBand := true
      pageNumbers := true }
  | .slides =>
    { model := .frame
      fontSize := some slidesFontSize
      parskip := some {}
      lists := .beamer
      preambleSans := true
      chrome := true }
  | .card =>
    { model := .face
      runningFurniture := false
      pagesBound := some .faces
      inkInArea := some "the margins are the print safe zone: ink past them risks \
the trim; declare \\assert{ text.in_area } to take control"
      xHeightFloor := some (cardXHeightFloor,
        "1.4mm x-height is the fluent-reading floor at hand-held \
distance (Legge & Bigelow 2011); declare \\assert{ text.xheight >= ... } to take control")
      trimDefault := some (Dim.mm100 8560, Dim.mm100 5398)
      safeMargin := some (Dim.mm 5) }
  | .resume =>
    { model := .flow
      measureBand := true
      parskip := some {}
      pagesBound := some (.lit .eq 1)
      pagesHelp := "the resume class asserts content fits one page; \
declare \\assert{ pages <= N } to take control"
      inkInArea := some "the margins frame what every printer keeps: ink past \
them risks the clip; declare \\assert{ text.in_area } to take control"
      xHeightFloor := some (cardXHeightFloor,
        "1.4mm x-height is the fluent-reading floor at hand-held \
distance (Legge & Bigelow 2011); declare \\assert{ text.xheight >= ... } to take control") }
  | .webpage =>
    { model := .flow
      measureBand := true
      lists := .web
      formats := #["html", "md"]
      mdName := some "llms.txt" }
  | .poster =>
    { model := .face
      fontSize := some posterFontSize
      lists := .beamer
      preambleSans := true
      headline := true
      pagesBound := some .faces
      inkInArea := some "the margins are the print safe zone: ink past them risks \
the trim; declare \\assert{ text.in_area } to take control"
      xHeightFloor := some (posterXHeightFloor,
        "3.5mm x-height is the fluent-reading floor (Legge & Bigelow 2011) \
at 1m, the distance where a poster body at beamerposter's own 24.88pt \
calibration reads fluently; declare \
\\assert{ text.xheight >= ... } to take control")
      -- ISO 216 A0, landscape: beamerposter's default board. The measure
      -- band stays off as an honest gap: its judge reads the page text
      -- width, and a poster's column is the real measure.
      trimDefault := some (Dim.mm 1189, Dim.mm 841)
      safeMargin := some (Dim.mm 10) }

/-- The class fixes the page model: a poster is a face — one fixed,
printed, trimmed surface — by the record, definitionally. -/
public theorem poster_model_face : (DocClass.poster).record.model = .face := by rfl

/-- The font a package measures its lengths in as it loads: the preamble's
current font, which is Latin Modern at the class's `\normalsize`
(`optionNormalSize`: 10.95 pt under `11pt`) — its sans under beamer
(`ClassRecord.preambleSans`), its roman under the standard classes and
moderncv. booktabs assigns its `\dimen`s once, there (`\heavyrulewidth=.08em
… \belowrulesep=.65ex`, booktabs.dtx), so its em and ex are this face's and
never a table's own. The x-heights are lualatex's `\fontdimen5` of lmsans10
(4.44pt at 10pt) and lmroman10 (4.31pt), per mille of the size. A face the
document declares before booktabs loads would be the preamble's font
instead; the engine does not measure that one and names the loss (W0398). -/
public structure PreambleFace where
  size : Sp
  xHeight : Sp
  deriving Repr, BEq, Inhabited

/-- A class's preamble font at the `\normalsize` its size option sets. -/
public def PreambleFace.ofClass (rec : ClassRecord) (size : Sp) : PreambleFace :=
  let size := optionNormalSize size
  { size, xHeight := size * (if rec.preambleSans then 444 else 431) / 1000 }

/-- A length as the preamble font fixes it: its em at the class size, its ex
at Latin Modern's x-height there. -/
public def PreambleFace.resolve (face : PreambleFace) (l : Dim.Length) : Sp :=
  l.resolve face.size face.xHeight

/-- The table lengths a preamble declares (`tableLengths`' names), as LaTeX
assigns them: `\setlength` evaluates its em and ex where it stands, which in
the preamble is the preamble's font (`PreambleFace`), so
`\setlength{\belowrulesep}{1ex}` is 4.31pt in a 10pt article whatever face
and size its tables set in. Every other token is left as declared, and so
is a table length a body declares: it resolves where the table reads it. -/
public def PreambleFace.fixTableLengths (face : PreambleFace) (tk : Tokens) : Tokens :=
  { entries := tk.entries.map fun (n, g) =>
      if (tableLengths.lookup n).isSome then
        (n, { g with width := Dim.Length.ofSp (face.resolve g.width) })
      else (n, g) }

/-- The poster's headline band: title, authors, institute — the `\title`
family read as class furniture, the way the gemini lineage's headline
template reads the declarations without a `\maketitle`
(beamerthemegemini.sty, the headline template over `\inserttitle`,
`\insertauthor`, `\insertinstitute`). One value both backends consume:
the PDF lays it as the face's page-top band in the `frametitle` roles,
HTML as the page's `<header>`. Assembled once, at `Elab`'s document
assembly, only for a class whose record declares the band
(`ClassRecord.headline`). -/
public structure Headline where
  title : Array Inline
  author : Array Inline := #[]
  institute : Array Inline := #[]
  deriving Repr, BEq, Inhabited

/-- One piece of recovered ink: the loss that named it, the command it stood
for, and the source text the recovery kept. `Salvage` is taken, and means
something else — where a floor's *characters* come from — so this carries the
other half of the same vocabulary: which construct the characters came from.

`subject` is the tie to the diagnostic that paid for it. Every refusal that
recovers goes through `Elab.warnOnce` with the key `"ctrl:<name>"`, which
lands on `Diag.subject` — the structured dedup key, never the message text
(`pending_named` is the shape this follows). So an entry is accounted for
when some diagnostic carries the same subject.
`Elab.control_completion_contract` proves recovery accounting at the executed
frontend's final output; `salvageChecks` checks that distinction over the
corpus and invented probes. -/
public structure Recovered where
  code : DiagCode
  /-- The refused command's name, without its backslash. -/
  command : String
  /-- The source the groups carried, as the author wrote it: what the census
  asks about when it wants to know whether a word on the page is salvage. -/
  text : String
  deriving Repr, BEq

/-- The diagnostic subject a recovery is paid for under: `warnOnce`'s own
key, so the accounting compares structured fields rather than parsing a
message. -/
@[expose] public def Recovered.subject (s : Recovered) : String := "ctrl:" ++ s.command

public structure Doc where
  docClass : DocClass := .article
  classOptions : String := ""
  page : PageSpec := {}
  fonts : FontSpec := {}
  palette : Palette := {}
  tokens : Tokens := {}
  /-- The caption positions the document declares (`captionPosOf` reads
  them): a float type's scope, or `""` for every type, and where its
  captions are placed for. -/
  captionPos : Array (String × CaptionPos) := #[]
  /-- `\runninghead` / `\runningfoot`: one line of inline content each, laid
  out in the margin after the body, when the page count is known. -/
  head : Option (Array Inline) := none
  foot : Option (Array Inline) := none
  /-- beamer's `\logo`: one piece of inline content — normally an image —
  placed at the lower-right corner of every page carrying running content,
  the way the head and foot are placed. -/
  logo : Option (Array Inline) := none
  /-- The headline band a headline class draws (`ClassRecord.headline`;
  the poster today): the `\title` family as furniture. `none` on every
  other class and when no title is declared. -/
  headline : Option Headline := none
  /-- `\logoleft` / `\logoright`: the headline band's two corner slots
  (the gemini lineage's own commands), each one piece of inline content —
  normally an image — placed by the furniture pass in the band's corner,
  the `\logo` machinery's shape. Only a page carrying the band draws
  them. -/
  logoLeft : Option (Array Inline) := none
  logoRight : Option (Array Inline) := none
  /-- First page that carries the running head (`\runninghead[from = 2]`
  keeps the opening page clean, as a title page is). The gate is the
  declaration's own: each `\runninghead` sets it — to its `[from]`, or back
  to 1 when the option is not given — and never its sibling's. -/
  headFrom : Nat := 1
  /-- First page that carries the running foot: `\runningfoot`'s own gate,
  the mirror of `headFrom`. `\thispagestyle{empty}` on the opening page sets
  both to `2` — fancyhdr's page style genuinely covers both. -/
  footFrom : Nat := 1
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
  /-- natbib as the document declared it: `none` when natbib is not loaded —
  LaTeX's own `\cite` then, numbers in square brackets — and otherwise its
  punctuation declarations in the order natbib applies them, in its own
  `\setcitestyle` vocabulary: a load's options expanded in natbib's
  declaration order, then each preamble `\setcitestyle`. Resolution replays
  them against the bibliography style (`Bib.CitePunct.ofDoc`), because the
  style may be declared after every citation. -/
  natbib : Option (Array String) := none
  /-- The boundary tool in force: the external TeX the driver runs for
  pictures outside the rendered subset — the document's pin
  (`\pictures{ tool = lualatex }`, or the `\tikzexternalize` spelling) or
  the engine default, the boundary being open by default. `none` is the
  declared refusal (`tool = none`): nothing routes, so no request rides. -/
  pictureTool : Option String := some "lualatex"
  /-- The boundary requests this document states: `(id, body)` — the
  picture's identity is the content hash of the author's bytes, and the
  body is the picture as written — the `bibRefs` shape. The request the
  driver fulfils is formed at the request site (`pictureRefs`): the body
  wrapped with `picturePreamble`, the document's font roles, and exactly
  the palette roles its body and carried declarations mention, so its
  colours and faces are the page's (`Design.ofDoc` reads the same palette).
  The result embeds through the image path as a measured form XObject. The trust
  label: the engine claims the *box*, never the contents. -/
  pictureSrcs : Array (String × String) := #[]
  /-- The preamble a boundary standalone needs beyond the document's
  design: non-native package loads and the tikz-family set lines, as
  written (`Compat.boundaryDecls`). Set once by the elaborator. -/
  picturePreamble : String := ""
  /-- The document's own macro definitions, in document order: the name,
  and the declaration as the boundary standalone reads it. Captured as the
  document wrote it rather than spelled back from a native `UserCmd`,
  because an optional argument's default is the one part the native form
  drops. The request site carries the subset its body and carried preamble
  reach (`macroDecls`, `macroDecls_covers`), so a picture that spells a
  document macro is drawn with it. -/
  pictureMacros : Array (String × String) := #[]
  /-- The ink this document carries that its author did not write: one entry
  per construct the engine refused and recovered, in flow order.

  The engine's floor for a construct it cannot render is that construct's
  *content*, never its spelling, and for prose that floor is right — a
  refused `\emph{text}` still ships "text". For a control-plane command the
  argument is a keyword, and the same floor puts a stray word on the page:
  `\setlayout{fullpage}` ships "fullpage" in both backends. Nothing could
  say so, because recovered ink was byte-identical to authored prose, and two
  claims failed on that: a statement that a control command's groups
  contribute no ink could not be made general, and an artifact check that
  content ink may not spell a preamble argument accused two innocent
  fixtures.

  A census rather than a mark in the tree, because both claims quantify over
  the *whole* document's ink — "the keyword is nowhere in it", "this ink is
  salvage, do not accuse it" — and neither asks where the salvage stands.
  What this therefore cannot answer is a claim about one region's ink; that
  wants a wrapper node, which costs an arm in every walk and both backends,
  and is worth paying when a claim needs it and not before. -/
  salvage : Array Recovered := #[]
  /-- Where the frame numbering starts over: the body index of the first
  block after `\appendix` in a deck that loads appendixnumberbeamer, whose
  `\appendix` keeps the main part's last number as its total and sets
  `framenumber` to 0 (`appendixnumberbeamer.sty`). `none` numbers the body
  whole. -/
  frameRestart : Option Nat := none
  body : Array Block := #[]
  deriving Repr, BEq, Inhabited

/-- The document's one frame numbering: the body numbered whole, or — where
`frameRestart` splits it — each part numbered from 1 on its own, as
appendixnumberbeamer leaves beamer's counter. T2–T4 hold over each part. -/
public def Doc.frameNumbers (doc : Doc) : Array (Option Nat) :=
  match doc.frameRestart with
  | none => Ir.frameNumbers doc.body
  | some p =>
    Ir.frameNumbers (doc.body.extract 0 p) ++ Ir.frameNumbers (doc.body.extract p doc.body.size)

/-- The numbering's denominator at body index `i`: the count of the part `i`
stands in — appendixnumberbeamer's `\inserttotalframenumber`, the main
part's count before the restart and the appendix's after it. -/
public def Doc.frameCountAt (doc : Doc) (i : Nat) : Nat :=
  match doc.frameRestart with
  | none => Ir.frameCount doc.body
  | some p =>
    if i < p then Ir.frameCount (doc.body.extract 0 p)
    else Ir.frameCount (doc.body.extract p doc.body.size)

/-- The numbering's denominator where the document starts. -/
public def Doc.frameCount (doc : Doc) : Nat :=
  doc.frameCountAt 0

/-- The document's preamble font: its class's (`PreambleFace.ofClass`) at
its class size. The one resolving site both backends read a table's
undeclared lengths from (`Layout.tableLength`, `HtmlDoc.tableLengthFallback`). -/
public def Doc.preambleFace (doc : Doc) : PreambleFace :=
  PreambleFace.ofClass doc.docClass.record doc.page.fontSize

/-- appendixnumberbeamer's numbering, exactly: split at the restart, the
main part numbers `1, …, M` and the appendix `1, …, A`, each gapless — T3
(`frameNumbers_gapless`) over each part. -/
public theorem Doc.frameNumbers_restart_exact (doc : Doc) (p : Nat)
    (h : doc.frameRestart = some p) :
    doc.frameNumbers.toList.filterMap id =
      List.range' 1 (Ir.frameCount (doc.body.extract 0 p)) ++
        List.range' 1 (Ir.frameCount (doc.body.extract p doc.body.size)) := by
  simp only [Doc.frameNumbers, h, Array.toList_append, List.filterMap_append,
    frameNumbers_gapless]

/-- The numbering indexes the body whole, restart or none: every consumer
reads position `i` for block `i`. -/
public theorem Doc.frameNumbers_size (doc : Doc) : doc.frameNumbers.size = doc.body.size := by
  unfold Doc.frameNumbers
  split
  · exact Ir.frameNumbers_size doc.body
  · simp only [Array.size_append, Ir.frameNumbers_size, Array.size_extract]
    omega

/-- Whether the artifacts carry the document's faces — the one resolving
site the HTML's font shipment and the PDF's embedding read. A declared
`fonts =` wins; undeclared, the rule is the one the driver always had: a
document that told no stylesheet story (`css` unset) ships its faces, one
that did (`css = own`, the site whose stylesheet owns fonts) ships none.
Declaring `fonts = embedded` beside `css = own` is how such a site opts
back in. -/
public def Doc.fontPolicy (doc : Doc) : FontPolicy :=
  match doc.output.contract.fonts with
  | some p => p
  | none => if doc.output.css.isNone then .embedded else .none

/-- Undeclared, the policy is exactly the stylesheet rule (`_exact`): the
refactor that made `shipFonts` a value changed no document's shipment. -/
public theorem Doc.fontPolicy_exact (doc : Doc) (h : doc.output.contract.fonts = none) :
    doc.fontPolicy = (if doc.output.css.isNone then .embedded else .none) := by
  simp [fontPolicy, h]

/-- Whether this document's pages carry the plain page number: the
document's own `\page{ numbers = ... }` wins; an undeclared document takes
its class record's default (`ClassRecord.pageNumbers`). One resolving site,
read by layout's furniture pass and the driver's glyph precompute alike. -/
@[expose] public def Doc.pageNumbersOn (doc : Doc) : Bool :=
  doc.page.numbers.getD doc.docClass.record.pageNumbers

/-- Whether counted body lines carry margin line numbers: the document's
own declaration and nothing else — no class default turns line numbers
on (the page key is a declared flag, never a default). One resolving
site, read by layout's furniture pass and the driver's glyph precompute
alike. -/
@[expose] public def Doc.lineNumbersOn (doc : Doc) : Bool :=
  doc.page.linenumbers.getD false

/-- The line-number modulus in force: 1 — every counted line — unless
declared. Floored at 1 so the printing test `count % modulus == 0` is
meaningful for every declaration that reached the spec. -/
public def Doc.lineModulo (doc : Doc) : Nat :=
  max 1 (doc.page.lineModulo.getD 1)

/-- Render a symbolic glue the way it was declared, so goldens show intent
rather than a resolved number. -/
public def dumpGlue (g : SymGlue) : String :=
  let part (l : Length) : String :=
    let bits := (if l.sp != 0 then [s!"{l.sp.toPtString}pt"] else []) ++
      (if l.em != 0 then [s!"{l.em}/1000em"] else []) ++
      (if l.ex != 0 then [s!"{l.ex}/1000ex"] else [])
    if bits.isEmpty then "0" else String.intercalate "+" bits
  let base := part g.width
  let plus := if g.stretch == ({} : Length) then "" else s!" plus {part g.stretch}"
  let minus := if g.shrink == ({} : Length) then "" else s!" minus {part g.shrink}"
  base ++ plus ++ minus

/-- A sourced glue as the golden shows it: the declared value, and the
token name it was resolved from when it had one. The name is what the
HTML defers to, so an elaboration that dropped it is visible here. -/
private def dumpSourcedGlue (g : Sourced SymGlue) : String :=
  match g.token with
  | some n => s!"{dumpGlue g.value} from {n}"
  | none => dumpGlue g.value

/-- LaTeX's own punctuation: the characters that are markup in a math
source and never its content. A page that ships one of these is showing a
reader its source, which is the one recovery no diagnostic may choose — the
honest floor for a construct the engine cannot model is the formula's text
content, never its spelling. `&`, `^` and `_` are on the list because this
is a *math* source: there the tab and the script marks are always markup,
where in ordinary text an ampersand is content.

A formula the parser *did* model is a different matter: there `\{` is the
author asking for a brace glyph, and `formulaFloor` ships it, because the
parse decided it was content. This list governs salvage from a source
string, where that decision was never reached. -/
public def markupChars : List Char := ['\\', '{', '}', '$', '&', '^', '_', '~']

/-- Control words whose leading `{...}` arguments name something rather
than carrying content, with how many of them do: `\textcolor{indigo}{q}`
sets `q` in a colour, so one argument is a name and the next is content,
while `\rule{1pt}{2pt}` is two lengths and no content at all. Without the
count the second length rode onto the page — markup-free by the character
test and still nonsense to a reader.

`\text`-like wrappers are deliberately absent: their argument *is* the
content, and that is what the floor exists to keep.

`\cancelto` earns its row for a sharper reason than the rest: its value
argument is not merely noise on the page but a *false reading* —
`\cancelto{0}{x}` shipped `0x`, a product, where the source says `x`
cancels to `0`. A lossy floor is the contract; a floor that states the
opposite of the source is not. Native math carries the strike and value;
this policy still governs recovery when another construct makes the
whole formula unrenderable, or a use appears outside mathematics. -/
public def floorNamedArgs : List (String × Nat) :=
  [("textcolor", 1), ("colorbox", 1), ("fcolorbox", 2), ("color", 1),
   ("pagecolor", 1), ("label", 1), ("ref", 1), ("eqref", 1), ("tag", 1),
   ("hspace", 1), ("vspace", 1), ("raisebox", 1), ("begin", 1), ("end", 1),
   ("cite", 1), ("phantom", 1), ("hphantom", 1), ("vphantom", 1),
   ("parbox", 1), ("rule", 2), ("setlength", 2), ("addtolength", 2),
   ("cancelto", 1)]

/-- Past a balanced `{...}` beginning at `i`, or past the end when it never
closes. An index loop, so the bound is the array and no measure is owed. -/
private def skipBalanced (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  let mut depth := 0
  for _ in [0:cs.size + 1] do
    if j ≥ cs.size then break
    let c := (cs[j]?).getD ' '
    if c == '{' then
      depth := depth + 1
      j := j + 1
    else if c == '}' then
      j := j + 1
      if depth ≤ 1 then break else depth := depth - 1
    else
      j := j + 1
  return j

/-- Past a `[...]` option run beginning at `i`, else `i` itself. A naming
command's option run is markup with its arguments — without this step
`\textcolor[rgb]{1,0,0}{x}` spent its named argument on the colour triple
and shipped `rgb` as ink. -/
private def skipOption (cs : Array Char) (i : Nat) : Nat := Id.run do
  if (cs[i]?).getD ' ' != '[' then return i
  let mut j := i + 1
  for _ in [0:cs.size + 1] do
    if j ≥ cs.size then break
    let c := (cs[j]?).getD ' '
    j := j + 1
    if c == ']' then break
  return j

/-- Past the spaces at `i`. -/
private def skipFloorWs (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:cs.size + 1] do
    if j ≥ cs.size then break
    if !((cs[j]?).getD 'x').isWhitespace then break
    j := j + 1
  return j

/-- Which characters of a math source are content: one flag per character.
A control sequence's name is markup, and so are the leading arguments a
`floorNamedArgs` command names rather than fills. Everything else is
content — the character test (`markupChars`) then removes LaTeX's
punctuation, so the two filters are independent and the salvage is
markup-free whatever this walk decides.

A naming command's arguments are consumed *positionally*, here at the
command, rather than by a counter the next brace anywhere satisfies: the
counter form let `\color\textcolor{red}{x}` spend one drop on `{red}` and
the other on the content `{x}`, deleting the formula's only content with
nothing said about it.

Index loops throughout, so the bounds are the array and no measure is
owed. -/
public def floorMask (src : String) : Array Bool := Id.run do
  let cs := src.toList.toArray
  let at? (k : Nat) : Char := (cs[k]?).getD ' '
  let mut keep : Array Bool := Array.replicate cs.size true
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    if at? i != '\\' then
      i := i + 1
    else
      keep := keep.setIfInBounds i false
      let mut j := i + 1
      if j < cs.size && !(at? j).isAlpha then
        -- a control symbol is one character: `\\`, `\,`, `\{`
        let sym := at? j
        keep := keep.setIfInBounds j false
        j := j + 1
        -- `\\[2ex]` is how an author spaces an array's rows, so the row
        -- separator's own option run is markup with it. Only this one: after
        -- `\{` or `\,` a bracket is content.
        if sym == '\\' then
          let optStart := skipFloorWs cs j
          let stop := skipOption cs optStart
          if stop != optStart then
            for m in [j:stop] do
              keep := keep.setIfInBounds m false
            j := stop
      else
        let mut name := ""
        for _ in [0:cs.size + 1] do
          if j ≥ cs.size then break
          if !(at? j).isAlpha then break
          name := name.push (at? j)
          keep := keep.setIfInBounds j false
          j := j + 1
        -- a starred command's star is part of its name: without this the
        -- positional scan below looked for `{` and found `*`, so
        -- `\hspace*{1pt}` shipped its length.
        let star := skipFloorWs cs j
        if at? star == '*' then
          for m in [j:star + 1] do
            keep := keep.setIfInBounds m false
          j := star + 1
        -- An option run immediately after the name is this command's, as
        -- LaTeX reads it, whether or not the engine knows the command:
        -- `\sqrt[3]{8}` shipped `[3]` and `\zzz[opt]{x}` shipped `[opt]`
        -- because only a `floorNamedArgs` command ever swept one. The same
        -- drop is already made in text (inside W0301's own accounting) and
        -- in a node body, so this
        -- is one rule at its third site rather than a new judgement. It is
        -- keyed on the control word and not on the bracket: `[0,1]` standing
        -- after no command is an interval, and content.
        let optStart := skipFloorWs cs j
        let optStop := skipOption cs optStart
        if optStop != optStart then
          for m in [j:optStop] do
            keep := keep.setIfInBounds m false
          j := optStop
        if let some arity := floorNamedArgs.lookup name then
          for _ in [0:arity] do
            let opened := skipFloorWs cs (skipOption cs (skipFloorWs cs j))
            -- The run up to the group — the space after the name and any
            -- option run — is the command's too. Masked before the `{`
            -- test, not inside it: masking only on the success path left
            -- `[rgb]` on the page whenever the scan gave up.
            for m in [j:opened] do
              keep := keep.setIfInBounds m false
            if at? opened != '{' then
              j := opened
              break
            let stop := skipBalanced cs opened
            for m in [opened:stop] do
              keep := keep.setIfInBounds m false
            j := stop
          -- `\raisebox{lift}[height][depth]{body}`: the options trail the
          -- named argument, so they are swept after the arity loop.
          for _ in [0:2] do
            let stop := skipOption cs j
            if stop == j then break
            for m in [j:stop] do
              keep := keep.setIfInBounds m false
            j := stop
      i := j
  -- A second pass over the same mask squeezes the whitespace a dropped
  -- command leaves behind: `\overset {x}` writes a space after its name,
  -- and keeping it would indent the salvage. Dropping a character never
  -- breaks the membership property `floorInk_mem` reads off the filter.
  let survives (k : Nat) : Bool :=
    (keep[k]?.getD false) && !markupChars.contains (at? k)
  let mut lastSpace := true
  for k in [0:cs.size] do
    if survives k then
      if (at? k).isWhitespace then
        if lastSpace then keep := keep.setIfInBounds k false
        else lastSpace := true
      else lastSpace := false
  let mut last := cs.size
  for _ in [0:cs.size + 1] do
    if last == 0 then break
    let k := last - 1
    if survives k then
      if (at? k).isWhitespace then keep := keep.setIfInBounds k false else break
    last := k
  return keep

/-- What the salvage keeps: the math source's own content characters, with
LaTeX's punctuation removed. Stated as a filter over the source so every
character of it is a character of the source by construction — nothing is
invented, and `floorInk_mem` reads straight off the filter. -/
public def floorChars (src : String) : List Char :=
  let mask := floorMask src
  (src.toList.zipIdx.filterMap fun (c, i) =>
    if (mask[i]?.getD true) && !markupChars.contains c then some c else none)

/-- The declared placeholder a formula sets when the salvage comes to
nothing: `$\overset{\alpha}{\beta}$` is markup and symbol commands end to
end, so its content characters are none at all, and the alternative to a
placeholder is a blank where an equation stood. A blank is not an honest
floor either — it tells a reader nothing was there. Bracketed, so it reads
as a placeholder rather than as content, and markup-free, so it cannot
break the property it is inserted under.

It reaches the tagged tree and the alternative text as well as the page, and
that is deliberate: a screen reader hearing nothing where an equation stood
learns less than one hearing a placeholder, which is the same argument that
put it on the page. -/
public def mathFloorPlaceholder : List Char := ['[', '\u2026', ']']

/-- The characters a degraded formula actually inks: its salvage, or the
declared placeholder when the salvage is empty. `floorInk_accounts` is the
statement that the second case is never silent. -/
public def floorInk (src : String) : List Char :=
  let cs := floorChars src
  if cs.isEmpty then mathFloorPlaceholder else cs

/-- The honest floor for math the elaborator cannot model: the formula's
text content, or a visible placeholder when it has none. The alternative —
setting the source as body text — puts control sequences on the page where
an equation belongs, which is the worst recovery available: the reader is
shown markup and cannot tell it from content. Both backends read this one
function, so the floor is one decision; the construct is still named by its
diagnostic, so the loss is announced rather than displayed.

The floor drops a symbol command rather than translating it: the symbol
table sits above the IR (it belongs to the math surface, which no backend
may reach into), so a translating floor would either duplicate the table or
invert the layering. A dropped symbol is named by the diagnostic; a shipped
backslash is not. -/
public def mathFloor (src : String) : String := String.ofList (floorInk src)

/-- Math accents shared by parsing and the textual formula reading. The
combining marks and stretch flags are unicode-math's accent table;
`overline` uses U+0305 (TeXbook Appendix G, rule 9). -/
public def mathAccentCommands : List (String × Char × Bool) :=
  [("hat", '\u0302', false), ("widehat", '\u0302', true),
   ("tilde", '\u0303', false), ("widetilde", '\u0303', true),
   ("bar", '\u0304', false), ("dot", '\u0307', false), ("ddot", '\u0308', false),
   ("vec", '\u20D7', false), ("overline", '\u0305', true)]

namespace FormulaText

-- The math AST has its own mutually recursive lists, nuclei and grids.
-- A structural reading needs their boundaries; the glyph-coverage census
-- deliberately omits operators drawn as rules and cannot supply this text.
private def grouped (s : String) : String := (String.singleton '(' ++ s).push ')'

private def optionalChar : Option Char → String
  | none => ""
  | some c => String.singleton c

private def script (marker body : String) : String :=
  if body.isEmpty then "" else
    let text := grouped body
    marker ++ text

private def scripts (base sup sub : String) : String :=
  if sup.isEmpty && sub.isEmpty then base
  else grouped base ++ script "_" sub ++ script "^" sup

private def fraction (spec : Math.FracSpec) (num den : String) : String :=
  optionalChar spec.left ++
    (if spec.rule = some 0 then
      if num.isEmpty && den.isEmpty then "" else "stack" ++ grouped (num ++ ";" ++ den)
     else grouped num ++ "/" ++ grouped den) ++
    optionalChar spec.right

private def radical (degree body : String) : String :=
  let text := grouped body
  if degree.isEmpty then
    "sqrt" ++ text
  else
    let index := grouped degree
    "root" ++ index ++ text

private def cancellation (mark : Math.CancelMark) (value body : String) : String :=
  let name := match mark with
    | .up => "cancel" | .down => "bcancel" | .cross => "xcancel" | .to => "cancelto"
  let text := grouped (body ++
    (if mark = .to then ";" ++ value
     else if value.isEmpty then "" else ";" ++ value))
  name ++ text

mutual

private def list (acc : String) : Math.MList → String
  | .nil => acc
  | .cons x rest => list (acc ++ item x) rest

private def item : Math.MItem → String
  | .atom _ n sup sub _ => scripts (nucleus n) (list "" sup) (list "" sub)
  | .space _ => ""
  | .ink _ _ => ""

private def nucleus : Math.MNucleus → String
  | .sym c => String.singleton c
  | .styled _ c => String.singleton c
  | .word s => s
  | .list body => list "" body
  | .alpha _ _ body => list "" body
  | .frac spec num den => fraction spec (list "" num) (list "" den)
  | .rad deg body => radical (list "" deg) (list "" body)
  | .delim left right body =>
    let text := optionalChar left ++ list "" body
    let close := optionalChar right
    text ++ close
  | .big d _ => optionalChar d
  | .grid _ rs =>
    let text := rows "" rs
    if text.isEmpty then "" else "[" ++ text ++ "]"
  | .accent mark wide body =>
    let name := ((mathAccentCommands.find? (fun p => p.2 == (mark, wide))).map (·.1)).getD "accent"
    name ++ grouped (list "" body)
  | .cancel mark _ value body => cancellation mark (list "" value) (list "" body)

private def row (acc : String) : Math.MRow → String
  | .nil => acc
  | .cons c rest => row (acc ++ list "" c ++ (match rest with
      | .nil => "" | .cons _ _ => ",")) rest

private def rows (acc : String) : Math.MRows → String
  | .nil => acc
  | .cons r rest => rows (acc ++ "[" ++ row "" r ++ "]" ++ (match rest with
      | .nil => "" | .cons _ _ => ",")) rest

end

private theorem script_length (marker body : String) : body.length ≤ (script marker body).length := by
  simp only [script]
  split
  · rename_i h
    simp_all
  · simp [grouped, String.length_append]
    omega

private theorem scripts_length (base sup sub : String) :
    base.length + sup.length + sub.length ≤ (scripts base sup sub).length := by
  simp only [scripts]
  split
  · rename_i h
    simp_all
  · have hs := script_length "^" sup
    have hb := script_length "_" sub
    simp only [grouped, String.length_append, String.length_push, String.length_singleton] at *
    omega

private theorem fraction_length (spec : Math.FracSpec) (num den : String) :
    (optionalChar spec.left).length + num.length + den.length + (optionalChar spec.right).length ≤
      (fraction spec num den).length := by
  simp only [fraction]
  split
  · split
    · rename_i h
      simp_all
    · simp only [grouped, String.length_append, String.length_push, String.length_singleton]
      omega
  · simp only [grouped, String.length_append, String.length_push, String.length_singleton]
    omega

private theorem radical_length (deg body : String) :
    deg.length + body.length ≤ (radical deg body).length := by
  simp only [radical]
  split
  · rename_i h
    simp_all [grouped]
    omega
  · simp only [grouped, String.length_append, String.length_push, String.length_singleton]
    omega

private theorem cancellation_length (mark : Math.CancelMark) (value body : String) :
    body.length + value.length ≤ (cancellation mark value body).length := by
  cases mark <;> by_cases h : value.isEmpty <;> simp_all [cancellation, grouped] <;> omega

mutual

private theorem list_length : ∀ (body : Math.MList) (chars : Array Char) (text : String),
    (Math.MList.scalarsList chars body).size + text.length ≤ (list text body).length + chars.size
  | .nil, _, _ => by simp [list, Math.MList.scalarsList, Nat.add_comm]
  | .cons x rest, chars, text => by
    have hx := item_length x chars
    have hr := list_length rest (x.scalars chars) (text ++ item x)
    simp only [list, Math.MList.scalarsList, String.length_append] at *
    omega

private theorem item_length : ∀ (x : Math.MItem) (chars : Array Char),
    (x.scalars chars).size ≤ chars.size + (item x).length
  | .space _, _ => by simp [item, Math.MItem.scalars]
  | .ink _ _, _ => by simp [item, Math.MItem.scalars]
  | .atom _ n sup sub _, chars => by
    have hn := nucleus_length n chars
    have hs := list_length sup (n.scalars chars) ""
    have hb := list_length sub (Math.MList.scalarsList (n.scalars chars) sup) ""
    have h := scripts_length (nucleus n) (list "" sup) (list "" sub)
    simp only [item, Math.MItem.scalars, String.length_empty, Nat.add_zero] at *
    omega

private theorem nucleus_length : ∀ (n : Math.MNucleus) (chars : Array Char),
    (n.scalars chars).size ≤ chars.size + (nucleus n).length
  | .sym c, _ => by simp [Math.MNucleus.scalars, nucleus]
  | .styled _ c, _ => by simp [Math.MNucleus.scalars, nucleus]
  | .word s, _ => by
    simp [Math.MNucleus.scalars, nucleus, String.foldl_eq_foldl_toList, String.length_toList]
  | .list b, chars => by
    simpa [Math.MNucleus.scalars, nucleus, Nat.add_comm] using list_length b chars ""
  | .alpha _ _ b, chars => by
    simpa [Math.MNucleus.scalars, nucleus, Nat.add_comm] using list_length b chars ""
  | .frac spec num den, chars => by
    have hn := list_length num (match spec.left with
      | none => chars | some c => chars.push c) ""
    have hd := list_length den (Math.MList.scalarsList (match spec.left with
      | none => chars | some c => chars.push c) num) ""
    have h := fraction_length spec (list "" num) (list "" den)
    simp only [Math.MNucleus.scalars, nucleus]
    cases hl : spec.left <;> cases hr : spec.right <;>
      simp [hl, hr, optionalChar, String.length_empty] at * <;> omega
  | .rad deg b, chars => by
    have hd := list_length deg chars ""
    have hb := list_length b (Math.MList.scalarsList chars deg) ""
    have h := radical_length (list "" deg) (list "" b)
    simp only [Math.MNucleus.scalars, nucleus, String.length_empty, Nat.add_zero] at *
    omega
  | .delim l r b, chars => by
    have h := list_length b (match r with
      | none => (match l with | none => chars | some c => chars.push c)
      | some c => (match l with | none => chars | some c => chars.push c).push c) ""
    cases l <;> cases r <;>
      simp_all [Math.MNucleus.scalars, nucleus, optionalChar, String.length_append] <;> omega
  | .big d _, chars => by
    cases d <;> simp [Math.MNucleus.scalars, nucleus, optionalChar]
  | .grid _ rs, chars => by
    have h := rows_length rs chars ""
    simp only [Math.MNucleus.scalars, nucleus]
    split
    · rename_i hz
      simp_all
    · simp only [String.length_append]
      simp only [String.length_empty, Nat.add_zero] at h
      omega
  | .accent mark _ b, chars => by
    have h := list_length b (if mark == '\u0305' then chars else chars.push mark) ""
    simp only [Math.MNucleus.scalars, nucleus, grouped, String.length_append,
      String.length_push, String.length_singleton]
    split <;> simp_all <;> omega
  | .cancel mark _ value b, chars => by
    have hb := list_length b chars ""
    have hv := list_length value (Math.MList.scalarsList chars b) ""
    have h := cancellation_length mark (list "" value) (list "" b)
    simp only [Math.MNucleus.scalars, nucleus, String.length_empty, Nat.add_zero] at *
    omega

private theorem row_length : ∀ (r : Math.MRow) (chars : Array Char) (text : String),
    (r.scalarsRow chars).size + text.length ≤ (row text r).length + chars.size
  | .nil, _, _ => by simp [row, Math.MRow.scalarsRow, Nat.add_comm]
  | .cons c rest, chars, text => by
    have hc := list_length c chars ""
    have hr := row_length rest (Math.MList.scalarsList chars c)
      (text ++ list "" c ++ (match rest with | .nil => "" | .cons _ _ => ","))
    simp only [row, Math.MRow.scalarsRow, String.length_append, String.length_empty,
      Nat.add_zero] at *
    omega

private theorem rows_length : ∀ (rs : Math.MRows) (chars : Array Char) (text : String),
    (rs.scalarsRows chars).size + text.length ≤ (rows text rs).length + chars.size
  | .nil, _, _ => by simp [rows, Math.MRows.scalarsRows, Nat.add_comm]
  | .cons r rest, chars, text => by
    have hc := row_length r chars ""
    have hr := rows_length rest (r.scalarsRow chars)
      (text ++ "[" ++ row "" r ++ "]" ++ (match rest with | .nil => "" | .cons _ _ => ","))
    simp only [rows, Math.MRows.scalarsRows, String.length_append, String.length_empty,
      Nat.add_zero] at *
    omega

end

mutual

private theorem list_mapInk (f : Ir.Color → Option String → Ir.Color) :
    ∀ (body : Math.MList) (acc : String), list acc (Math.MList.mapInk f body) = list acc body
  | .nil, _ => rfl
  | .cons x rest, acc => by
    simp only [Math.MList.mapInk, list, item_mapInk f x, list_mapInk f rest]

private theorem item_mapInk (f : Ir.Color → Option String → Ir.Color) :
    ∀ (x : Math.MItem), item (Math.MItem.mapInk f x) = item x
  | .space _ => rfl
  | .ink _ _ => rfl
  | .atom _ n sup sub _ => by
    simp only [Math.MItem.mapInk, item, nucleus_mapInk f n, list_mapInk f sup,
      list_mapInk f sub]

private theorem nucleus_mapInk (f : Ir.Color → Option String → Ir.Color) :
    ∀ (n : Math.MNucleus), nucleus (Math.MNucleus.mapInk f n) = nucleus n
  | .sym _ => rfl
  | .styled _ _ => rfl
  | .word _ => rfl
  | .list body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f body]
  | .alpha _ _ body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f body]
  | .frac _ num den => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f num, list_mapInk f den]
  | .rad deg body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f deg, list_mapInk f body]
  | .delim _ _ body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f body]
  | .big _ _ => rfl
  | .grid _ rs => by
    simp only [Math.MNucleus.mapInk, nucleus, rows_mapInk f rs]
  | .accent _ _ body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f body]
  | .cancel _ _ value body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f value, list_mapInk f body]

private theorem row_mapInk (f : Ir.Color → Option String → Ir.Color) :
    ∀ (r : Math.MRow) (acc : String), row acc (Math.MRow.mapInk f r) = row acc r
  | .nil, _ => rfl
  | .cons c rest, acc => by
    simp only [Math.MRow.mapInk, row, list_mapInk f c]
    rw [row_mapInk f rest]
    cases rest <;> rfl

private theorem rows_mapInk (f : Ir.Color → Option String → Ir.Color) :
    ∀ (rs : Math.MRows) (acc : String), rows acc (Math.MRows.mapInk f rs) = rows acc rs
  | .nil, _ => rfl
  | .cons r rest, acc => by
    simp only [Math.MRows.mapInk, rows, row_mapInk f r]
    rw [rows_mapInk f rest]
    cases rest <;> rfl

end

end FormulaText

/-- The shared plaintext reading of a parsed formula: fallback page text,
picture labels, alternatives, outlines and tagged structure all read this.
Grouping, `/`, scripts, roots and matrices follow AsciiMath's linear
notation (https://asciimath.org/#syntax). Ruleless fractions are named
`stack(num;den)`; cancellation names the mark and its operands; accents
use the same names and marks as the parser.

This is a readable structural floor, not a round-trip serialization of
arbitrary word atoms. Parsed literal characters bypass the source filter:
a parsed brace is content. Nonprinting spaces, ink switches and absent
delimiters stay empty. -/
public def formulaFloor (body : Math.MList) : String := FormulaText.list "" body

/-- The independent glyph census is a lower bound on the length of the
structured recovery. In particular, a formula with a nonempty parsed census
cannot recover to an empty string. This is character accounting, not a
claim that every source token denotes a glyph. -/
public theorem formulaFloor_content_covers (body : Math.MList) :
    (Math.MList.scalarsList #[] body).size ≤ (formulaFloor body).length := by
  simpa [formulaFloor] using FormulaText.list_length body #[] ""

/-- Recolouring preserves the complete structural reading, including the
operators and grouping that the scalar census does not count. -/
public theorem formulaFloor_ink_id (f : Color → Option String → Color) (body : Math.MList) :
    formulaFloor (Math.MList.mapInk f body) = formulaFloor body :=
  FormulaText.list_mapInk f body ""

/-- Fraction operands never read as their bare juxtaposition, even when
one or both operands are empty. Grouping and the division sign belong to
the shared structural reading, independently of the eventual backend. -/
public theorem formulaFloor_separates (num den : Math.MList) :
    formulaFloor (.cons (.atom .ord (.frac {} num den) .nil .nil false) .nil) ≠
      formulaFloor num ++ formulaFloor den := by
  intro h
  have hlen := congrArg String.length h
  simp [formulaFloor, FormulaText.list, FormulaText.item, FormulaText.nucleus,
    FormulaText.scripts, FormulaText.fraction, FormulaText.optionalChar, FormulaText.grouped,
    String.length_append] at hlen
  omega

/-- Nothing invented and no markup: every character of a formula's salvage
is a character of its source, and none of them is LaTeX punctuation. The
recoveries this replaced shipped the source itself, markup and all.

What this does *not* say, since the distinction matters: it is an upper
bound. It rules out invention and markup, and it holds for any `floorMask`
whatever — including one that dropped everything. The lower bound is
`floorChars_id`, which reads the index loops to establish the converse
for literal content. The executable half meanwhile is the
whole-string rows in `recoveryChecks`, which fail under both an
all-dropping and an all-keeping mask. -/
public theorem floorChars_mem (src : String) :
    ∀ c ∈ floorChars src, c ∈ src.toList ∧ c ∉ markupChars := by
  intro c hc
  simp only [floorChars, List.mem_filterMap] at hc
  obtain ⟨p, hp, hq⟩ := hc
  by_cases hk : (floorMask src)[p.2]?.getD true && !markupChars.contains p.1
  · simp only [hk, ite_true] at hq
    cases hq
    refine ⟨?_, ?_⟩
    · have hm : p.1 ∈ (src.toList.zipIdx 0).map Prod.fst := List.mem_map_of_mem hp
      rw [List.zipIdx_map_fst] at hm
      exact hm
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
      simpa using hk.2
  · simp only [Bool.not_eq_true] at hk
    simp only [hk] at hq
    simp at hq

/-- A `filterMap` that keeps every element is the projection it keeps. -/
private theorem filterMap_eq_map_fst {α β : Type} (l : List (α × β)) (g : α × β → Option α)
    (hg : ∀ p ∈ l, g p = some p.1) : l.filterMap g = l.map Prod.fst := by
  induction l with
  | nil => simp
  | cons p rest ih =>
    rw [List.filterMap_cons, hg p (by simp), List.map_cons,
      ih (fun q hq => hg q (by simp [hq]))]

/-- **The mask of a markup-free source keeps every index.** Each of
`floorMask`'s three loops preserves "the mask is still all-true": the
naming-argument scan because no character is a backslash, so the branch
that drops one is unreachable; the whitespace squeeze and the trailing trim
because no character is whitespace — and the trim's own `survives` test
supplies the bound that makes its character readable, so the invariant
needs nothing about the descending cursor. -/
public theorem floorMask_id (src : String)
    (h : ∀ c ∈ src.toList, c ≠ '\\' ∧ c ∉ markupChars ∧ c.isWhitespace = false) :
    floorMask src = Array.replicate src.toList.length true := by
  have hat : ∀ i, i < src.toList.length → (src.toList[i]?.getD ' ') ∈ src.toList := by
    intro i hi
    rw [List.getElem?_eq_getElem hi]
    simp [List.getElem_mem]
  have hws : ∀ i, i < src.toList.length →
      (src.toList[i]?.getD ' ').isWhitespace = false :=
    fun i hi => (h _ (hat i hi)).2.2
  have hbs : ∀ i, i < src.toList.length → (src.toList[i]?.getD ' ') ≠ '\\' :=
    fun i hi => (h _ (hat i hi)).1
  have hrep : ∀ j, ((Array.replicate src.toList.length true)[j]?).getD false = true →
      j < src.toList.length := by
    intro j hj
    simp only [Array.getElem?_replicate] at hj
    split at hj
    · assumption
    · simp at hj
  simp only [floorMask, List.size_toArray]
  refine Loop.bind_eq_of_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _
    (Loop.forIn_range_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _ _ rfl ?step1) ?rest
  case step1 =>
    intro i _ _ b hb
    split
    · exact hb
    · rename_i hlt
      split
      · exact hb
      · rename_i hne
        exact absurd (by simpa using hne) (hbs b.2 (by omega))
  case rest =>
  intro b hb
  rw [hb]
  refine Loop.bind_eq_of_inv (fun (st : Array Bool × Bool) =>
      st.1 = Array.replicate src.toList.length true) _ _ _
    (Loop.forIn_range_inv (fun (st : Array Bool × Bool) =>
      st.1 = Array.replicate src.toList.length true) _ _ _ _ rfl ?step2) ?rest2
  case step2 =>
    intro i _ hi c hc
    split
    · split
      · rename_i hw; exact absurd hw (by simp [hws i hi])
      · exact hc
    · exact hc
  case rest2 =>
  intro c hc
  rw [hc]
  refine Loop.bind_eq_of_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _
    (Loop.forIn_range_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _ _ rfl ?step3) ?rest3
  case step3 =>
    intro i _ _ d hd
    split
    · exact hd
    · split
      · rename_i hsv
        have hlt : d.2 - 1 < src.toList.length := hrep _ (by
          simpa using (Bool.and_eq_true _ _ ▸ hsv : _ ∧ _).1)
        split
        · rename_i hw; exact absurd hw (by simp [hws _ hlt])
        · exact hd
      · exact hd
  case rest3 =>
  intro d hd
  exact hd

/-- A math source with no control sequence, no LaTeX punctuation and no
whitespace salvages to exactly itself: the floor keeps content, it is not
merely free to drop it. The membership bound alone permits an all-dropping mask;
this identity rules that out on literal content. -/
public theorem floorChars_id (src : String)
    (h : ∀ c ∈ src.toList,
      c ≠ '\\' ∧ c ∉ markupChars ∧ c.isWhitespace = false) :
    floorChars src = src.toList := by
  simp only [floorChars, floorMask_id src h]
  rw [filterMap_eq_map_fst]
  · exact List.zipIdx_map_fst 0 src.toList
  · intro p hp
    have hmem : p.1 ∈ src.toList := by
      have hm := List.mem_map_of_mem (f := Prod.fst) hp
      rwa [List.zipIdx_map_fst] at hm
    simp [Array.getElem?_replicate, (h _ hmem).2.1]
    split <;> simp


/-- The same fact over what actually reaches the page: every character a
degraded formula inks is a character of its source or one of the declared
placeholder's, and none of them is LaTeX punctuation. -/
public theorem floorInk_mem (src : String) :
    ∀ c ∈ floorInk src,
      (c ∈ src.toList ∨ c ∈ mathFloorPlaceholder) ∧ c ∉ markupChars := by
  intro c hc
  simp only [floorInk] at hc
  split at hc
  · refine ⟨Or.inr hc, ?_⟩
    simp only [mathFloorPlaceholder, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> decide
  · obtain ⟨hsrc, hmk⟩ := floorChars_mem src c hc
    exact ⟨Or.inl hsrc, hmk⟩

/-- An empty salvage is paid for, never shipped as a blank: a formula whose
content characters are all markup inks the declared placeholder instead, so
the page says something stood here. What it does not say is *what* — that is
the diagnostic's, and `elabMathInline` words the empty case separately so the
warning and the page agree. -/
public theorem floorInk_accounts (src : String) : floorInk src ≠ [] := by
  simp only [floorInk]
  split
  · simp [mathFloorPlaceholder]
  · rename_i h
    simpa [List.isEmpty_iff] using h

/-- Where a salvage's characters come from, which is what decides how much
of the floor is checkable. The provenance rule the floor entries argue for,
as a value the judge reads rather than a distinction three docstrings make
in prose.

`filtered` is salvage from an unparsed source: no parse decided anything, so
the result is a subsequence of what the author wrote and LaTeX's punctuation
is markup by the character test. `floorChars` is the one filtered salvage.

`translated` is what a *parse* decided was content: the characters are the
parse's own and not the source's. `\{` arrives as `{` because the author
asked for a brace glyph and `x` arrives as `𝑥` because that is the letter a
math list sets, so the character test would delete exactly what was meant —
a reviewer once read both as leaks, which is the warning that this rule is
easy to misread. `formulaFloor` and a node body's salvage are translated. -/
public inductive Salvage where
  | filtered
  | translated
  deriving Repr, BEq, DecidableEq

/-- **The recovery floor as one judge, and the only thing every floor
shares.** `Loss.floor` declares what a construct's place owes a reader; this
says whether a salvage delivered it. Three clauses, each the generalisation
of a statement that already stood at one floor and was re-derived at the
next:

* *shipped only where something is owed* — a `.refuse` or `.inert` floor
  inks nothing. A run that writes no artifact has no page for a recovery to
  stand on, and a construct with no content operand has nothing to salvage,
  so ink in either place is invention rather than recovery. This is the
  clause that keeps a `config` code from acquiring a placeholder.
* *paid for* — a floor that owes ink delivers it whenever the construct
  carried content. `floorInk_accounts` is this clause at the math floor and
  `Picture.labelFloor_accounts` at a node label's, and the second was
  written from scratch after the first was on the record.
* *drawn, and markup-free* — every character shipped is one the construct
  carried or one of the declared placeholder's, and none of them is LaTeX's
  punctuation. `floorChars_mem` is this clause, and it binds a `filtered`
  salvage only: a parse's decision about what is content is not this judge's
  to overrule.

What the judge deliberately does not express is the corollary the
`\cancelto` entry adds — that the kept fragments may not compose into a
*different* well-formed claim. `0x` where `x` cancels to `0` passes all
three clauses and is still false, because the defect is in the arrangement
rather than in any character. `floorNamedArgs` is the mechanism for the
cases where dropping an operand fixes it; where both fragments are content
the repair is a separator, which is `formulaFloor_separates`. -/
@[expose] public def FloorHonest (f : Floor) (s : Salvage) (carried ink : List Char) : Prop :=
  (f.ships = false → ink = []) ∧
  (f.inks = true → carried ≠ [] → ink ≠ []) ∧
  (s = .filtered → ∀ c ∈ ink,
    (c ∈ carried ∨ c ∈ mathFloorPlaceholder) ∧ c ∉ markupChars)

/-- Every shipping recovery code pays for a parsed formula's content.
The reference is the parsed glyph census, independent of the formatter;
raw source punctuation and length parameters can be intentionally nonprinting
(`\big.` and an empty ruleless `\genfrac`, for example). This does not assert
that the parser preserves arbitrary source content. -/
public theorem formulaFloor_covers (c : DiagCode) (h : c.floor.ships) (body : Math.MList) :
    FloorHonest c.floor .translated
      (Math.MList.scalarsList #[] body).toList (formulaFloor body).toList := by
  refine ⟨fun hn => absurd (h.symm.trans hn) (by decide), fun _ hc hi => ?_,
    fun hn => nomatch hn⟩
  have hc' : (Math.MList.scalarsList #[] body).size > 0 := by
    simpa [← Array.length_toList, List.length_pos_iff] using hc
  have hi' : (formulaFloor body).length = 0 := by
    simpa [String.length_toList] using congrArg List.length hi
  have bound := formulaFloor_content_covers body
  omega

/-- Did this construct carry content at all? The source's own content
characters, read through the same mask the floor reads, so "carried content"
is one question with one answer and not a judgement each raise site makes.

A diagnostic that names a loss where the answer is no is naming a non-loss,
which dilutes its one meaning and fails a `--werror` run for free — the
defect W0385's own five neutral names were found to have. A raise site whose
construct may carry nothing reads this before it warns. -/
public def floorCarries (src : String) : Bool := !(floorChars src).isEmpty

/-- **Every registered code's floor is discharged by the salvage, for every
code.** A diagnostic inherits its recovery from the loss it declares and
chooses nothing: whatever a code in the registry demands of the construct's
place, the math floor delivers. This is `floorInk_mem` and
`floorInk_accounts` as one statement keyed on the loss — the two halves that
stood in two places and were then derived a third time from scratch at a
third site.

The hypothesis is the one real constraint, and it is a routing rule rather
than a formality: `floorInk` inks unconditionally, so a code whose floor
does not ship may not be routed here. Sending a `config` or `info` code to
this floor would put the declared placeholder where nothing was lost. -/
public theorem floorInk_covers (c : DiagCode) (h : c.floor.ships) (src : String) :
    FloorHonest c.floor .filtered src.toList (floorInk src) := by
  refine ⟨fun hn => absurd (h.symm.trans hn) (by decide), fun _ _ => ?_, fun _ => ?_⟩
  · exact floorInk_accounts src
  · exact floorInk_mem src

/-- The same statement at the one loss class that owes ink, spelled out so
the registry's `degraded` codes have a named fact rather than an instance of
a quantified one: the math floor is an honest `degraded` recovery for every
source, including one whose content characters are none. -/
public theorem floorInk_degraded_covers (src : String) :
    FloorHonest Loss.degraded.floor .filtered src.toList (floorInk src) := by
  exact ⟨fun hn => absurd (Loss.degraded_floor_ships_exact.symm.trans hn) (by decide),
    fun _ _ => floorInk_accounts src,
    fun _ => floorInk_mem src⟩


/-- Typographic punctuation, applied to ordinary text. `--` and `---` are the
dashes an author means when they type them; `...` is an ellipsis. TeX's quote
ligatures come first (TeXbook ch. 2: ``` `` ``` and `''` are how quotation
marks are typed; Appendix F's Computer Modern ligature table adds the single
`` ` `` → ‘ and the Spanish pairs !+backtick → ¡, ?+backtick → ¿); a straight
double quote or lone apostrophe
becomes the directional pair, chosen by what precedes it (so an apostrophe in
"don't" closes). Literal text (mono, verbatim) is exempt — that is where a
straight quote or backtick is the point. -/
public def smartPunct (s : String) : String :=
  String.ofList (go s.toList [])
where
  /-- `prev` is the output so far, reversed: its head is the character just
  emitted, which is what decides quote direction. Two-character ligatures
  match before the single-character arms. -/
  go : List Char → List Char → List Char
    | [], prev => prev.reverse
    | '-' :: '-' :: '-' :: rest, prev => go rest ('—' :: prev)
    | '-' :: '-' :: rest, prev => go rest ('–' :: prev)
    | '.' :: '.' :: '.' :: rest, prev => go rest ('…' :: prev)
    | '`' :: '`' :: rest, prev => go rest ('“' :: prev)
    | '`' :: rest, prev => go rest ('‘' :: prev)
    | '\'' :: '\'' :: rest, prev => go rest ('”' :: prev)
    | '!' :: '`' :: rest, prev => go rest ('¡' :: prev)
    | '?' :: '`' :: rest, prev => go rest ('¿' :: prev)
    | '"' :: rest, prev =>
      let opening := match prev with
        | [] => true
        | c :: _ => c == ' ' || c == '(' || c == '[' || c == '—' || c == '–'
      go rest ((if opening then '“' else '”') :: prev)
    | '\'' :: rest, prev =>
      let opening := match prev with
        | [] => true
        | c :: _ => c == ' ' || c == '(' || c == '[' || c == '“'
      go rest ((if opening then '‘' else '’') :: prev)
    | c :: rest, prev => go rest (c :: prev)

-- Display-only printers. Structural recursion through `List`, so no `partial`.

mutual

/-- The characters of inline content with every mark stripped: what a URL or
a palette key built from a parameter is worth as text. -/
@[expose] public def plainText (xs : Array Inline) : String :=
  plainTextList xs.toList

@[expose] public def plainTextList (xs : List Inline) : String :=
  match xs with
  | [] => ""
  | x :: rest => plainTextOne x ++ plainTextList rest

@[expose] public def plainTextOne (x : Inline) : String :=
  match x with
  | .text s => s
  | .math _ src => mathFloor src
  | .formula _ _ body => formulaFloor body
  | .styled _ body => plainTextList body.toList
  | .colored _ _ body => plainTextList body.toList
  | .located _ body => plainTextList body.toList
  | .role _ body => plainTextList body.toList
  | .link _ body => plainTextList body.toList
  | .decorated _ body => plainTextList body.toList
  | .onSteps _ body => plainTextList body.toList
  | .altSteps _ firstPage otherPage =>
    plainTextList firstPage.toList ++ plainTextList otherPage.toList
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount => ""
  | .image _ _ _ => ""
  -- an icon is worth its text alternative: what the markdown twin renders
  | .icon _ label => label
  -- an anchor ships no ink; a reference is worth what it resolved to
  | .label _ => ""
  | .ref _ _ text _ => text
  -- a citation is worth the number it shows (or LaTeX's ? unresolved)
  | .cite _ keys => citeMarks keys
  -- the note body is document text; its mark digit is generated ink,
  -- excluded as a citation's mark is
  | .footnote _ body => plainTextList body.toList
  | .linebreak _ => " "

end

mutual

/-- The text the first page of an overlay sequence shows, onto `acc`:
`plainText`'s reading, except that an alternation contributes only the group
stored first — the one step 1 inks (`OverlaySpec.showsFirst_id`). Covered
content still reads, since it dims on the page and never hides. A name is
one page's reading: a frame's anchor and its accessible name read this,
while the census (`plainText`) carries both groups because both ship — read
as the census, `\textcolor<2>{c}{Word}` named its frame "WordWord".
Hand-rolled because the generic fold visits both groups. -/
-- conserves: none — one page's reading: an alternation's other group ships
-- on the other pages, and the census (`plainText`) counts it there.
public def firstPageTextOne (acc : String) (x : Inline) : String :=
  match x with
  | .altSteps _ firstPage _ => firstPageTextList acc firstPage.toList
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body
  | .link _ body | .decorated _ body | .onSteps _ body | .footnote _ body =>
    firstPageTextList acc body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .label _
  | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _
  | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
    String.append acc (plainTextOne x)

public def firstPageTextList (acc : String) : List Inline → String
  | [] => acc
  | x :: rest => firstPageTextList (firstPageTextOne acc x) rest

end

/-- The text the first page of an overlay sequence shows
(`firstPageTextOne`), from nothing. -/
public def firstPageText (xs : Array Inline) : String := firstPageTextList "" xs.toList

/-- The words a picture's labels set, in shape order, joined: what a sighted
reader reads in the drawing. The one reading a picture's name takes, whoever
draws it — the SVG's accessible name (`HtmlDoc.pictureName`), and the text
alternative of the image the boundary returns for it, so a picture routed
there keeps the name its own labels give it. -/
public def Pic.Picture.said (pic : Pic.Picture) : String :=
  String.intercalate ", " (pic.labelContents.toList.filterMap fun content =>
    let s := plainText content
    if s.toList.any (!·.isWhitespace) then some s.trimAscii.toString else none)

/-- The alternative a reader of either artifact gets for a picture, resolved
once: what the author declared, else the words its own labels set
(`said`) — latex-lab-tikz's default for a picture given no key hands a
reader exactly its text — else nothing said. Both backends read this one
value (`HtmlDoc.pictureRole`, `Struct`'s picture leaf). -/
public def Pic.Picture.alternative (pic : Pic.Picture) : Alt :=
  match pic.alt with
  | .undeclared => Alt.declare pic.said
  | .decorative => .decorative
  | .described t => .described t

/-- A declaration outranks the picture's words: the resolution changes only
what the author left undeclared. -/
public theorem Pic.Picture.alternative_fixed_point (pic : Pic.Picture) (h : pic.alt ≠ .undeclared) :
    pic.alternative = pic.alt := by
  unfold Pic.Picture.alternative
  cases hp : pic.alt with
  | undeclared => exact absurd hp h
  | decorative => rfl
  | described _ => rfl

/-- A role is a name around content, never content: the census reads
straight through it, so no annotation can add or hide a character. -/
public theorem role_plaintext (n : String) (body : Array Inline) :
    plainTextOne (.role n body) = plainTextList body.toList := by rfl

mutual

/-- One leaf-parameterised fold hosts every collect walk over the tree:
`fi` reads each inline node — applied to the node itself, never to
children, so the recursion below stays explicit and the checker sees it.
Document order, a node before its content. -/
@[expose] public def foldInline (fi : α → Inline → α) (acc : α) (x : Inline) : α :=
  match x with
  | .styled _ body => foldInlineList fi (fi acc x) body.toList
  | .colored _ _ body => foldInlineList fi (fi acc x) body.toList
  | .located _ body => foldInlineList fi (fi acc x) body.toList
  | .role _ body => foldInlineList fi (fi acc x) body.toList
  | .link _ body => foldInlineList fi (fi acc x) body.toList
  | .decorated _ body => foldInlineList fi (fi acc x) body.toList
  | .onSteps _ body => foldInlineList fi (fi acc x) body.toList
  | .altSteps _ firstPage otherPage =>
    foldInlineList fi (foldInlineList fi (fi acc x) firstPage.toList) otherPage.toList
  | .footnote _ body => foldInlineList fi (fi acc x) body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ => fi acc x

@[expose] public def foldInlineList (fi : α → Inline → α) (acc : α) : List Inline → α
  | [] => acc
  | x :: rest => foldInlineList fi (foldInline fi acc x) rest

end

/-- `foldInline` over an inline tree, the collectors' entry. -/
@[expose] public def foldInlines (fi : α → Inline → α) (acc : α) (xs : Array Inline) : α :=
  foldInlineList fi acc xs.toList

/-- The first contributing source location, in document order. Enclosing
declarations precede their content, so a delayed diagnostic retains the
declaration's origin even when its value was parsed separately. -/
-- conserves: none — reads provenance through the generic inline fold.
public def inlineSource (content : Array Inline) : Option Span :=
  foldInlines (fun source inline => match inline with
    | .located span _ => source.orElse (fun _ => some span)
    | .text _ | .math _ _ | .formula _ _ _ | .styled _ _
      | .colored _ _ _ | .role _ _ | .link _ _ | .label _
      | .ref _ _ _ _ | .decorated _ _ | .fill | .hspace _ _
      | .rule _ _ _ | .pageNumber | .pageCount | .linebreak _
      | .strut _ | .italicCorr _ | .onSteps _ _ | .altSteps _ _ _
      | .image _ _ _ | .icon _ _ | .cite _ _ | .footnote _ _ => source)
    none content

@[expose] public def foldTableCells (fi : α → Inline → α) (acc : α) : List (Array Inline) → α
  | [] => acc
  | cell :: rest => foldTableCells fi (foldInlineList fi acc cell.toList) rest

/-- `foldInline` over algorithm lines: each line's content, then its
comment, in reading order — one spelling for every collector, so no two
can disagree on what an algorithm declares. -/
@[expose] public def foldAlgLines (fi : α → Inline → α) (acc : α) : List AlgLine → α
  | [] => acc
  | l :: rest =>
    foldAlgLines fi (match l.comment with
      | some c => foldInlineList fi (foldInlineList fi acc l.content.toList) c.toList
      | none => foldInlineList fi acc l.content.toList) rest

@[expose] public def foldTableRows (fi : α → Inline → α) (acc : α) :
    List (Array (Array Inline)) → α
  | [] => acc
  | row :: rest => foldTableRows fi (foldTableCells fi acc row.toList) rest

mutual

/-- The block face of the fold: `fb` reads each block, `fi` each inline —
the node first, a frame's title and a float's caption before their bodies,
as the collectors this fold hosts always read them. A `.bibliography`'s
items are formatted renderings, not authored content, so the fold reads
the marker itself and does not descend into them. -/
@[expose] public def foldBlock (fb : α → Block → α) (fi : α → Inline → α) (acc : α) (b : Block) : α :=
  match b with
  | .para content => foldInlineList fi (fb acc b) content.toList
  -- the formula, then the number beside it: an author's tag is inline content
  | .equation number content =>
    foldInlineList fi (foldInlineList fi (fb acc b) content.toList) number.toList
  | .section _ _ _ title => foldInlineList fi (fb acc b) title.toList
  | .list _ items => foldBlockItems fb fi (fb acc b) items.toList
  | .center body => foldBlockList fb fi (fb acc b) body.toList
  | .ragged _ body => foldBlockList fb fi (fb acc b) body.toList
  | .quote body => foldBlockList fb fi (fb acc b) body.toList
  | .abstract body => foldBlockList fb fi (fb acc b) body.toList
  | .titled _ title body =>
    foldBlockList fb fi (foldInlineList fi (fb acc b) title.toList) body.toList
  | .role _ body => foldBlockList fb fi (fb acc b) body.toList
  | .link _ body => foldBlockList fb fi (fb acc b) body.toList
  | .spaced _ body => foldBlockList fb fi (fb acc b) body.toList
  | .columns cols => foldBlockCols fb fi (fb acc b) cols.toList
  | .onSteps _ body => foldBlockList fb fi (fb acc b) body.toList
  | .altSteps _ firstPage otherPage =>
    foldBlockList fb fi (foldBlockList fb fi (fb acc b) firstPage.toList) otherPage.toList
  | .only _ body => foldBlockList fb fi (fb acc b) body.toList
  | .nav _ body => foldBlockList fb fi (fb acc b) body.toList
  | .note body => foldBlockList fb fi (fb acc b) body.toList
  | .frame title _ _ _ body =>
    foldBlockList fb fi (foldInlineList fi (fb acc b) title.toList) body.toList
  | .framefoot content => foldInlineList fi (fb acc b) content.toList
  | .float _ _ _ body caption =>
    foldBlockList fb fi (foldInlineList fi (fb acc b) caption.toList) body.toList
  | .table _ _ _ rows _ _ => foldTableRows fi (fb acc b) rows.toList
  | .algorithm _ _ lines => foldAlgLines fi (fb acc b) lines.toList
  | .logo content => foldInlineList fi (fb acc b) content.toList
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .bibliography _ _ _ => fb acc b

@[expose] public def foldBlockList (fb : α → Block → α) (fi : α → Inline → α) (acc : α) :
    List Block → α
  | [] => acc
  | b :: rest => foldBlockList fb fi (foldBlock fb fi acc b) rest

@[expose] public def foldBlockItems (fb : α → Block → α) (fi : α → Inline → α) (acc : α) :
    List (Array Block) → α
  | [] => acc
  | item :: rest => foldBlockItems fb fi (foldBlockList fb fi acc item.toList) rest

@[expose] public def foldBlockCols (fb : α → Block → α) (fi : α → Inline → α) (acc : α) :
    List (BoxWidth × Array Block) → α
  | [] => acc
  | (_, body) :: rest => foldBlockCols fb fi (foldBlockList fb fi acc body.toList) rest

end

/-- `foldBlock` over a block tree: `bibRefs`, `bibStyleName`, and
`BibStyle.citedKeys` are leaf projections of this one traversal. -/
@[expose] public def foldBlocks (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (xs : Array Block) : α :=
  foldBlockList fb fi acc xs.toList

/-- The events a context-threading walk declares. `foldBlock`'s pair of
leaf functions is the case where no context descends and the way out is
silent — `foldCtxBlock_covers` is that equality, and it is what makes a
conversion to this walk a no-op on the artifact. Two things a leaf fold
cannot express live here: a value bound over a node's *extent*, read from
`γ` (the float binding a `\label` under a captioned float resolves
against), and the *end* of a container, which a tree built from the IR
needs and an accumulator reading a node before its content can never
find. The context descends and does not escape — siblings are read under
the context their parent opened them in, and `closeBlock` sees that same
context, so a node's own binding cannot leak past where it stands. -/
public structure CtxFold (γ : Type) (α : Type) where
  /-- Entering a block: the accumulator, and the context its content is
  read under. -/
  openBlock : γ → α → Block → α × γ
  /-- Leaving a block, under the context the block was entered in. -/
  closeBlock : γ → α → Block → α
  /-- Entering an inline node: the accumulator, and the context its
  content is read under. -/
  openInline : γ → α → Inline → α × γ
  /-- Leaving an inline node, under the context it was entered in. -/
  closeInline : γ → α → Inline → α

mutual

/-- `foldInline`'s descent with a context and a close event: document
order, a node before its content, the context `openInline` returns in
force over that content alone. Structural mutual recursion through `List`,
the same knot `foldInline` ties — no measure, and total by construction. -/
public def foldCtxInline (w : CtxFold γ α) (ctx : γ) (acc : α) (x : Inline) : α :=
  match x with
  | .styled _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .colored _ _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .located _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .role _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .link _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .decorated _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .onSteps _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .altSteps _ firstPage otherPage =>
    let r := w.openInline ctx acc x
    w.closeInline ctx
      (foldCtxInlineList w r.2 (foldCtxInlineList w r.2 r.1 firstPage.toList)
        otherPage.toList) x
  | .footnote _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
    w.closeInline ctx (w.openInline ctx acc x).1 x

public def foldCtxInlineList (w : CtxFold γ α) (ctx : γ) (acc : α) : List Inline → α
  | [] => acc
  | x :: rest => foldCtxInlineList w ctx (foldCtxInline w ctx acc x) rest

end

/-- `foldCtxInline` over an inline tree, the walk's inline entry. -/
public def foldCtxInlines (w : CtxFold γ α) (ctx : γ) (acc : α) (xs : Array Inline) : α :=
  foldCtxInlineList w ctx acc xs.toList

public def foldCtxTableCells (w : CtxFold γ α) (ctx : γ) (acc : α) : List (Array Inline) → α
  | [] => acc
  | cell :: rest => foldCtxTableCells w ctx (foldCtxInlineList w ctx acc cell.toList) rest

public def foldCtxTableRows (w : CtxFold γ α) (ctx : γ) (acc : α) :
    List (Array (Array Inline)) → α
  | [] => acc
  | row :: rest => foldCtxTableRows w ctx (foldCtxTableCells w ctx acc row.toList) rest

/-- `foldCtxInline` over algorithm lines: content then comment, the reading
order `foldAlgLines` declares once for every collector. -/
public def foldCtxAlgLines (w : CtxFold γ α) (ctx : γ) (acc : α) : List AlgLine → α
  | [] => acc
  | l :: rest =>
    foldCtxAlgLines w ctx (match l.comment with
      | some c => foldCtxInlineList w ctx (foldCtxInlineList w ctx acc l.content.toList) c.toList
      | none => foldCtxInlineList w ctx acc l.content.toList) rest

mutual

/-- The block face: `foldBlock`'s descent, arm for arm, with the context
`openBlock` returns in force over the node's content and `closeBlock`
called once that content is read. A `.bibliography`'s items are the style's
renderings, not authored content, so the walk reads the marker and does not
descend — the same line `foldBlock` draws. -/
@[expose] public def foldCtxBlock (w : CtxFold γ α) (ctx : γ) (acc : α) (b : Block) : α :=
  match b with
  | .para content =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxInlineList w r.2 r.1 content.toList) b
  | .equation number content =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx
      (foldCtxInlineList w r.2 (foldCtxInlineList w r.2 r.1 content.toList) number.toList) b
  | .section _ _ _ title =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxInlineList w r.2 r.1 title.toList) b
  | .list _ items =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockItems w r.2 r.1 items.toList) b
  | .center body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .ragged _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .quote body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .abstract body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .titled _ title body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx
      (foldCtxBlockList w r.2 (foldCtxInlineList w r.2 r.1 title.toList) body.toList) b
  | .role _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .link _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .spaced _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .columns cols =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockCols w r.2 r.1 cols.toList) b
  | .onSteps _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .altSteps _ firstPage otherPage =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx
      (foldCtxBlockList w r.2 (foldCtxBlockList w r.2 r.1 firstPage.toList)
        otherPage.toList) b
  | .only _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .nav _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .note body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .frame title _ _ _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx
      (foldCtxBlockList w r.2 (foldCtxInlineList w r.2 r.1 title.toList) body.toList) b
  | .framefoot content =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxInlineList w r.2 r.1 content.toList) b
  | .float _ _ _ body caption =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx
      (foldCtxBlockList w r.2 (foldCtxInlineList w r.2 r.1 caption.toList) body.toList) b
  | .table _ _ _ rows _ _ =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxTableRows w r.2 r.1 rows.toList) b
  | .algorithm _ _ lines =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxAlgLines w r.2 r.1 lines.toList) b
  | .logo content =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxInlineList w r.2 r.1 content.toList) b
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .bibliography _ _ _ =>
    w.closeBlock ctx (w.openBlock ctx acc b).1 b

public def foldCtxBlockList (w : CtxFold γ α) (ctx : γ) (acc : α) : List Block → α
  | [] => acc
  | b :: rest => foldCtxBlockList w ctx (foldCtxBlock w ctx acc b) rest

public def foldCtxBlockItems (w : CtxFold γ α) (ctx : γ) (acc : α) : List (Array Block) → α
  | [] => acc
  | item :: rest => foldCtxBlockItems w ctx (foldCtxBlockList w ctx acc item.toList) rest

public def foldCtxBlockCols (w : CtxFold γ α) (ctx : γ) (acc : α) :
    List (BoxWidth × Array Block) → α
  | [] => acc
  | (_, body) :: rest => foldCtxBlockCols w ctx (foldCtxBlockList w ctx acc body.toList) rest

end

/-- `foldCtxBlock` over a block tree, the walk's entry. -/
public def foldCtxBlocks (w : CtxFold γ α) (ctx : γ) (acc : α) (xs : Array Block) : α :=
  foldCtxBlockList w ctx acc xs.toList

/-- The leaf fold as a context walk: nothing descends, nothing happens on
the way out. -/
public def CtxFold.ofFold (fb : α → Block → α) (fi : α → Inline → α) : CtxFold Unit α where
  openBlock := fun _ acc b => (fb acc b, ())
  closeBlock := fun _ acc _ => acc
  openInline := fun _ acc x => (fi acc x, ())
  closeInline := fun _ acc _ => acc

@[simp] public theorem CtxFold.ofFold_openBlock (fb : α → Block → α) (fi : α → Inline → α)
    (u : Unit) (acc : α) (b : Block) :
    (CtxFold.ofFold fb fi).openBlock u acc b = (fb acc b, ()) := by rfl

@[simp] public theorem CtxFold.ofFold_closeBlock (fb : α → Block → α) (fi : α → Inline → α)
    (u : Unit) (acc : α) (b : Block) : (CtxFold.ofFold fb fi).closeBlock u acc b = acc := by rfl

@[simp] public theorem CtxFold.ofFold_openInline (fb : α → Block → α) (fi : α → Inline → α)
    (u : Unit) (acc : α) (x : Inline) :
    (CtxFold.ofFold fb fi).openInline u acc x = (fi acc x, ()) := by rfl

@[simp] public theorem CtxFold.ofFold_closeInline (fb : α → Block → α) (fi : α → Inline → α)
    (u : Unit) (acc : α) (x : Inline) :
    (CtxFold.ofFold fb fi).closeInline u acc x = acc := by rfl

mutual

public theorem foldCtxInline_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (x : Inline) : foldCtxInline (CtxFold.ofFold fb fi) () acc x = foldInline fi acc x := by
  match x with
  | .styled _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .colored _ _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .located _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .role _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .link _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .decorated kind body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .onSteps _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .altSteps _ firstPage otherPage =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    rw [foldCtxInlineList_covers fb fi _ firstPage.toList,
      foldCtxInlineList_covers fb fi _ otherPage.toList]
  | .footnote _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]

public theorem foldCtxInlineList_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (xs : List Inline) :
    foldCtxInlineList (CtxFold.ofFold fb fi) () acc xs = foldInlineList fi acc xs := by
  match xs with
  | [] => rfl
  | x :: rest =>
    rw [foldCtxInlineList, foldInlineList, foldCtxInline_covers,
      foldCtxInlineList_covers fb fi _ rest]

end

public theorem foldCtxTableCells_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (cells : List (Array Inline)) :
    foldCtxTableCells (CtxFold.ofFold fb fi) () acc cells = foldTableCells fi acc cells := by
  induction cells generalizing acc with
  | nil => rfl
  | cons cell rest ih =>
    rw [foldCtxTableCells, foldTableCells, foldCtxInlineList_covers, ih]

public theorem foldCtxTableRows_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (rows : List (Array (Array Inline))) :
    foldCtxTableRows (CtxFold.ofFold fb fi) () acc rows = foldTableRows fi acc rows := by
  induction rows generalizing acc with
  | nil => rfl
  | cons row rest ih =>
    rw [foldCtxTableRows, foldTableRows, foldCtxTableCells_covers, ih]

public theorem foldCtxAlgLines_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (lines : List AlgLine) :
    foldCtxAlgLines (CtxFold.ofFold fb fi) () acc lines = foldAlgLines fi acc lines := by
  induction lines generalizing acc with
  | nil => rfl
  | cons l rest ih =>
    rw [foldCtxAlgLines, foldAlgLines]
    cases l.comment with
    | none => simp only [foldCtxInlineList_covers, ih]
    | some c => simp only [foldCtxInlineList_covers, ih]

mutual

/-- **The context walk covers the leaf fold** (`_covers`): with no context
descending and a silent way out, `foldCtxBlock` reads exactly the nodes
`foldBlock` reads, in exactly its order. The descent is declared twice in
this file, so this is the statement that keeps the two copies one walk —
the next `Ir` constructor descended in one and not the other fails here,
and a caller moved from `foldBlocks` to `foldCtxBlocks` is provably a
no-op. -/
public theorem foldCtxBlock_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (b : Block) : foldCtxBlock (CtxFold.ofFold fb fi) () acc b = foldBlock fb fi acc b := by
  match b with
  | .para content =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxInlineList_covers fb fi _ content.toList
  | .equation number content =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    rw [foldCtxInlineList_covers fb fi _ content.toList,
      foldCtxInlineList_covers fb fi _ number.toList]
  | .section _ _ _ title =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxInlineList_covers fb fi _ title.toList
  | .list _ items =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockItems_covers fb fi _ items.toList
  | .center body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .ragged _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .quote body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .abstract body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .titled _ title body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    rw [foldCtxInlineList_covers fb fi _ title.toList,
      foldCtxBlockList_covers fb fi _ body.toList]
  | .role _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .link _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .spaced _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .columns cols =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockCols_covers fb fi _ cols.toList
  | .onSteps _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .altSteps _ firstPage otherPage =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    rw [foldCtxBlockList_covers fb fi _ firstPage.toList,
      foldCtxBlockList_covers fb fi _ otherPage.toList]
  | .only _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .nav _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .note body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .frame title _ _ _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    rw [foldCtxInlineList_covers fb fi _ title.toList,
      foldCtxBlockList_covers fb fi _ body.toList]
  | .framefoot content =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxInlineList_covers fb fi _ content.toList
  | .float _ _ _ body caption =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    rw [foldCtxInlineList_covers fb fi _ caption.toList,
      foldCtxBlockList_covers fb fi _ body.toList]
  | .table _ _ _ rows _ _ =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxTableRows_covers fb fi _ rows.toList
  | .algorithm _ _ lines =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxAlgLines_covers fb fi _ lines.toList
  | .logo content =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxInlineList_covers fb fi _ content.toList
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .bibliography _ _ _ =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]

public theorem foldCtxBlockList_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (bs : List Block) :
    foldCtxBlockList (CtxFold.ofFold fb fi) () acc bs = foldBlockList fb fi acc bs := by
  match bs with
  | [] => rfl
  | b :: rest =>
    rw [foldCtxBlockList, foldBlockList, foldCtxBlock_covers,
      foldCtxBlockList_covers fb fi _ rest]

public theorem foldCtxBlockItems_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (items : List (Array Block)) :
    foldCtxBlockItems (CtxFold.ofFold fb fi) () acc items = foldBlockItems fb fi acc items := by
  match items with
  | [] => rfl
  | item :: rest =>
    rw [foldCtxBlockItems, foldBlockItems, foldCtxBlockList_covers,
      foldCtxBlockItems_covers fb fi _ rest]

public theorem foldCtxBlockCols_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (cols : List (BoxWidth × Array Block)) :
    foldCtxBlockCols (CtxFold.ofFold fb fi) () acc cols = foldBlockCols fb fi acc cols := by
  match cols with
  | [] => rfl
  | (_, body) :: rest =>
    rw [foldCtxBlockCols, foldBlockCols, foldCtxBlockList_covers,
      foldCtxBlockCols_covers fb fi _ rest]

end

/-- The tree face of `foldCtxBlock_covers`: `foldCtxBlocks` with no context
is `foldBlocks`. -/
public theorem foldCtxBlocks_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (xs : Array Block) :
    foldCtxBlocks (CtxFold.ofFold fb fi) () acc xs = foldBlocks fb fi acc xs :=
  foldCtxBlockList_covers fb fi acc xs.toList

/-- Does any node of the inline content satisfy `p`? The Bool face of the
fold — the trigger census the conditional-identity schema
(`mapInlines_id`) and `hasPhysicalPage` read. -/
@[expose] public def anyInline (p : Inline → Bool) (xs : Array Inline) : Bool :=
  foldInlines (fun b x => b || p x) false xs

/-- An inline that emits an HTML anchor now or after reference/citation
resolution. Conservatively counting citations keeps a later rewrite from
creating an anchor inside an already-built block link. -/
public def Inline.anchorBearing : Inline → Bool
  | .link _ _ | .ref _ _ _ _ | .cite _ _ | .footnote _ _ => true
  | .text _ | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _
  | .located _ _ | .role _ _ | .decorated _ _ | .fill | .hspace _ _ | .rule _ _ _
  | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ | .onSteps _ _ | .altSteps _ _ _
  | .image _ _ _ | .icon _ _ | .label _ => false

/-- Whether a block body already contains an anchor-bearing construct. -/
public def hasBlockAnchor (xs : Array Block) : Bool :=
  foldBlocks (fun found b => found || (b matches .link _ _))
    (fun found x => found || x.anchorBearing) false xs

/-- Whether an inline leaf bears text ink a link affordance should mark. A
link's underline and ink ride text; an image, an anchor, pure spacing or a
strut carry none, so they take no affordance — which is what leaves an
image-only link body with no invisible underline (its reachable, named
anchor is the affordance instead). The wrapper nodes are descended by the
afford walk and never classified here. -/
public def Inline.bearsLinkText : Inline → Bool
  | .text _ | .math _ _ | .formula _ _ _ | .ref _ _ _ _ | .cite _ _
  | .icon _ _ | .pageNumber | .pageCount => true
  | .image _ _ _ | .label _ | .fill | .hspace _ _ | .rule _ _ _
  | .strut _ | .italicCorr _ | .linebreak _
  | .styled _ _ | .colored _ _ _ | .located _ _ | .role _ _ | .link _ _ | .decorated _ _
  | .onSteps _ _ | .altSteps _ _ _ | .footnote _ _ => false

/-- One link-body leaf given its kind's affordance: a text-bearing leaf is
underlined (`Decoration.underline`) and, where the kind declares one, set in
its ink (`Styles.linkInk`'s colour) — the two affordances an inline link
already carries (`Layout`'s `.link` arm, WCAG 2.2 SC 1.4.1); a leaf that
bears no text is left as it stands, so an image-only body carries no
invisible-only decoration. A leaf rewrite, so the afford walk applies it
exactly once per leaf. -/
public def Styles.linkLeafAfford (s : Styles) (kind : String) (x : Inline) : Inline :=
  if x.bearsLinkText then
    match (s.find? kind).bind (·.color) with
    | some (c, n) => .colored c n #[.decorated .underline #[x]]
    | none => .decorated .underline #[x]
  else x

/-- A text-bearing link-body leaf takes both affordances: it is underlined,
and set in the kind's ink where one is declared. The IR half of the inline
link's own `.link` + `linkInk` behaviour, now readable by both backends from
one body. -/
public theorem Styles.linkLeafAfford_afford (s : Styles) (kind : String) (x : Inline)
    (h : x.bearsLinkText = true) :
    s.linkLeafAfford kind x
      = (match (s.find? kind).bind (·.color) with
         | some (c, n) => .colored c n #[.decorated .underline #[x]]
         | none => .decorated .underline #[x]) := by
  simp only [Styles.linkLeafAfford, h, ite_true]
  rfl

/-- A leaf that bears no text is untouched by the affordance: an image, an
anchor or pure spacing takes no decoration, so an image-only link body
carries no invisible-only wrap — its affordance is the named anchor. -/
public theorem Styles.linkLeafAfford_id (s : Styles) (kind : String) (x : Inline)
    (h : x.bearsLinkText = false) : s.linkLeafAfford kind x = x := by
  simp [Styles.linkLeafAfford, h]

/-- The affordance conserves a leaf's census: underline and ink are both
body-transparent wraps, so an afforded leaf ships exactly the text it had —
the per-leaf hypothesis the body walk's `_text` instance reads. -/
public theorem Styles.linkLeafAfford_text (s : Styles) (kind : String) (x : Inline) :
    plainTextOne (s.linkLeafAfford kind x) = plainTextOne x := by
  rw [Styles.linkLeafAfford]
  split
  · split <;> simp [plainTextOne, plainTextList]
  · rfl


/-- The accessible reading of a block link, from the same generic fold that
censuses the block tree. Wrapper nodes contribute nothing twice; leaf text,
listing text, reference entries, and non-text alternatives do. -/
private def blockLinkInlineReading (acc : String) (x : Inline) : String :=
  match x with
  | .styled _ _ | .colored _ _ _ | .located _ _ | .role _ _ | .link _ _ | .decorated _ _
  | .onSteps _ _ | .altSteps _ _ _ | .footnote _ _ => acc
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _
  | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ => String.append acc (plainTextOne x)

private def blockLinkBlockReading (acc : String) (b : Block) : String :=
  match b with
  | .verbatim _ content spec =>
    let caption := match spec.caption with
      | some (_, cap) => plainText cap
      | none => ""
    String.append (String.append acc caption) content
  | .picture pic => String.append acc pic.alternative.text
  | .bibliography _ _ items =>
    items.foldl (fun s item => String.append s (plainText item.content)) acc
  | .para _ | .section _ _ _ _ | .list _ _ | .center _ | .ragged _ _ | .spaced _ _
  | .role _ _ | .link _ _ | .quote _ | .abstract _ | .titled _ _ _ | .equation _ _
  | .algorithm _ _ _ | .columns _ | .onSteps _ _ | .altSteps _ _ _ | .note _ | .only _ _
  | .nav _ _ | .logo _ | .pagebreak | .frame _ _ _ _ _ | .framefoot _ | .setPalette _
  | .setTokens _ | .rule _ _ _ | .table _ _ _ _ _ _ | .float _ _ _ _ _ => acc

/-- What assistive technology can name a block link from. -/
public def blockLinkReading (body : Array Block) : String :=
  foldBlocks blockLinkBlockReading blockLinkInlineReading "" body


/-- Unicode `White_Space` (PropList.txt, maintained under UAX #44): the
closed set 0009–000D, 0020, 0085, 00A0, 1680, 2000–200A, 2028, 2029, 202F,
205F, 3000. HTML forbids only ASCII whitespace in an id (§3.2.6), a subset
of this set; treating every White_Space character as a separator also keeps
the thin spaces the engine itself emits for `\,`/`\:`/`\;` out of anchors. -/
public def isWhiteSpaceUni (c : Char) : Bool :=
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
private def slugCharKeep (k : Char) : Option Char :=
  if isWhiteSpaceUni k then none
  else if k.isAlpha || k.isDigit then some k
  else if 0x80 ≤ k.toNat then some k
  else none

private def slugChar (c : Char) : Option Char :=
  slugCharKeep (if c.isAlpha || c.isDigit then c.toLower else c)

/-- The slug walk: separators collapse to one hyphen, emitted only between
kept characters, so no leading or trailing hyphen can exist by construction. -/
private def slugGo (acc : Array Char) (sep : Bool) : List Char → Array Char
  | [] => acc
  | c :: rest =>
    match slugChar c with
    | some k =>
      if sep && !acc.isEmpty then slugGo ((acc.push '-').push k) false rest
      else slugGo (acc.push k) false rest
    | none => slugGo acc true rest

/-- An anchor id from a title's own text. Every static site generator derives
ids this way, so an in-page `\href{#experience}` has a target by construction
rather than by a label the author must remember to declare. The text is the
title as its first page shows it (`firstPageText`): an overlay alternation
names its title once, by the group step 1 inks — the census reading spelled
both groups into one anchor. Non-emptiness — the other half of HTML §3.2.6's
requirement — is `sectionize`'s job: an all-separator title takes the id
`section`. Not done, stated rather than hidden: Unicode normalisation (UAX
#15 NFC) — a composed and a decomposed `é` make two different anchors; PLAN
carries the debt. -/
public def slug (title : Array Inline) : String :=
  String.ofList (slugGo #[] false (firstPageText title).toList).toList

private theorem slugCharKeep_not_whitespace (k k' : Char) (h : slugCharKeep k = some k') :
    isWhiteSpaceUni k' = false := by
  unfold slugCharKeep at h
  (repeat' split at h) <;> simp_all

private theorem slugChar_not_whitespace (c k : Char) (h : slugChar c = some k) :
    isWhiteSpaceUni k = false :=
  slugCharKeep_not_whitespace _ _ h

private theorem slugGo_no_whitespace (l : List Char) (acc : Array Char) (sep : Bool)
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
public theorem slug_no_whitespace (title : Array Inline) :
    ∀ c ∈ (slug title).toList, isWhiteSpaceUni c = false := by
  intro c hc
  simp only [slug, String.toList_ofList] at hc
  exact slugGo_no_whitespace _ _ _ (by simp) c hc

/-- **An alternating title anchors by the group its first page shows**
(`_exact`): a title that is one overlay alternation takes the anchor of its
first-page group alone, never of both groups — read as the census, a
`\textcolor<2>{c}{Word}` title anchored its frame `wordword`. -/
public theorem slug_altSteps_exact (spec : OverlaySpec) (firstPage otherPage : Array Inline) :
    slug #[.altSteps spec firstPage otherPage] = slug firstPage := by
  simp [slug, firstPageText, firstPageTextList, firstPageTextOne]

-- Navigation links: what a paged surface renders an unpinned nav as — the
-- document outline. Structural recursion through `List`, as the walks above.

mutual

/-- Every link of a navigation landmark's body, in document order, as
(text, target). -/
-- conserves: none — a projection of the links alone: a nav is furniture on
-- the paged surface, and only its links are navigation; what its body must
-- NOT ship there is pinned by the webnav census and the nav layout tests.
private def navLinkList (out : Array (String × String)) : List Block → Array (String × String)
  | [] => out
  | b :: rest => navLinkList (navLinkOne out b) rest

private def navLinkOne (out : Array (String × String)) : Block → Array (String × String)
  | .para content => navLinkInlineList out content.toList
  | .equation number content =>
    navLinkInlineList (navLinkInlineList out content.toList) number.toList
  | .section _ _ _ title => navLinkInlineList out title.toList
  | .verbatim _ _ _ => out
  | .logo _ => out
  | .framefoot _ => out
  | .setPalette _ => out
  | .setTokens _ => out
  | .pagebreak => out
  | .rule _ _ _ => out
  | .picture _ => out
  | .list _ items => navLinkItems out items.toList
  | .center body => navLinkList out body.toList
  | .ragged _ body => navLinkList out body.toList
  | .quote body => navLinkList out body.toList
  | .abstract body => navLinkList out body.toList
  | .titled _ title body => navLinkList (navLinkInlineList out title.toList) body.toList
  | .role _ body => navLinkList out body.toList
  | .link target body => out.push (blockLinkReading body, target)
  | .spaced _ body => navLinkList out body.toList
  | .columns cols => navLinkColumns out cols.toList
  | .onSteps _ body => navLinkList out body.toList
  | .altSteps _ firstPage otherPage =>
    navLinkList (navLinkList out firstPage.toList) otherPage.toList
  -- a speaker note is a side channel in every backend; never navigation
  | .note _ => out
  | .only _ body => navLinkList out body.toList
  | .nav _ body => navLinkList out body.toList
  | .frame title _ _ _ body => navLinkList (navLinkInlineList out title.toList) body.toList
  | .table _ _ _ rows _ _ => navLinkRows out rows.toList
  | .float _ _ _ body caption => navLinkInlineList (navLinkList out body.toList) caption.toList
  | .algorithm _ _ lines => navLinkAlgLines out lines.toList
  -- a resolved entry's content carries its URL and anchor links
  | .bibliography _ _ items => navLinkBibItems out items.toList

private def navLinkBibItems (out : Array (String × String)) :
    List BibItem → Array (String × String)
  | [] => out
  | item :: rest => navLinkBibItems (navLinkInlineList out item.content.toList) rest

private def navLinkRows (out : Array (String × String)) :
    List (Array (Array Inline)) → Array (String × String)
  | [] => out
  | row :: rest => navLinkRows (navLinkCells out row.toList) rest

private def navLinkCells (out : Array (String × String)) :
    List (Array Inline) → Array (String × String)
  | [] => out
  | cell :: rest => navLinkCells (navLinkInlineList out cell.toList) rest

private def navLinkItems (out : Array (String × String)) :
    List (Array Block) → Array (String × String)
  | [] => out
  | item :: rest => navLinkItems (navLinkList out item.toList) rest

private def navLinkColumns (out : Array (String × String)) :
    List (BoxWidth × Array Block) → Array (String × String)
  | [] => out
  | (_, body) :: rest => navLinkColumns (navLinkList out body.toList) rest

private def navLinkAlgLines (out : Array (String × String)) :
    List AlgLine → Array (String × String)
  | [] => out
  | l :: rest =>
    navLinkAlgLines (match l.comment with
      | some c => navLinkInlineList (navLinkInlineList out l.content.toList) c.toList
      | none => navLinkInlineList out l.content.toList) rest

private def navLinkInlineList (out : Array (String × String)) :
    List Inline → Array (String × String)
  | [] => out
  | x :: rest => navLinkInlineList (navLinkInline out x) rest

private def navLinkInline (out : Array (String × String)) : Inline → Array (String × String)
  -- the link whole: its text is the entry's title (a link cannot nest)
  | .link url body => out.push (plainTextList body.toList, url)
  | .styled _ body => navLinkInlineList out body.toList
  | .colored _ _ body => navLinkInlineList out body.toList
  | .located _ body => navLinkInlineList out body.toList
  | .role _ body => navLinkInlineList out body.toList
  | .decorated _ body => navLinkInlineList out body.toList
  | .onSteps _ body => navLinkInlineList out body.toList
  | .altSteps _ firstPage otherPage =>
    navLinkInlineList (navLinkInlineList out firstPage.toList) otherPage.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  -- a footnote's links are the note's own, never navigation entries
  | .footnote _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ => out

end

public def navLinks (body : Array Block) : Array (String × String) :=
  navLinkList #[] body.toList

/-- A step's range as the surface spells it: `step 2`, `step 2-3`, and
`step 2-2` for `<2->`, `<2-3>`, and `<2>`. -/
private def dumpStepRange (n : Nat) (last : Option Nat) : String :=
  match last with
  | some u => s!"step {n}-{u}"
  | none => s!"step {n}"

/-- An alternation's range, spelled as a step's is. -/
private def dumpAltRange (n : Nat) (last : Option Nat) : String :=
  match last with
  | some u => s!"alt {n}-{u}"
  | none => s!"alt {n}"

/-- Preserve the existing singleton dump; a union retains every declared
interval rather than printing their enclosing range. -/
private def dumpOverlayRange (kind : String) (spec : OverlaySpec) : String :=
  kind ++ " " ++ String.intercalate "," (spec.ranges.map fun (n, last) =>
    match last with
    | some u => s!"{n}-{u}"
    | none => toString n)

mutual

/-- One line of a formula's structure, for the IR dump: every atom's class,
scalar, and scripts, so a golden pins exactly what elaboration decided.
`ord:𝑥^{ord:2} bin:+ ord:𝑦` reads as it sets. The accumulator threads
through the walk, as every structural printer here does. -/
private def dumpMathItem (acc : String) (x : Math.MItem) : String :=
  match x with
  | .atom cls nuc sup sub lim =>
    let acc := acc ++ s!"{cls.label}:" ++ (if lim then "lim:" else "")
    dumpMathSub (dumpMathSup (dumpMathNucleus acc nuc) sup) sub
  | .space mu => acc ++ s!"mu:{mu}"
  | .ink c n => acc ++ s!"ink:#{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}"
      ++ (match n with | some n => s!"({n})" | none => "")

private def dumpMathNucleus (acc : String) (n : Math.MNucleus) : String :=
  match n with
  | .sym c => acc.push c
  | .styled sty c => ((acc ++ s!"styled:{sty.mathvariant}\{").push c).push '}'
  | .word s => acc ++ s.quote
  | .list body => (dumpMathList (acc.push '{') body).push '}'
  | .alpha a _ body => (dumpMathList (acc ++ s!"alpha:{a.name}\{") body).push '}'
  | .frac spec num den =>
    -- A generalized fraction shows what its spec declares beyond `\frac`'s:
    -- the delimiters, the rule in sp, and the style's rank (3 display).
    let name (c : Option Char) : String := match c with
      | some c => String.ofList [c]
      | none => "."
    let head := if spec == {} then "frac{" else
      s!"frac[{name spec.left}{name spec.right}" ++
        (match spec.rule with | some t => s!" rule:{t}" | none => "") ++
        (match spec.style with | some s => s!" style:{s.rank}" | none => "") ++ "]{"
    ((dumpMathList (acc ++ head) num ++ "}{" |> fun a =>
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
  | .big d step =>
    acc ++ s!"big{step}:" ++ (match d with | some c => String.ofList [c] | none => ".")
  | .accent mark stretch body =>
    -- The combining mark by scalar value: pushed bare it would combine
    -- with the golden's own text.
    let tag := if stretch then "acc*" else "acc"
    (dumpMathList (acc ++ s!"{tag}:{mark.toNat}\{") body).push '}'
  | .grid kind rows =>
    let tag := match kind with
      | .align => "align"
      | .gather => "gather"
      | .array cols s =>
        "array:" ++ String.join (cols.toList.map fun a => match a with
          | .left => "l"
          | .center => "c"
          | .right => "r") ++ (if s == 1000 then "" else s!"*{s}")
      | .small => "small"
    dumpMathRows (acc ++ tag ++ "[") rows ++ "]"
  | .cancel mark spec value body =>
    -- The mark, then what the spec declares beyond the defaults, then the
    -- struck subformula and the value it cancels to.
    let tag := match mark with
      | .up => "cancel"
      | .down => "bcancel"
      | .cross => "xcancel"
      | .to => "cancelto"
    let size := match spec.size with
      | .same => " samesize"
      | .step => ""
      | .sup => " Smaller"
    let opts := (if spec.thick then " thick" else "") ++ (if spec.room then "" else " overlap")
      ++ size ++ (match spec.color with
        | some (c, _) => s!" #{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}"
        | none => "")
    let acc := (dumpMathList (acc ++ tag ++ (if opts.isEmpty then "" else s!"[{(opts.drop 1).toString}]") ++ "{")
      body).push '}'
    match value with
    | .nil => acc
    | _ => (dumpMathList (acc ++ "to{") value).push '}'

private def dumpMathRows (acc : String) (rs : Math.MRows) : String :=
  match rs with
  | .nil => acc
  | .cons r rest =>
    dumpMathRows (dumpMathRow (acc ++ "(") r ++ ")") rest

private def dumpMathRow (acc : String) (r : Math.MRow) : String :=
  match r with
  | .nil => acc
  | .cons cell rest =>
    dumpMathRow (dumpMathList (acc ++ "|") cell) rest

private def dumpMathSup (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => (dumpMathRest (dumpMathItem (acc ++ "^{") x) rest).push '}'

private def dumpMathSub (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => (dumpMathRest (dumpMathItem (acc ++ "_{") x) rest).push '}'

private def dumpMathList (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => dumpMathRest (dumpMathItem acc x) rest

private def dumpMathRest (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => dumpMathRest (dumpMathItem (acc ++ " ") x) rest

end

mutual

private def dumpInlines (ind : String) (xs : Array Inline) : String :=
  dumpInlineList ind xs.toList

private def dumpInlineList (ind : String) (xs : List Inline) : String :=
  match xs with
  | [] => ""
  | x :: rest => dumpInline ind x ++ dumpInlineList ind rest

private def dumpInline (ind : String) (x : Inline) : String :=
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
      | some n => s!"{n} #{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}"
      | none => s!"#{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}"
    s!"{ind}color {tag}\n" ++ dumpInlines (ind ++ "  ") body
  | .located _ body => dumpInlines ind body
  | .role n body =>
    s!"{ind}role {n}\n" ++ dumpInlines (ind ++ "  ") body
  | .link url body =>
    s!"{ind}link {url.quote}\n" ++ dumpInlines (ind ++ "  ") body
  | .decorated kind body =>
    let label := match kind with
      | .underline => "underline"
      | .lineThrough => "line-through"
    s!"{ind}decoration {label}\n" ++ dumpInlines (ind ++ "  ") body
  | .onSteps spec body =>
    s!"{ind}{dumpOverlayRange "step" spec}\n" ++ dumpInlines (ind ++ "  ") body
  | .altSteps spec firstPage otherPage =>
    s!"{ind}{dumpOverlayRange "alt" spec}\n" ++
    s!"{ind}  first page\n" ++ dumpInlines (ind ++ "    ") firstPage ++
    s!"{ind}  other page\n" ++ dumpInlines (ind ++ "    ") otherPage
  | .fill => s!"{ind}fill\n"
  | .hspace g keep =>
    s!"{ind}hspace{if keep then "*" else ""} {Track.css (.affine g)}\n"
  | .rule w h r =>
    s!"{ind}rule {Track.css (.affine w)} × {Track.css (.affine h)} raise {Track.css (.affine r)}\n"
  | .strut _ => s!"{ind}strut\n"
  | .italicCorr maybe => s!"{ind}italicCorr{if maybe then " maybe" else ""}\n"
  | .label key => s!"{ind}label {key.quote}\n"
  | .ref key form text target =>
    let form := match form with
      | .plain => "ref"
      | .paren => "eqref"
      | .cref false => "cref"
      | .cref true => "Cref"
      | .crefRange false => "crefrange"
      | .crefRange true => "Crefrange"
      | .labelOnly => "labelcref"
      | .name false => "namecref"
      | .name true => "nameCref"
    let tgt := match target with
      | some a => s!" -> #{a}"
      | none => ""
    s!"{ind}{form} {key.quote} shows {text.quote}{tgt}\n"
  | .pageNumber => s!"{ind}pagenumber\n"
  | .pageCount => s!"{ind}pagecount\n"
  | .image src size alt =>
    let dim (label : String) (l : Image.Len) : String :=
      let v := match l.value with
        | .lit g => g.width.sp.toPtString ++ "pt"
        | .scale n d (.ref .textHeight) => s!"{n * 1000 / d}/1000th"
        | .scale n d (.ref _) => s!"{n * 1000 / d}/1000tw"
        | .ref .textHeight => "1000/1000th"
        | .ref _ => "1000/1000tw"
        | e => Track.css (.affine e)
      s!" {label} {v}"
    let parts :=
      (match size.width with | some l => dim "width" l | none => "") ++
      (match size.height with | some l => dim "height" l | none => "") ++
      (if size.scaleNum != 1 || size.scaleDen != 1 then
        s!" scale {size.scaleNum}/{size.scaleDen}" else "") ++
      (if size.keepAspect then " keepaspect" else "") ++ alt.dumpSuffix
    s!"{ind}image {src.quote}{parts}\n"
  | .icon c label =>
    s!"{ind}icon {(String.ofList [c]).quote} label {label.quote}\n"
  | .cite form keys =>
    let note (tag s : String) := if s.isEmpty then "" else s!" {tag} {s.quote}"
    s!"{ind}cite {form.command}{if form.full then "*" else ""}{note "pre" form.pre}\
{note "post" form.post} {String.intercalate " " (keys.toList.map (·.quote))}\n"
  | .footnote num body =>
    let tag := match num with
      | some n => s!" {n}"
      | none => ""
    s!"{ind}footnote{tag}\n" ++ dumpInlines (ind ++ "  ") body
  | .linebreak extra =>
    if extra == ({} : SymGlue) then s!"{ind}linebreak\n"
    else s!"{ind}linebreak {dumpGlue extra}\n"

end

/-- One column spec, for the dump: the align letter, then the declared
width. `l:400/1000` is a left `p{.4\linewidth}`; a bare letter is a
natural column; `~` after the letter marks a ragged one (`ColSpec.ragged`),
`l~:400/1000` a `>{\raggedright}p{.4\linewidth}`. -/
private def dumpColSpec (c : ColSpec) : String :=
  let al := match c.align with
    | .left => "l"
    | .center => "c"
    | .right => "r"
  let al := if c.ragged then al ++ "~" else al
  match c.width with
  | .natural => al
  | .sized e =>
    let width := match e with
      | .scale n d (.ref _) => s!"{n * 1000 / d}/1000"
      | .ref _ => "1000/1000"
      | .lit g => g.width.sp.toPtString ++ "pt"
      | other => Track.css (.affine other)
    s!"{al}:{width}"
  | .flex target => s!"{al}:flex:{target.css}"

private def dumpTableRule (r : TableRule) : String :=
  match r with
  | .top => "top"
  | .mid => "mid"
  | .bottom => "bottom"
  | .cmid a b tl tr =>
    let trim := (if tl then "l" else "") ++ (if tr then "r" else "")
    s!"cmid {a}-{b}{if trim.isEmpty then "" else s!"({trim})"}"
  | .gap g => s!"gap {dumpGlue g}"

private def dumpTableCells (ind : String) (acc : String) : List (Array Inline) -> String
  | [] => acc
  | cell :: rest =>
    let inner := dumpInlines (ind ++ "  ") cell
    dumpTableCells ind (acc ++ s!"{ind}cell\n" ++ inner) rest

private def dumpTableRows (ind : String) (acc : String) : List (Array (Array Inline)) -> String
  | [] => acc
  | row :: rest =>
    dumpTableRows ind (dumpTableCells (ind ++ "  ") (acc ++ s!"{ind}row\n") row.toList) rest

mutual

public def dumpBlocks (ind : String) (xs : Array Block) : String :=
  dumpBlockList ind xs.toList

private def dumpBlockList (ind : String) (xs : List Block) : String :=
  match xs with
  | [] => ""
  | b :: rest => dumpBlock ind b ++ dumpBlockList ind rest

private def dumpItems (ind : String) (items : List (Array Block)) : String :=
  match items with
  | [] => ""
  | item :: rest =>
    s!"{ind}item\n" ++ dumpBlocks (ind ++ "  ") item ++ dumpItems ind rest

private def dumpColumns (ind : String) (cols : List (BoxWidth × Array Block)) : String :=
  match cols with
  | [] => ""
  | (w, body) :: rest =>
    let pos := match w.pos with
      | .top => ""
      | .first => " [t]"
      | .center => " [c]"
      | .last => " [b]"
    let self := (match w.size with
      | .sized (.scale n d (.ref _)) =>
        s!"{ind}column {n * 1000 / d}/1000{pos}\n"
      | .sized (.ref _) => s!"{ind}column 1000/1000{pos}\n"
      | .sized (.lit g) => s!"{ind}column {g.width.sp.toPtString}pt{pos}\n"
      | .sized e => s!"{ind}column {Track.css (.affine e)}{pos}\n"
      | .share => s!"{ind}column{pos}\n") ++ dumpBlocks (ind ++ "  ") body
    let tail := dumpColumns ind rest
    self ++ tail

private def dumpBlock (ind : String) (b : Block) : String :=
  match b with
  | .para content => s!"{ind}para\n" ++ dumpInlines (ind ++ "  ") content
  | .equation number content =>
    -- A number that is one run of text keeps its one-line spelling; a tag
    -- carrying markup or math dumps its inlines, as a title does.
    (match number with
      | #[.text s] => s!"{ind}equation {s.quote}\n"
      | _ => s!"{ind}equation\n{ind}  number\n" ++ dumpInlines (ind ++ "    ") number) ++
    dumpInlines (ind ++ "  ") content
  | .section level starred num title =>
    let star := if starred then "*" else ""
    let n := match num with
      | some n => s!" number {n.quote}"
      | none => ""
    s!"{ind}section{star} {level}{n}\n" ++ dumpInlines (ind ++ "  ") title
  | .list ordered items =>
    let kind := if ordered then "ordered" else "unordered"
    s!"{ind}list {kind}\n" ++ dumpItems (ind ++ "  ") items.toList
  | .center body => s!"{ind}center\n" ++ dumpBlocks (ind ++ "  ") body
  | .ragged s body => s!"{ind}ragged {s.label}\n" ++ dumpBlocks (ind ++ "  ") body
  | .quote body => s!"{ind}quote\n" ++ dumpBlocks (ind ++ "  ") body
  | .abstract body => s!"{ind}abstract\n" ++ dumpBlocks (ind ++ "  ") body
  | .titled kind title body =>
    s!"{ind}titled {kind.name}\n" ++
    (if title.isEmpty then ""
     else s!"{ind}  title\n" ++ dumpInlines (ind ++ "    ") title) ++
    dumpBlocks (ind ++ "  ") body
  | .role n body => s!"{ind}role {n}\n" ++ dumpBlocks (ind ++ "  ") body
  | .link target body =>
    s!"{ind}block-link {target.quote}\n" ++ dumpBlocks (ind ++ "  ") body
  | .columns cols => s!"{ind}columns\n" ++ dumpColumns (ind ++ "  ") cols.toList
  | .onSteps spec body =>
    s!"{ind}{dumpOverlayRange "step" spec}\n" ++ dumpBlocks (ind ++ "  ") body
  | .altSteps spec firstPage otherPage =>
    s!"{ind}{dumpOverlayRange "alt" spec}\n" ++
    s!"{ind}  first page\n" ++ dumpBlocks (ind ++ "    ") firstPage ++
    s!"{ind}  other page\n" ++ dumpBlocks (ind ++ "    ") otherPage
  | .note body => s!"{ind}note\n" ++ dumpBlocks (ind ++ "  ") body
  | .only targets body =>
    s!"{ind}only {String.intercalate "," targets.toList}\n" ++ dumpBlocks (ind ++ "  ") body
  | .nav spec body =>
    let label := match spec.label with
      | some l => s!" label {l.quote}"
      | none => ""
    let pin := match spec.pin with
      | some p =>
        s!" pin {if p.top then "top" else "bottom"} \
{if p.left then "left" else "right"} offset {dumpGlue p.offset}" ++
        (if p.reveal then
          match p.revealBy with
          | some g => s!" reveal {dumpGlue g}"
          | none => " reveal scroll"
        else "")
      | none => ""
    s!"{ind}nav{label}{pin}\n" ++ dumpBlocks (ind ++ "  ") body
  | .logo content =>
    if content.isEmpty then s!"{ind}logo clear\n"
    else s!"{ind}logo\n" ++ dumpInlines (ind ++ "  ") content
  | .spaced before body =>
    s!"{ind}block before {dumpSourcedGlue before}\n" ++ dumpBlocks (ind ++ "  ") body
  | .verbatim covered s spec =>
    s!"{ind}verbatim{if covered.isSome then " covered" else ""}\
{if spec.numbers then " numbers" else ""}" ++
    (match spec.caption with
      | some (n, _) => s!" listing {n}"
      | none => "") ++
    (match spec.langToken with
      | some l => s!" language {l}"
      | none => "") ++ "\n" ++
    (match spec.caption with
      | some (_, cap) => s!"{ind}  caption\n" ++ dumpInlines (ind ++ "    ") cap
      | none => "") ++
    String.join ((verbatimLines s).toList.map
      fun l => s!"{ind}  {l.quote}\n")
  | .algorithm numbered semis lines =>
    s!"{ind}algorithm{if numbered then " numbered" else ""}{if semis then "" else " nosemi"}\n" ++
    String.join (lines.toList.map fun l =>
      s!"{ind}  line {l.depth} {l.kind.name}\n" ++
      dumpInlines (ind ++ "    ") l.content ++
      (match l.comment with
       | some c => s!"{ind}    comment\n" ++ dumpInlines (ind ++ "      ") c
       | none => ""))
  | .frame title standout valign _ body =>
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
  | .setPalette pal =>
    s!"{ind}setPalette\n" ++
    String.join (pal.entries.toList.map fun (n, c) =>
      s!"{ind}  {n} = #{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}\n")
  | .setTokens tk =>
    s!"{ind}setTokens\n" ++
    String.join (tk.entries.toList.map fun (n, g) =>
      s!"{ind}  {n} = {dumpGlue g}\n")
  | .pagebreak => s!"{ind}pagebreak\n"
  | .rule color name thickness =>
    let nm := match name with
      | some n => s!" {n}"
      | none => s!" #{Color.hexByte color.r}{Color.hexByte color.g}{Color.hexByte color.b}"
    s!"{ind}rule{nm} {dumpSourcedGlue thickness}\n"
  | .picture pic =>
    -- Every evaluated shape, so a golden witnesses the whole elaboration:
    -- unrolled loops, reduced expressions, resolved colours — and the box
    -- the picture declared, and each node border its natural box counts.
    let boxS := fun (b : Pic.Box) =>
      s!"{b.1.1.toPtString} {b.1.2.toPtString} {b.2.1.toPtString} {b.2.2.toPtString}"
    s!"{ind}picture {pic.shapes.size} shapes{pic.alt.dumpSuffix}\n" ++
    (match pic.declared with
      | some b => s!"{ind}  declared {boxS b}\n"
      | none => "") ++
    (match pic.baseline with
      | some y => s!"{ind}  baseline {y.toPtString}\n"
      | none => "") ++
    String.join (pic.borders.toList.map fun b => s!"{ind}  border {boxS b}\n") ++
    String.join (pic.shapes.toList.map fun s =>
      match s with
      | .rect x y w h c =>
        s!"{ind}  rect {x.toPtString} {y.toPtString} {w.toPtString} {h.toPtString} \
#{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}\n"
      | .label x y content c sc al =>
        let alS := match al with
          | .center => ""
          | .west => " west"
          | .east => " east"
          | .south => " south"
          | .north => " north"
        s!"{ind}  label {x.toPtString} {y.toPtString} \
#{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b} {sc}{alS}\n" ++
        dumpInlines (ind ++ "    ") content
      | .circle x y r st fl =>
        s!"{ind}  circle {x.toPtString} {y.toPtString} {r.toPtString}\
{Pic.paintDump st fl}\n"
      | .frame x y w h st fl =>
        s!"{ind}  frame {x.toPtString} {y.toPtString} {w.toPtString} \
{h.toPtString}{Pic.paintDump st fl}\n"
      | .edge segs st tip =>
        let pts := String.join (segs.toList.map fun sg => match sg with
          | .line x1 y1 x2 y2 =>
            s!" ({x1.toPtString},{y1.toPtString})--({x2.toPtString},{y2.toPtString})"
          | .cubic x1 y1 _ _ _ _ x2 y2 =>
            s!" ({x1.toPtString},{y1.toPtString})~({x2.toPtString},{y2.toPtString})")
        s!"{ind}  edge{pts}{Pic.paintDump (some st) none}\
{if tip.isSome then " tip" else ""}\n")
  | .table cols padL padR rows rules spans =>
    let spec := String.intercalate "," (cols.toList.map dumpColSpec)
    let pads := (if padL then "" else "@{}") ++ spec ++ (if padR then "" else "@{}")
    let ruleLines := String.join (rules.toList.map fun (i, r) =>
      s!"{ind}  rule {i} {dumpTableRule r}\n")
    let spanLines := String.join (spans.toList.map fun sp =>
      s!"{ind}  span {sp.row}:{sp.col} x{sp.n} {dumpColSpec sp.spec}\n")
    dumpTableRows (ind ++ "  ") (s!"{ind}table {pads}\n" ++ ruleLines ++ spanLines) rows.toList
  | .float kind num capAbove body caption =>
    let k := match kind with
      | .figure => "figure"
      | .table => "table"
      | .sub => "sub"
      | .algorithm => "algorithm"
    let n := match num with
      | some n => s!" {n}"
      | none => ""
    s!"{ind}float {k}{n}{if capAbove then " caption-above" else ""}\n" ++
    (if caption.isEmpty then ""
     else s!"{ind}  caption\n" ++ dumpInlines (ind ++ "    ") caption) ++
    dumpBlocks (ind ++ "  ") body
  | .bibliography src style items =>
    let st := match style with
      | some s => s!" style {s.quote}"
      | none => ""
    s!"{ind}bibliography {src.quote}{st}\n" ++
    String.join (items.toList.map fun item =>
      let mark := match item.marker with
        | some m => s!"[{m}] "
        | none => ""
      s!"{ind}  {mark}{item.key.quote}\n" ++
        dumpInlines (ind ++ "    ") item.content)

end

/-- The fraction pending overlay content covers to, unless the document
declares `covered`: 38% of each run's own ink over the surface —
Material's disabled-state opacity (m2.material.io/design/interaction/
states.html#disabled: content at 38% opacity), an *opacity*, so it applies
per colour; compositing over an opaque page is mixing toward it. -/
public def coveredFractionDefault : Nat := 38

/-- One foreground/background pairing a themed element ships. -/
public structure ColorPair where
  fg : Color
  bg : Color
  deriving Repr, BEq

/-- A region's declared paint. Missing channels inherit independently;
an absent background never requests a fill. This is shared design data,
not a backend's choice of fallback colours. -/
public structure SurfaceLook where
  fg : Option Color := none
  bg : Option Color := none
  deriving Repr, BEq

/-- Resolve a region on its enclosing surface, including a nested region
or a frame with its own ground. The declaration remains available to the
painter: `look.bg` alone decides whether to paint a new surface. -/
@[expose] public def SurfaceLook.resolve (look : SurfaceLook) (parent : ColorPair) : ColorPair :=
  { fg := look.fg.getD parent.fg, bg := look.bg.getD parent.bg }

/-- Inheritance is per channel and preserves every explicit declaration.
Both artifacts project this same pair; neither invents a body colour. -/
public theorem SurfaceLook.resolve_contract (look : SurfaceLook) (parent : ColorPair) :
    (look.resolve parent).fg = look.fg.getD parent.fg ∧
    (look.resolve parent).bg = look.bg.getD parent.bg := by
  exact ⟨rfl, rfl⟩

public theorem SurfaceLook.undeclared_exact (parent : ColorPair) :
    (SurfaceLook.mk none none).resolve parent = parent := by rfl

/-- beamer's block colour boxes' `colsep*=.75ex` (beamerinnerthemedefault.sty,
`block begin`), shared by a painted title and body: such a box stands this
far above and below its lines, and its paint reaches this far beyond the
text measure on both sides while the text stays on the measure. The PDF
resolves it against the face's x-height; HTML keeps the `ex`. -/
@[expose] public def titledPadding : Length := { ex := 750 }

public theorem titledPadding_contract (fontSize xHeight : Sp) :
    titledPadding.resolve fontSize xHeight = 3 * xHeight / 4 := by
  simp only [titledPadding, Length.resolve, Int.zero_add, Int.zero_mul, Int.zero_ediv]
  have h : (750 : Int) * xHeight = 250 * (3 * xHeight) := by omega
  rw [h, show (1000 : Int) = 250 * 4 by decide]
  exact Int.mul_ediv_mul_of_pos _ _ (by decide)

/-- A painted title meeting a painted body: `\nointerlineskip\vskip-0.5pt`,
the body box overlapping the title box by half a point. -/
public def blockSeam : Sp := Dim.pt 1 / 2

/-- `n` tenths of TeX's millimetre, 7227⁄2540 of the point this engine's
`pt` is numerically: tcolorbox's lengths (tcolorbox.sty) are TeX's. -/
public def texMmTenths (n : Int) : Sp := n * 7227 * Dim.spPerPt / 25400

/-- tcolorbox's box under its reset style, `size=normal` (tcolorbox.sty,
`size/normal`): the frame's rule (`boxrule=0.5mm`, the title rule the
same), `boxsep=1mm`, `left=right=4mm`, `top=bottom=2mm`, the title's own
`toptitle` and `bottomtitle` zero. Both backends read these. -/
public def tcbRule : Sp := texMmTenths 5
public def tcbBoxsep : Sp := texMmTenths 10
public def tcbSide : Sp := texMmTenths 40
public def tcbTop : Sp := texMmTenths 20
public def tcbBottom : Sp := texMmTenths 20

/-- How far a box's text stands inside its edges, on both sides: the rule,
`boxsep` and `left` (`right`), 5.5 mm. -/
public def tcbInset : Sp := tcbRule + tcbBoxsep + tcbSide

/-- An unpainted body box opens on `\vskip-.25ex\vbox{}`: its first line is
spaced from a box standing a quarter ex above the body box's own top. -/
public def blockBodyRaise : Length := { ex := 250 }

/-- Beamer's three body elements (`beamercolorthemedefault.sty`) start
empty. Themes such as Moloch declare their fills and inheritance through
the palette bindings; no title or accent role implies a body fill. -/
@[expose] public def titledBodyLook (pal : Palette) (kind : TitledKind) : SurfaceLook :=
  { fg := pal.find? (kind.roleStem ++ "bodyfg"), bg := pal.find? (kind.roleStem ++ "bodybg") }

public theorem titledBodyLook_exact (pal : Palette) (kind : TitledKind) :
    (titledBodyLook pal kind).fg = pal.find? (kind.roleStem ++ "bodyfg") ∧
    (titledBodyLook pal kind).bg = pal.find? (kind.roleStem ++ "bodybg") := by
  exact ⟨rfl, rfl⟩

/-- A titled block's resolved look: the title's ink, and the bar behind it
when the palette declares one — no bar key, no bar, exactly the
frame-title rule. -/
public structure TitledLook where
  fg : Color
  bar : Option Color
  deriving Repr, BEq

/-- The one resolving site for the titled block's roles, per kind —
beamer's own parent chain (beamercolorthemedefault.sty: `block title` on
structure, `block title alerted` on `alerted text`, `block title example`
on `example text`), read onto the engine's keys: a bare title takes the
kind's content colour (`alert`, `example`; the ink for `block`), and a
declared `<kind>titlebg` turns the title into a colour bar whose default
ink is the page colour, as the frame-title bar's is. Layout reads it with
the palette in force at the block; `Design.ofDoc` reads it for the
contrast contract. -/
public def titledLook (pal : Palette) : TitledKind → TitledLook
  | .block | .box =>
    let bar := pal.find? "blocktitlebg"
    { fg := (pal.find? "blocktitlefg").getD
        (if bar.isSome then (pal.find? "bg").getD Color.white
         else (pal.find? "fg").getD Color.black)
      bar := bar }
  | .alert =>
    let bar := pal.find? "alerttitlebg"
    { fg := (pal.find? "alerttitlefg").getD
        (if bar.isSome then (pal.find? "bg").getD Color.white
         else (pal.find? "alert").getD ((pal.find? "fg").getD Color.black))
      bar := bar }
  | .example =>
    let bar := pal.find? "exampletitlebg"
    { fg := (pal.find? "exampletitlefg").getD
        (if bar.isSome then (pal.find? "bg").getD Color.white
         else (pal.find? "example").getD ((pal.find? "fg").getD Color.black))
      bar := bar }


/-- The palette roles that declare a listing colour, each for one Pygments
token type: the role reads as that type's colour declaration in the
listing's style, inherited by every descendant that declares none of its
own (`Listing.paint`). -/
public def listingRoles : List (String × ListingHighlight.Kind) :=
  [("codekeyword", .keyword), ("codestring", .string), ("codenumber", .number),
   ("codecomment", .comment), ("codebuiltin", .nameBuiltin), ("codename", .nameFunction),
   ("codeoperator", .operator)]

/-- A listing colour a palette declares: the role, the token type whose
colour it declares, and the colour. -/
public structure ListingRole where
  role : String
  kind : ListingHighlight.Kind
  color : Color
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
public structure Design where
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
  /-- The listing colours the palette declares (`code…` roles). Every other
  token colour is the listing's style's, which the shared painter keeps
  legible on the actual ground; declared ones pass through the ordinary
  contrast judge. -/
  listing : Array ListingRole
  /-- The frame-title bar, when the design has one. -/
  frametitle : Option ColorPair
  /-- The title's ink when no bar is declared, and the subtitle's ink on
  the same title surface. Beamer's subtitle inherits its title. -/
  frameTitleFg : Color
  framesubtitle : Color
  /-- The section divider's heading, on the page's ground. -/
  sectionTitle : Color
  /-- The chrome footline's ink and optional band background. -/
  footline : TitledLook
  /-- The titled block's title look, one per kind (`titledLook`, the one
  resolving site). Total: an undeclared palette pairs the kind's content
  colour with no bar. -/
  blockTitle : TitledLook
  alertTitle : TitledLook
  exampleTitle : TitledLook
  /-- Each body inherits the enclosing surface unless its own channels
  are declared. Title and body surfaces are independent. -/
  blockBody : SurfaceLook
  alertBody : SurfaceLook
  exampleBody : SurfaceLook
  /-- The themed section page and its progress bar, when the design has one. -/
  progress : Option ColorPair
  /-- The section-page variant inherits the base progress colours but
  may override either channel without recolouring other progress sites. -/
  sectionProgress : Option ColorPair
  /-- A `[standout]` frame's pair — total: without the keys it inverts the
  page's own colours. -/
  standout : ColorPair
  /-- The title page's own ground and the ink that stands on it, when the
  design declares one — a title page whose ground differs from the rest of
  the document, which is what a theme spells as a full-bleed fill over the
  page. `none` is the title page that takes the document's own ground, and
  is the undeclared default: a ground nobody declared is never invented
  here (`titleGround_exact`). Declared, the ink defaults by inversion, the
  same rule `standout` follows — a declared ground is usually the page's
  opposite, and inverting is what makes light matter land on a dark title
  page without a second declaration. -/
  titlepage : Option ColorPair
  /-- The title-page rule's colour; the ink when undeclared. Declared by
  both shipped bundles and consumed by no backend yet — the role check in
  `Tests.lean` names it until the title-page rule lands. -/
  separator : Color
  /-- Every role's realized ink on a ground that is not the page (the
  frame-title bar, a titled bar, the standout inversion, the title page):
  one value per role, declaration and ground, which the PDF's runs ship and
  the HTML's scoped tokens declare (`HtmlDoc.realized_agree`). -/
  inks : Array GroundInk
  /-- Thickness of the progress bar, resolved at layout like any token. -/
  progressheight : SymGlue
  styles : Styles
  deriving Repr, BEq

/-- **The one resolving site for every palette role.** Each default the
backends used to apply at their own use sites (`find?` + `getD`, each with
its own chain) is applied here, once — and the argument is a palette rather
than a document precisely because two consumers read two different
palettes: `Design.ofDoc` reads the document's, and the layout reads the
*epoch* palette in force where a frame stands, so a `\setPalette` mid-deck
retitles the frames after it. That difference is the design; the defaults
chain behind it is not, and it was written out a second time in
`Layout.collectFrameTitle` until this function existed
(`frametitle_agree`).

The two fields a palette cannot answer — the progress bar's thickness and
the style table — take their undeclared values here, and `ofDoc` overlays
the document's declarations. -/
@[expose] public def Design.ofPalette (pal : Palette) : Design :=
  let fg := (pal.find? "fg").getD Color.black
  let bg := (pal.find? "bg").getD Color.white
  let frameTitleFg := (pal.find? "frametitlefg").getD fg
  let frametitle := (pal.find? "frametitlebg").map fun barBg =>
    { fg := (pal.find? "frametitlefg").getD bg, bg := barBg : ColorPair }
  let muted := (pal.find? "muted").getD fg
  let footBg := pal.find? "footlinebg"
  let footKey := if (pal.find? "muted").isSome then "muted" else "fg"
  let footInk := footBg.bind fun ground =>
    pal.inks.find? fun e => e.role == footKey && e.declared == muted && e.ground == ground
  { fg := fg
    bg := bg
    fgDeclared := (pal.find? "fg").isSome
    bgDeclared := (pal.find? "bg").isSome
    coveredFraction := pal.coveredFraction.getD coveredFractionDefault
    covered := pal.find? "covered"
    muted := muted
    listing := (listingRoles.filterMap fun (role, kind) =>
      (pal.find? role).map fun color => { role, kind, color }).toArray
    frametitle := frametitle
    frameTitleFg := frameTitleFg
    framesubtitle := (pal.find? "framesubtitlefg").getD
      ((frametitle.map (·.fg)).getD frameTitleFg)
    sectionTitle := (pal.find? "sectiontitlefg").getD fg
    footline := { fg := (footInk.map (·.ink)).getD muted, bar := footBg }
    blockTitle := titledLook pal .block
    alertTitle := titledLook pal .alert
    exampleTitle := titledLook pal .example
    blockBody := titledBodyLook pal .block
    alertBody := titledBodyLook pal .alert
    exampleBody := titledBodyLook pal .example
    progress := (pal.find? "progressfg").map fun barFg =>
      { fg := barFg
        bg := (pal.find? "progressbg").getD bg }
    sectionProgress := ((pal.find? "sectionprogressfg").or (pal.find? "progressfg")).map fun barFg =>
      { fg := barFg
        bg := ((pal.find? "sectionprogressbg").or (pal.find? "progressbg")).getD bg }
    standout := { fg := (pal.find? "standoutfg").getD bg
                  bg := (pal.find? "standoutbg").getD fg }
    titlepage := (pal.find? "titlepagebg").map fun ground =>
      { fg := (pal.find? "titlepagefg").getD bg
        bg := ground }
    separator := (pal.find? "separator").getD fg
    inks := pal.inks
    progressheight := { width := Dim.Length.ofSp (Dim.pt 1) }
    styles := {} }

/-- The body's declaration projected from the resolved design. -/
@[expose] public def Design.titledBody (d : Design) : TitledKind → SurfaceLook
  | .block | .box => d.blockBody
  | .alert => d.alertBody
  | .example => d.exampleBody

public theorem Design.titledBody_projects (pal : Palette) (kind : TitledKind) :
    (Design.ofPalette pal).titledBody kind = titledBodyLook pal kind := by
  cases kind <;> rfl

/-- Read a recorded contrast realization on this surface. Source colours
stay exact unless the contrast judge recorded a bounded correction for
this role, declaration and ground. -/
@[expose] public def Design.inkOn (d : Design) (role : String) (pair : ColorPair) : ColorPair :=
  { pair with fg := ((d.inks.find? fun e =>
      e.role == role && e.declared == pair.fg && e.ground == pair.bg).map (·.ink)).getD pair.fg }

/-- The body inherits its enclosing ink's role as well as its declaration,
so a nested background-only body reads the correction for its own ground. -/
@[expose] public def Design.titledBodyPaint (d : Design) (kind : TitledKind)
    (parent : ColorPair) (parentRole : String) : ColorPair :=
  let look := d.titledBody kind
  d.inkOn (if look.fg.isSome then kind.roleStem ++ "bodyfg" else parentRole) (look.resolve parent)

/-- Ground selection and ink realization share one resolved body value;
realization can change its ink only, never introduce a new ground. -/
public theorem Design.titledBodyPaint_contract (d : Design) (kind : TitledKind)
    (parent : ColorPair) (parentRole : String) :
    (d.titledBodyPaint kind parent parentRole).bg = (d.titledBody kind).bg.getD parent.bg := by
  rfl

public theorem Design.titledBodyPaint_declared_exact (d : Design) (kind : TitledKind)
    (parent : ColorPair) (parentRole : String) (h : d.inks = #[]) :
    d.titledBodyPaint kind parent parentRole = (d.titledBody kind).resolve parent := by
  simp [Design.titledBodyPaint, Design.inkOn, h]

/-- The ground a frame's body stands on when the frame declares one of its
own: a title page's (`titlepagebg`, through `Design.ofPalette`), `none` for
a frame on the page's own ground. The one reading the page painter
(`Layout.titleGround`), the contrast judge and the role-realization walk
(`recolorRolesBlock`) make, so a pair realized on the title page is
rewritten on the title page and painted there. -/
@[expose] public def titleGroundOf (pal : Palette) (valign : VAlign) : Option Color :=
  if valign matches .golden then (Design.ofPalette pal).titlepage.map (·.bg) else none

/-- **The one reading of the ground a frame's pages stand on**, off the
palette in force where the frame stands — the document's, or a body
`\palette`'s epoch, which is how a deck declares one frame's background
(reveal.js's per-slide `data-background-color`, here a declaration both
backends already carry). A `[standout]` frame stands on its inversion
(`Design.standout`), the title page on its own declared ground when it
has one (`titleGroundOf`), and every other frame on the palette's
declared `bg`. `none` is an undeclared ground, which neither backend
paints: the PDF ships no fill and the HTML stage its stylesheet surface.
The page painter reads this (`Layout.collectBlock`'s frame arm), and the
HTML stage resolves the same `--bg` from the epoch's redefinition on its
node (`HtmlDoc.stageGround`); `artStageGroundChecks` holds the two
artifacts to it. -/
public def frameGroundOf (pal : Palette) (standout : Bool) (valign : VAlign) : Option Color :=
  if standout then some (Design.ofPalette pal).standout.bg
  else (titleGroundOf pal valign).orElse fun _ => pal.find? "bg"

/-- **A plain frame stands on the declared `bg` in force, and on nothing
else**: a ground nobody declared is never invented, and an epoch's own
ground is never replaced by the document's — the half of a per-slide
background the page painter owed before it read the palette in force. -/
public theorem frameGround_exact (pal : Palette) (valign : VAlign) (h : ¬ valign = .golden) :
    frameGroundOf pal false valign = pal.find? "bg" := by
  cases valign <;> simp_all [frameGroundOf, titleGroundOf]

/-- The document's resolved design: `ofPalette` over its palette, with the
two declarations a palette does not carry. -/
@[expose] public def Design.ofDoc (doc : Doc) : Design :=
  { Design.ofPalette doc.palette with
    -- The fallback is moloch's own default, `progressbar linewidth=1pt`
    -- (beamerouterthememoloch.dtx, \moloch@outer@setdefaults); the layout
    -- fallback and the bundles' token entries are the same value.
    progressheight := (doc.tokens.find? "progressheight").getD
      { width := Dim.Length.ofSp (Dim.pt 1) }
    styles := doc.styles }

/-- A restored standout footer stands on the standout canvas and uses its
foreground. The deferred `use={standout,background canvas}` colour reads
these values at the frame, after standout has set the canvas; ordinary
footers retain their own pair. Both backends project this one value. -/
public def Design.frameFootLook (d : Design) (standout : Bool) : TitledLook :=
  if standout then { fg := d.standout.fg, bar := some d.standout.bg } else d.footline

public theorem Design.standoutFootLook_projects (d : Design) :
    (d.frameFootLook true).fg = d.standout.fg ∧
    (d.frameFootLook true).bar = some d.standout.bg := ⟨rfl, rfl⟩

/-- **Two projections of one resolved value agree.** The frame-title pair is
a function of the palette alone: the document-level design's pair is the one
`ofPalette` resolves from the document's palette, so the value the PDF reads
at a frame — `(Design.ofPalette epochPalette).frametitle`, the epoch palette
being the only difference — is the same construction and not a second copy
of the chain `frametitlefg` → `bg` → white. `ofDoc`'s overlay could have
touched the pair; this says it does not. -/
public theorem frametitle_agree (doc : Doc) :
    (Design.ofDoc doc).frametitle = (Design.ofPalette doc.palette).frametitle := by rfl

/-- The added Beamer sites travel the same palette resolution chain in
the document design and in an epoch's design. -/
public theorem beamerColors_agree (doc : Doc) :
    ((Design.ofDoc doc).framesubtitle, (Design.ofDoc doc).sectionTitle,
      (Design.ofDoc doc).sectionProgress, (Design.ofDoc doc).footline) =
    ((Design.ofPalette doc.palette).framesubtitle, (Design.ofPalette doc.palette).sectionTitle,
      (Design.ofPalette doc.palette).sectionProgress, (Design.ofPalette doc.palette).footline) := by rfl

/-- The title page's pair travels the same one chain, for the same reason:
the layout resolves the *epoch* palette in force where the title frame
stands and `ofDoc` the document's, so the two must be the same
construction and not two copies of it. -/
public theorem titlepage_agree (doc : Doc) :
    (Design.ofDoc doc).titlepage = (Design.ofPalette doc.palette).titlepage := by rfl

/-- **A ground nobody declared is never invented.** The title page's ground
is the declared role and nothing else: `titlepagebg` unset resolves to no
pair at all, so no page is painted a colour the document did not name, and a
declared one reaches the artifacts as itself rather than as something the
engine chose for it. This is what makes the contrast judge's verdict a
verdict about the author's pair — the defect it forbids is a ground derived
from `fg` or from the standout keys, which would report a failure the
document never wrote. -/
public theorem Design.titleGround_exact (pal : Palette) :
    (Design.ofPalette pal).titlepage.map (·.bg) = pal.find? "titlepagebg" := by
  unfold Design.ofPalette
  cases pal.find? "titlepagebg" <;> rfl

/-- Per-element style, total: the empty style is the default, applied here
rather than at each consumer. -/
public def Design.style (d : Design) (element : String) : ElementStyle :=
  (d.styles.find? element).getD {}

/-- The palette keys whose resolved `Design` field a backend consumes today,
each named with its consumers; `Tests.lean` checks every role a built-in
bundle declares appears here or is a content colour, so a decorative key no
code reads is a named warning, never silence. -/
public def Design.consumedRoles : List String :=
  ["fg", "bg",                        -- Layout.run / B.docBg, the frame and section-
                                      -- page arms (frameGroundOf), HtmlDoc.themeCss
                                      -- and the deck stage (stageGround)
   "covered",                         -- Layout.run's overlay dimming
   "muted",                           -- Layout.run's chrome footer, HtmlDoc.themeCss
   "frametitlefg", "frametitlebg",    -- Layout.collectBlock, HtmlDoc.themeCss
   "framesubtitlefg",                 -- Elab.frameRestGo's coloured title line
   "sectiontitlefg",                  -- Layout.collectSection, HtmlDoc.themeCss
   "footlinebg",                      -- Layout.B.finishPage, HtmlDoc.themeCss
   "blocktitlefg", "blocktitlebg",    -- Layout.collectBlock titled arm,
   "alerttitlefg", "alerttitlebg",    --   HtmlDoc.themeCss (titledLook is
   "exampletitlefg", "exampletitlebg",--   the one resolving site)
   "blockbodyfg", "blockbodybg",      -- Layout and HtmlDoc titled bodies;
   "alertbodyfg", "alertbodybg",      --   Contrast judges their local surface
   "examplebodyfg", "examplebodybg",  --   through titledBodyLook
   "progressfg", "progressbg",        -- Layout.collectBlock, HtmlDoc.themeCss
   "sectionprogressfg", "sectionprogressbg", -- the section-page progress variant
   "standoutfg", "standoutbg",        -- Layout.collectBlock frame arm
   "titlepagefg", "titlepagebg",      -- Layout.titleGround / collectBlock frame
                                      -- arm, HtmlDoc.themeCss, Contrast's
                                      -- titlePageStep
   "separator"] ++                    -- the title-page rule (Elab.titleBlocks
                                      -- via the titlepage style; Layout .rule,
                                      -- HtmlDoc's <hr class="separator">)
  listingRoles.map (·.1)              -- Listing.tokenInline, both backends


/-- How covering paints: the colour of a covered run that had none of its
own, and the per-colour cover of an explicitly coloured one — the same
ink, quieter, never a repaint to one constant. Built once per document by
`Design.cover` (the one resolving site); the walks below only apply it. -/
public structure Cover where
  plain : Color
  of : Color → Color

-- Overlay walks. Structural recursion through `List`, as the printers above.

/-- One component of a numbered overlay: a number, a closed range, or an
open range. Mode and incremental specifications are not numbered selectors. -/
private def overlayInterval (w : String) : Option (Nat × Option Nat) := do
  match w.trimAscii.toString.splitOn "-" with
  | [n] =>
    let n ← n.toNat?
    pure (n, some n)
  | [a, b] =>
    if a.isEmpty && b.isEmpty then none else do
      let n ← if a.isEmpty then some 1 else a.toNat?
      if b.isEmpty then pure (n, none) else do
        let u ← b.toNat?
        pure (n, some u)
  | _ => none

/-- The shared reader for every numbered overlay entry, including overprint.
A comma is union; every component must be numbered. An unsupported component
refuses the entire selector instead of silently dropping steps. -/
public def overlayRange (w : String) : Option OverlaySpec := do
  if !(w.startsWith "<" && w.endsWith ">" && w.length ≥ 3) then none else do
    let ranges ← (((w.drop 1).dropEnd 1).toString.splitOn ",").mapM overlayInterval
    match ranges with
    | (n, last) :: more => pure ⟨n, last, more⟩
    | [] => none

/-- The single-interval projection of `OverlaySpec.showsFirst`. Actual
overlay nodes carry the full selector, including disjoint intervals. -/
@[expose] public def altShowsFirst (n : Nat) (last : Option Nat) (k : Nat) : Bool :=
  (OverlaySpec.mk n last []).showsFirst k

/-- Step 1 inks the group stored first: page order, as a fact rather than a
convention a later reader has to trust. -/
public theorem altShowsFirst_id (n : Nat) (last : Option Nat) :
    altShowsFirst n last 1 = true :=
  OverlaySpec.showsFirst_id _

/-- Single-interval projection of the shared reachability decision. -/
public def altReachesOther (n : Nat) (last : Option Nat) (steps : Nat) : Bool :=
  (OverlaySpec.mk n last []).reachesOther steps

/-- Is the group stored first the one a *pending* step inks? The side of the
spec page order put it on, and the only per-node fact an artifact needs
beyond the range itself: a consumer that can test `stepPending` at a step
recovers `altShowsFirst` from it (`altShowsFirst_side`). The HTML deck tags
each group's wrapper with this, because a stylesheet can test the range but
not read a node's two groups — so both artifacts decide from the one
arithmetic instead of each re-deriving the selection. -/
public def altFirstWhenPending (n : Nat) (last : Option Nat) : Bool :=
  (OverlaySpec.mk n last []).pending 1

/-- The predicate, factored the way a per-step consumer can use it: whether
step `k` inks the group stored first is whether `k`'s pending state matches
the side page order gave that group. The equation both artifacts read —
the PDF page tests `altShowsFirst` directly at layout's arms, the HTML deck
tests `stepPending` in its own per-snap selectors and compares against the
tagged side (`HtmlDoc.alt_backend_agree`). -/
public theorem altShowsFirst_side (n : Nat) (last : Option Nat) (k : Nat) :
    altShowsFirst n last k = (stepPending n last k == altFirstWhenPending n last) := by
  simp [altShowsFirst, altFirstWhenPending, OverlaySpec.showsFirst]

mutual

/-- The last step a frame's body reaches. `frameSteps` also includes its
title when counting handout pages. A frame nested below another block
keeps one page. -/
public def maxStepBlocks (xs : Array Block) : Nat := maxStepBlockList xs.toList

private def maxStepBlockList : List Block → Nat
  | [] => 1
  | b :: rest => max (maxStepBlock b) (maxStepBlockList rest)

/-- Exhaustive by design (never add a wildcard arm). The `1` arms are
decisions, not gaps: furniture (a section title, a frame footer) and the
note side channel sit outside the overlay model — the dim walks keep them
whole, so a step there must not multiply handout pages either — and
verbatim carries no inline structure. -/
private def maxStepBlock : Block → Nat
  | .para content => maxStepInlines content
  | .equation _ content => maxStepInlines content
  | .list _ items => maxStepItems items.toList
  | .center body => maxStepBlockList body.toList
  | .ragged _ body => maxStepBlockList body.toList
  | .quote body => maxStepBlockList body.toList
  | .abstract body => maxStepBlockList body.toList
  -- A titled block's title is furniture and does not multiply pages;
  -- the body's own steps take theirs.
  | .titled _ _ body => maxStepBlockList body.toList
  | .role _ body => maxStepBlockList body.toList
  | .link _ body => maxStepBlockList body.toList
  | .spaced _ body => maxStepBlockList body.toList
  | .columns cols => maxStepColumns cols.toList
  | .onSteps spec body => max (spec.maxStep) (maxStepBlockList body.toList)
  | .altSteps spec firstPage otherPage =>
    max (spec.maxStep)
      (max (maxStepBlockList firstPage.toList) (maxStepBlockList otherPage.toList))
  -- Conditional content steps like any other content: a backend that keeps
  -- it must give its overlays their pages. A nav's links may step too.
  | .only _ body => maxStepBlockList body.toList
  | .nav _ body => maxStepBlockList body.toList
  | .section _ _ _ _ => 1
  | .verbatim _ _ _ => 1
  | .algorithm _ _ lines => maxStepAlgLines lines.toList
  | .note _ => 1
  | .frame _ _ _ _ _ => 1
  | .framefoot _ => 1
  | .setPalette _ => 1
  | .setTokens _ => 1
  | .pagebreak => 1
  | .logo _ => 1
  | .rule _ _ _ => 1
  -- A picture is concrete ink with no overlay structure inside it.
  | .picture _ => 1
  -- A cell's content may step (an overlay reveal per row); the caption is
  -- furniture and does not multiply pages.
  | .table _ _ _ rows _ _ => maxStepTableRows rows.toList
  | .float _ _ _ body _ => maxStepBlockList body.toList
  -- A reference list is furniture like a section title: no overlay inside.
  | .bibliography _ _ _ => 1

private def maxStepTableRows : List (Array (Array Inline)) → Nat
  | [] => 1
  | row :: rest => max (maxStepTableCells row.toList) (maxStepTableRows rest)

private def maxStepTableCells : List (Array Inline) → Nat
  | [] => 1
  | cell :: rest => max (maxStepInlines cell) (maxStepTableCells rest)

private def maxStepItems : List (Array Block) → Nat
  | [] => 1
  | item :: rest => max (maxStepBlockList item.toList) (maxStepItems rest)

private def maxStepColumns : List (BoxWidth × Array Block) → Nat
  | [] => 1
  | (_, body) :: rest => max (maxStepBlockList body.toList) (maxStepColumns rest)

private def maxStepAlgLines : List AlgLine → Nat
  | [] => 1
  | l :: rest =>
    max (max (maxStepInlineList l.content.toList)
      (match l.comment with
       | some c => maxStepInlineList c.toList
       | none => 1))
      (maxStepAlgLines rest)

public def maxStepInlines (xs : Array Inline) : Nat := maxStepInlineList xs.toList

private def maxStepInlineList : List Inline → Nat
  | [] => 1
  | x :: rest => max (maxStepInline x) (maxStepInlineList rest)

private def maxStepInline : Inline → Nat
  | .styled _ body => maxStepInlineList body.toList
  | .colored _ _ body => maxStepInlineList body.toList
  | .located _ body => maxStepInlineList body.toList
  | .role _ body => maxStepInlineList body.toList
  | .link _ body => maxStepInlineList body.toList
  | .decorated _ body => maxStepInlineList body.toList
  | .footnote _ body => maxStepInlineList body.toList
  | .onSteps spec body => max (spec.maxStep) (maxStepInlineList body.toList)
  | .altSteps spec firstPage otherPage =>
    max (spec.maxStep)
      (max (maxStepInlineList firstPage.toList) (maxStepInlineList otherPage.toList))
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ | .cite _ _ => 1

end

/-- The declared overlay extent of a top-level frame's title and body,
or zero for any other block. LuaLaTeX gives a frame with only
`\frametitle{\alt<1,4>{Amber}{Blue}}` four pages; a subtitle is part of
the same title inlines. Physical pagination can add spill pages beyond
this overlay extent. `Layout.pages_partition_frames` partitions actual
shipped pages into unique source/step and flow buckets and accounts for
all pages, including spills. `frameSteps_covers` holds the title and body
endpoints to this declared extent. -/
public def frameSteps (b : Block) : Nat :=
  if let .frame title _ _ _ body := b then
    max 1 (max (maxStepInlines title) (maxStepBlocks body))
  else 0

/-- Every numbered endpoint in a frame's title or body has a page in its
shared extent. -/
public theorem frameSteps_covers (title : Array Inline) (standout : Bool)
    (valign : VAlign) (breakable : Bool) (body : Array Block) :
    maxStepInlines title ≤ frameSteps (.frame title standout valign breakable body) ∧
    maxStepBlocks body ≤ frameSteps (.frame title standout valign breakable body) := by
  simp only [frameSteps]
  constructor <;> omega

/-- A title whose endpoints fit within the body's extent adds no pages. -/
public theorem frameSteps_body_exact (title : Array Inline) (standout : Bool)
    (valign : VAlign) (breakable : Bool) (body : Array Block)
    (h : maxStepInlines title ≤ maxStepBlocks body) :
    frameSteps (.frame title standout valign breakable body) = max 1 (maxStepBlocks body) := by
  simp [frameSteps, Nat.max_eq_right h]

/-- Alternation groups no step of their own frame inks, counted over the
document's frames — block alternations and inline ones alike. **Zero is the
contract.** Two consecutive step pages that ship the same ink are either a
document that meant it or an engine that lost an increment, and the engine
cannot tell those apart after the fact; an unreachable group, though, is
decidable *before* the pages are built, from the range and the frame's own
step window. An overprint whose items were chained head-first produced
exactly this — `\onslide<1->` then `\onslide<2->` left item 1 winning on
every step and item 2 reachable from none, two byte-identical pages, no
diagnostic — so the shape is checked rather than trusted. Only the group
stored *second* can be unreachable (`altShowsFirst_id` gives step 1 to the
first), and only a non-empty one is a loss: the empty other group is what a
chain's last link carries, and it inks nothing whether a step reaches it or
not. A leaf function over `foldBlocks`, not a new walk. -/
public def altUnreachable (doc : Doc) : Nat :=
  doc.body.foldl (init := 0) fun n b =>
    match b with
    | .frame _ _ _ _ body =>
      let steps := frameSteps b
      n + foldBlocks
        (fun k blk => match blk with
          | .altSteps spec _ o => if spec.reachesOther steps || o.isEmpty then k else k + 1
          | .para _ | .section _ _ _ _ | .list _ _ | .center _ | .ragged _ _
          | .spaced _ _ | .role _ _ | .link _ _ | .quote _ | .abstract _
          | .titled _ _ _ | .equation _ _ | .verbatim _ _ _ | .algorithm _ _ _
          | .columns _ | .onSteps _ _ | .note _ | .only _ _ | .nav _ _ | .logo _
          | .pagebreak | .frame _ _ _ _ _ | .framefoot _ | .setPalette _ | .setTokens _
          | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ | .float _ _ _ _ _
          | .bibliography _ _ _ => k)
        (fun k x => match x with
          | .altSteps spec _ o => if spec.reachesOther steps || o.isEmpty then k else k + 1
          | .text _ | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _
          | .located _ _ | .role _ _ | .link _ _ | .label _ | .ref _ _ _ _
          | .decorated _ _ | .fill | .hspace _ _ | .rule _ _ _
          | .pageNumber | .pageCount | .linebreak _ | .strut _ | .italicCorr _
          | .onSteps _ _ | .image _ _ _ | .icon _ _ | .cite _ _ | .footnote _ _ => k)
        0 body
    | .para _ | .section _ _ _ _ | .list _ _ | .center _ | .ragged _ _
    | .spaced _ _ | .role _ _ | .link _ _ | .quote _ | .abstract _
    | .titled _ _ _ | .equation _ _ | .verbatim _ _ _ | .algorithm _ _ _
    | .columns _ | .onSteps _ _ | .altSteps _ _ _ | .note _ | .only _ _
    | .nav _ _ | .logo _ | .pagebreak | .framefoot _ | .setPalette _ | .setTokens _
    | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ | .float _ _ _ _ _
    | .bibliography _ _ _ => n

mutual

/-- One overlay walk, two modes, selected by `pending`. Off, it is the dim
walk: the frame's body as step `k` of its overlay shows it — content
outside a step's declared range flips the flag and covers, everything else
stays. On, it is the cover itself: every paragraph below here covered.
Covered means covered — an explicit colour nested inside (an alert, a
palette name) is covered too, exactly as beamer's transparent covering
mutes coloured text — but covered means *the same colour, quieter*: each
coloured run takes its own cover (`cover.of`), never a repaint to one
constant that would make a covered alert and a covered example the same
grey. Runs with no colour of their own take `cover.plain`; a titled
block's heading has one, the block title's ink, which resolves at layout
from the palette in force and takes its cover there with the block's
boxes; verbatim dims through its own `covered` field; section blocks carry
no colour and stay (recorded in PLAN). Only colours change in either mode,
so no step can reflow the slide — the cover-not-hide invariant, by
construction. -/
private def dimBlockList (cover : Cover) (k : Nat) (pending : Bool) (out : Array Block) :
    List Block → Array Block
  | [] => out
  | b :: rest =>
    dimBlockList cover k pending (out.push (dimBlock cover k pending b)) rest

private def dimBlock (cover : Cover) (k : Nat) (pending : Bool) : Block → Block
  | .para content =>
    if pending then
      .para #[.colored cover.plain none (dimInlineList cover k true #[] content.toList)]
    else .para (dimInlineList cover k false #[] content.toList)
  | .equation num content =>
    if pending then
      .equation num #[.colored cover.plain none (dimInlineList cover k true #[] content.toList)]
    else .equation num (dimInlineList cover k false #[] content.toList)
  | .list o items => .list o (dimItems cover k pending #[] items.toList)
  | .center body => .center (dimBlockList cover k pending #[] body.toList)
  | .ragged s body => .ragged s (dimBlockList cover k pending #[] body.toList)
  | .quote body => .quote (dimBlockList cover k pending #[] body.toList)
  | .abstract body => .abstract (dimBlockList cover k pending #[] body.toList)
  | .titled kind title body =>
    .titled kind (dimInlineList cover k pending #[] title.toList)
      (dimBlockList cover k pending #[] body.toList)
  | .role n body => .role n (dimBlockList cover k pending #[] body.toList)
  | .link target body => .link target (dimBlockList cover k pending #[] body.toList)
  | .spaced g body => .spaced g (dimBlockList cover k pending #[] body.toList)
  | .columns cols => .columns (dimColumns cover k pending #[] cols.toList)
  -- The mode flip: a pending step's body covers, and inside a cover a
  -- nested step stays covered — `\uncover<2>` covers on 1 and again from 3,
  -- exactly as beamer's transparent covering does.
  | .onSteps spec body =>
    .onSteps spec (dimBlockList cover k (pending || spec.pending k) #[] body.toList)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (dimBlockList cover k pending #[] firstPage.toList)
      (dimBlockList cover k pending #[] otherPage.toList)
  | .only targets body => .only targets (dimBlockList cover k pending #[] body.toList)
  | .nav spec body => .nav spec (dimBlockList cover k pending #[] body.toList)
  | .section l st num title => .section l st num title
  | .verbatim c s spec =>
    .verbatim (if pending then some cover.plain else c) s
      { spec with caption := spec.caption.map fun (n, cap) =>
          (n, dimInlineList cover k pending #[] cap.toList) }
  -- Lines cover and dim as paragraphs do, comment included: only colours
  -- change, so no step can reflow the pseudocode.
  | .algorithm n sm lines => .algorithm n sm (dimAlgLines cover k pending #[] lines.toList)
  | .note body => .note body
  | .frame t st v br body => .frame t st v br body
  | .framefoot content => .framefoot content
  -- A stateful declaration carries no ink: covering changes only colours
  -- of content, never the state the declaration installs.
  | .setPalette pal => .setPalette pal
  | .setTokens tk => .setTokens tk
  | .pagebreak => .pagebreak
  | .logo content => .logo content
  | .rule c nm th => .rule c nm th
  -- A picture has no overlay structure inside it: covered, each shape takes
  -- its own colour's cover, exactly as a coloured run does.
  | .picture p => .picture (if pending then p.recolor cover.of else p)
  -- Cells cover as paragraphs do and dim in place: only colours change, so
  -- no step can reflow the grid. Rules are decorative ink and keep their
  -- weight; the caption covers and dims with its float.
  | .table cols pl pr rows rules spans =>
    .table cols pl pr (dimTableRows cover k pending #[] rows.toList) rules spans
  | .float fk num ca body caption =>
    .float fk num ca (dimBlockList cover k pending #[] body.toList)
      (if pending then
        if caption.isEmpty then caption
        else #[.colored cover.plain none (dimInlineList cover k true #[] caption.toList)]
       else dimInlineList cover k false #[] caption.toList)
  -- A reference list is furniture, like a section title: the dim walk
  -- keeps it whole (the `.section` decision, recorded in PLAN).
  | .bibliography src style items => .bibliography src style items

private def dimTableRows (cover : Cover) (k : Nat) (pending : Bool)
    (out : Array (Array (Array Inline))) :
    List (Array (Array Inline)) → Array (Array (Array Inline))
  | [] => out
  | row :: rest =>
    dimTableRows cover k pending (out.push (dimTableCells cover k pending #[] row.toList)) rest

private def dimTableCells (cover : Cover) (k : Nat) (pending : Bool)
    (out : Array (Array Inline)) :
    List (Array Inline) → Array (Array Inline)
  | [] => out
  | cell :: rest =>
    dimTableCells cover k pending (out.push
      (if pending then
        if cell.isEmpty then cell
        else #[.colored cover.plain none (dimInlineList cover k true #[] cell.toList)]
       else dimInlineList cover k false #[] cell.toList)) rest

private def dimItems (cover : Cover) (k : Nat) (pending : Bool) (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest =>
    dimItems cover k pending (out.push (dimBlockList cover k pending #[] item.toList)) rest

private def dimColumns (cover : Cover) (k : Nat) (pending : Bool)
    (out : Array (BoxWidth × Array Block)) :
    List (BoxWidth × Array Block) → Array (BoxWidth × Array Block)
  | [] => out
  | (w, body) :: rest =>
    dimColumns cover k pending (out.push (w, dimBlockList cover k pending #[] body.toList)) rest

private def dimAlgLines (cover : Cover) (k : Nat) (pending : Bool) (out : Array AlgLine) :
    List AlgLine → Array AlgLine
  | [] => out
  | l :: rest =>
    let content := if pending then
        (if l.content.isEmpty then l.content
         else #[.colored cover.plain none (dimInlineList cover k true #[] l.content.toList)])
      else dimInlineList cover k false #[] l.content.toList
    let comment := match l.comment with
      | some c =>
        some (if pending then
            (if c.isEmpty then c
             else #[Inline.colored cover.plain none (dimInlineList cover k true #[] c.toList)])
          else dimInlineList cover k false #[] c.toList)
      | none => Option.none
    dimAlgLines cover k pending (out.push
      { depth := l.depth
        kind := l.kind
        content := content
        comment := comment }) rest

private def dimInlineList (cover : Cover) (k : Nat) (pending : Bool) (out : Array Inline) :
    List Inline → Array Inline
  | [] => out
  | x :: rest =>
    dimInlineList cover k pending (out.push (dimInline cover k pending x)) rest

private def dimInline (cover : Cover) (k : Nat) (pending : Bool) : Inline → Inline
  | .styled st body => .styled st (dimInlineList cover k pending #[] body.toList)
  | .colored c nm body =>
    if pending then .colored (cover.of c) none (dimInlineList cover k true #[] body.toList)
    else .colored c nm (dimInlineList cover k false #[] body.toList)
  -- a role is a name, not ink: the cover dims what is inside it
  | .located n body => .located n (dimInlineList cover k pending #[] body.toList)
  | .role n body => .role n (dimInlineList cover k pending #[] body.toList)
  | .link u body => .link u (dimInlineList cover k pending #[] body.toList)
  | .decorated kind body => .decorated kind (dimInlineList cover k pending #[] body.toList)
  -- The inline flip wraps: a covered paragraph's plain cover comes from its
  -- block wrapper, but a pending inline step must bring its own.
  | .onSteps spec body =>
    if !pending && spec.pending k then
      .onSteps spec #[.colored cover.plain none (dimInlineList cover k true #[] body.toList)]
    else .onSteps spec (dimInlineList cover k pending #[] body.toList)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (dimInlineList cover k pending #[] firstPage.toList)
      (dimInlineList cover k pending #[] otherPage.toList)
  | .text s => .text s
  | .math d src => .math d src
  -- the walk leaves formula and image nodes whole: a pending formula or
  -- raster dims in the backends' hands, not here
  | .formula d src body => .formula d src body
  | .image src size alt => .image src size alt
  | .icon s l => .icon s l
  | .label k => .label k
  | .ref k p t tg => .ref k p t tg
  | .fill => .fill
  | .hspace g keep => .hspace g keep
  | .rule w h r => .rule w h r
  | .strut h => .strut h
  | .italicCorr m => .italicCorr m
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak e => .linebreak e
  -- a citation dims with its paragraph's cover, like bare text: no colour
  -- of its own, so the walk leaves it whole
  | .cite t keys => .cite t keys
  -- a note's body dims like any content: recoloured inside, never removed
  | .footnote n body => .footnote n (dimInlineList cover k pending #[] body.toList)

end

/-- The frame's body as step `k` of its overlay shows it: the walk's page
entry, `pending` off. -/
public def dimBlocks (cover : Cover) (k : Nat) (xs : Array Block) : Array Block :=
  dimBlockList cover k false #[] xs.toList

/-- The item flatten itself: a leading `.step` wrapper that opens on a
paragraph gives the item that paragraph, where the marker attaches, and
keeps the rest of its body under the wrapper; a wrapper opening on anything
else stands whole, and an empty one goes. The wrapper must reach what
follows the paragraph: a block's boxes and heading ink resolve at layout and
take the step's cover there (`Layout`'s `.onSteps` arm), and flattened they
shipped at full ink on the steps that do not show their item. Named so its
text conservation is one lemma, not a case buried inside the walk. -/
public def flattenLeadStep (item : Array Block) : Array Block :=
  match item[0]? with
  | some (Block.onSteps spec body) =>
    match (body[0]? : Option Block) with
    | some (.para p) =>
      #[.para p] ++
        (if body.size ≤ 1 then #[] else #[Block.onSteps spec (body.extract 1 body.size)]) ++
        item.extract 1 item.size
    | none => item.extract 1 item.size
    | some (.onSteps _ _) | some (.section _ _ _ _) | some (.list _ _) | some (.center _)
    | some (.ragged _ _) | some (.spaced _ _) | some (.role _ _) | some (.link _ _)
    | some (.quote _) | some (.abstract _) | some (.titled _ _ _) | some (.equation _ _)
    | some (.verbatim _ _ _) | some (.algorithm _ _ _) | some (.columns _)
    | some (.altSteps _ _ _) | some (.note _) | some (.only _ _) | some (.nav _ _)
    | some (.logo _) | some .pagebreak | some (.frame _ _ _ _ _) | some (.framefoot _)
    | some (.setPalette _) | some (.setTokens _) | some (.rule _ _ _) | some (.picture _)
    | some (.table _ _ _ _ _ _) | some (.float _ _ _ _ _) | some (.bibliography _ _ _) => item
  | none => item
  | some (.para _) | some (.section _ _ _ _) | some (.list _ _) | some (.center _)
  | some (.ragged _ _) | some (.spaced _ _) | some (.role _ _) | some (.link _ _)
  | some (.quote _) | some (.abstract _) | some (.titled _ _ _) | some (.equation _ _)
  | some (.verbatim _ _ _) | some (.algorithm _ _ _) | some (.columns _)
  | some (.altSteps _ _ _) | some (.note _) | some (.only _ _) | some (.nav _ _)
  | some (.logo _) | some .pagebreak | some (.frame _ _ _ _ _) | some (.framefoot _)
  | some (.setPalette _) | some (.setTokens _) | some (.rule _ _ _) | some (.picture _)
  | some (.table _ _ _ _ _ _) | some (.float _ _ _ _ _) | some (.bibliography _ _ _) => item

mutual

/-- Inside a list item, a leading `.step` (an overlay `\item<2->`) is pure
grouping by the time layout runs — dimming is already painted into colours —
but it hides the item's first paragraph from the walk that attaches the
marker. Flatten it, so the marker lands where LaTeX puts the label. Layout's
own pre-pass; the HTML backend keeps the wrapper for its `data-step`. -/
public def unwrapItemSteps (xs : Array Block) : Array Block :=
  unwrapItemStepList #[] xs.toList

private def unwrapItemStepList (out : Array Block) : List Block → Array Block
  | [] => out
  | b :: rest => unwrapItemStepList (out.push (unwrapItemStep b)) rest

public def unwrapItemStep : Block → Block
  | .list o items => .list o (unwrapItemStepItems #[] items.toList)
  | .center body => .center (unwrapItemStepList #[] body.toList)
  | .ragged s body => .ragged s (unwrapItemStepList #[] body.toList)
  | .quote body => .quote (unwrapItemStepList #[] body.toList)
  | .abstract body => .abstract (unwrapItemStepList #[] body.toList)
  | .titled kind title body => .titled kind title (unwrapItemStepList #[] body.toList)
  | .role n body => .role n (unwrapItemStepList #[] body.toList)
  | .link target body => .link target (unwrapItemStepList #[] body.toList)
  | .spaced g body => .spaced g (unwrapItemStepList #[] body.toList)
  | .columns cols => .columns (unwrapItemStepCols #[] cols.toList)
  | .onSteps spec body => .onSteps spec (unwrapItemStepList #[] body.toList)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (unwrapItemStepList #[] firstPage.toList)
      (unwrapItemStepList #[] otherPage.toList)
  | .only targets body => .only targets (unwrapItemStepList #[] body.toList)
  | .nav spec body => .nav spec (unwrapItemStepList #[] body.toList)
  | .frame t s v br body => .frame t s v br (unwrapItemStepList #[] body.toList)
  | .para content => .para content
  | .equation n content => .equation n content
  | .section l st num title => .section l st num title
  | .verbatim c s sp => .verbatim c s sp
  | .algorithm n sm lines => .algorithm n sm lines
  | .note body => .note body
  | .framefoot content => .framefoot content
  | .setPalette pal => .setPalette pal
  | .setTokens tk => .setTokens tk
  | .pagebreak => .pagebreak
  | .logo content => .logo content
  | .rule c nm th => .rule c nm th
  | .picture p => .picture p
  -- A cell holds inlines and a caption is furniture: no item paragraph can
  -- hide below either, so both nodes pass whole (float body walked: a
  -- listed figure body may hold a list).
  | .table cols pl pr rows rules spans => .table cols pl pr rows rules spans
  | .float k n ca body caption => .float k n ca (unwrapItemStepList #[] body.toList) caption
  -- A reference list holds entries, never item paragraphs.
  | .bibliography src style items => .bibliography src style items

private def unwrapItemStepItems (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest =>
    unwrapItemStepItems
      (out.push (flattenLeadStep (unwrapItemStepList #[] item.toList))) rest

private def unwrapItemStepCols (out : Array (BoxWidth × Array Block)) :
    List (BoxWidth × Array Block) → Array (BoxWidth × Array Block)
  | [] => out
  | (w, body) :: rest =>
    unwrapItemStepCols (out.push (w, unwrapItemStepList #[] body.toList)) rest

end

/-- Layout's item pre-pass preserves a paragraph verbatim. The collector reads
this equation without depending on the pre-pass's private traversal state. -/
public theorem unwrapItemStep_para_exact (content : Array Inline) :
    unwrapItemStep (.para content) = .para content := by
  rfl

/-- The conservation shape, named once: `f` leaves the census fixed. Every
public IR-to-IR walk states its conservation as an instance of this — one
shape, many instances — so an instance is grep-recognisable and the
pre-commit hook can ask a new walk for one (or for the one-line refusal
naming why none holds). -/
@[expose] public def Conserves (census : α → β) (f : α → α) : Prop :=
  ∀ x, census (f x) = census x

/-- Body-transparent wraps, once: a constructor whose own census is exactly
its body's conserves the census when wrapped around any content.
`langWrap_text`, `footnoteWrap_text`, and `decorated_text` are its
one-line instances (`rfl` per constructor), and the next wrapper's costs
the same line. -/
public theorem wrap_text (w : Array Inline → Inline)
    (hw : ∀ xs, plainTextOne (w xs) = plainText xs) :
    Conserves plainText (fun xs => #[w xs]) := fun xs => by
  simp [plainText, plainTextList, hw]

/-- Diagnostic provenance is transparent to the text census. In particular,
an empty annotation adds neither content nor a template hole. -/
public theorem located_text (span : Span) :
    Conserves plainText (fun xs => #[.located span xs]) :=
  wrap_text (.located span) fun _ => rfl

/-- Wrap inline content in a language switch: what `\foreignlanguage`,
`\selectlanguage`, and `otherlanguage` become. -/
public def langWrap (tag : String) (xs : Array Inline) : Array Inline :=
  #[.styled (.lang tag) xs]

/-- Language markup has one declared wrapper around its unchanged content. -/
public theorem langWrap_exact (tag : String) (xs : Array Inline) :
    langWrap tag xs = #[.styled (.lang tag) xs] := by
  rfl

/-- The language attribute is pure markup: tagging content ships exactly
the text census the content already had — `langWrap_text` below, an
instance of `wrap_text` because the census ignores style wrappers. -/
public theorem langWrap_text (tag : String) :
    Conserves plainText (langWrap tag) :=
  wrap_text (.styled (.lang tag)) fun _ => rfl

/-- Wrap inline content as a footnote's body: what `\footnote` becomes. -/
public def footnoteWrap (num : Option Nat) (xs : Array Inline) : Array Inline :=
  #[.footnote num xs]

/-- The note body is document text: marking content as a footnote ships
exactly the text census the content already had. The mark digit is
generated ink, excluded as `citeMark` is. -/
public theorem footnoteWrap_text (num : Option Nat) :
    Conserves plainText (footnoteWrap num) :=
  wrap_text (.footnote num) fun _ => rfl

/-- A link's ink (`Styles.linkInk`) is a body-transparent wrap
(`Inline.colored`, whose census is its body's) where the kind declares a
colour, and the body unchanged where it does not, so it ships exactly the
text census the body already had — the `Styles` walk's conservation fact
(AGENTS.md, obligation table). -/
public theorem Styles_text (s : Styles) (kind : String) :
    Conserves plainText (s.linkInk kind) := by
  intro body
  unfold Styles.linkInk
  match (s.find? kind).bind (·.color) with
  | none => rfl
  | some (c, n) => exact wrap_text (Inline.colored c n) (fun _ => rfl) body

-- Nothing vanishes: dimming recolours, never removes. The text of a frame's
-- body is identical on every handout page, so the union of what the steps
-- show is the whole content — each page already shows all of it, dimmed or
-- not. Stated over the walks above and proved by the same structural
-- recursion; a step function that dropped or reordered content would fail
-- these equalities.

/-- A listing caption's census text: the declared characters, `""` when
none is declared. The number prefix is backend furniture, excluded as a
float's `captionPrefix` is. -/
@[expose] public def ListingSpec.capText (spec : ListingSpec) : String :=
  match spec.caption with
  | some (_, cap) => plainText cap
  | none => ""

/-- The algorithm lines' census: each line's declared content, then its
comment — the keywords a kind implies are generated by the backends
(`AlgLine.rendered`) and never counted, exactly as caption prefixes are
not (`algorithm_text` is the statement). -/
@[expose] public def algLineText (acc : String) : List AlgLine → String
  | [] => acc
  | l :: rest =>
    algLineText (match l.comment with
      | some c =>
        let pc := plainText c
        (acc ++ plainText l.content) ++ pc
      | none => acc ++ plainText l.content) rest

mutual

/-- The characters of block content with every mark stripped: the block
companion of `plainText`, and what the overlay walks must preserve. The
accumulator threads through, as every walk here does. -/
@[expose] public def blocksText (xs : Array Block) : String := blockTextList "" xs.toList

@[expose] public def blockTextList (acc : String) : List Block → String
  | [] => acc
  | b :: rest => blockTextList (blockTextOne acc b) rest

@[expose] public def blockTextOne (acc : String) : Block → String
  | .para content =>
    let t := plainText content
    acc ++ t
  -- an equation's number ships beside its formula in every backend
  | .equation number content =>
    let t := plainText content
    let n := plainText number
    acc ++ t ++ n
  | .section _ _ _ title =>
    let t := plainText title
    acc ++ t
  | .list _ items => blockTextItems acc items.toList
  | .center body => blockTextList acc body.toList
  | .ragged _ body => blockTextList acc body.toList
  -- A quotation's text is real census content, exactly as a paragraph's.
  | .quote body => blockTextList acc body.toList
  | .abstract body => blockTextList acc body.toList
  -- The title counts with its block, before the body, as a frame's does;
  -- the bar and background are decorative ink and ship no characters.
  | .titled _ title body => blockTextList (acc ++ plainText title) body.toList
  | .role _ body => blockTextList acc body.toList
  | .link _ body => blockTextList acc body.toList
  | .spaced _ body => blockTextList acc body.toList
  | .columns cols => blockTextColumns acc cols.toList
  | .onSteps _ body => blockTextList acc body.toList
  | .altSteps _ firstPage otherPage =>
    blockTextList (blockTextList acc firstPage.toList) otherPage.toList
  -- The census reads the DECLARED content: what a conditional addresses to
  -- one backend is still content the document declares, so it counts here;
  -- `keepFor` is where a backend's own view drops it.
  | .only _ body => blockTextList acc body.toList
  | .nav _ body => blockTextList acc body.toList
  | .note body => blockTextList acc body.toList
  | .verbatim _ s spec => acc ++ spec.capText ++ s
  -- Content and comment count; generated keywords never do (algorithm_text).
  | .algorithm _ _ lines => algLineText acc lines.toList
  | .logo content => acc ++ plainText content
  | .frame title _ _ _ body => blockTextList (acc ++ plainText title) body.toList
  | .framefoot content => acc ++ plainText content
  -- A stateful declaration ships no text of its own.
  | .setPalette _ => acc
  | .setTokens _ => acc
  | .pagebreak => acc
  -- A rule is decorative ink; it carries no text.
  | .rule _ _ _ => acc
  -- A picture's labels are diagram ink, not running text: they reach the
  -- shipped-page census through the label runs layout sets, and the census
  -- rows assert them there.
  | .picture _ => acc
  -- Every cell's text is census content — the conservation the user reads
  -- as "no cell silently vanished". The caption counts with its float,
  -- before the body, as a frame's title does.
  | .table _ _ _ rows _ _ => blockTextTableRows acc rows.toList
  | .float _ _ _ body caption => blockTextList (acc ++ plainText caption) body.toList
  -- Every entry's text is census content, in list order.
  | .bibliography _ _ items => blockTextBibItems acc items.toList

@[expose] public def blockTextBibItems (acc : String) : List BibItem → String
  | [] => acc
  | item :: rest => blockTextBibItems (acc ++ plainText item.content) rest

@[expose] public def blockTextTableRows (acc : String) : List (Array (Array Inline)) → String
  | [] => acc
  | row :: rest => blockTextTableRows (blockTextTableCells acc row.toList) rest

@[expose] public def blockTextTableCells (acc : String) : List (Array Inline) → String
  | [] => acc
  | cell :: rest => blockTextTableCells (acc ++ plainText cell) rest

@[expose] public def blockTextItems (acc : String) : List (Array Block) → String
  | [] => acc
  | item :: rest => blockTextItems (blockTextList acc item.toList) rest

@[expose] public def blockTextColumns (acc : String) : List (BoxWidth × Array Block) → String
  | [] => acc
  | (_, body) :: rest => blockTextColumns (blockTextList acc body.toList) rest

end

public theorem blockTextList_append (a b : List Block) (acc : String) :
    blockTextList acc (a ++ b) = blockTextList (blockTextList acc a) b := by
  induction a generalizing acc with
  | nil => simp [blockTextList]
  | cons x xs ih => simp [blockTextList, ih]

/-- Blocks are content-free furniture: a titled block's census is its
title's text then its body's, onto whatever came before — the bar and the
background ship no characters. Definitional (`rfl`), the frame arm's own
shape, so an edit that made the furniture ship text fails this build. -/
public theorem titled_text (acc : String) (kind : TitledKind) (title : Array Inline)
    (body : Array Block) :
    blockTextOne acc (.titled kind title body)
      = blockTextList (acc ++ plainText title) body.toList := by rfl

/-- A declared vertical skip standing on its own, as `\vskip` does: glue
the next placed line pays, no content. -/
private def gapBlock (g : Dim.SymGlue) : Block := .spaced (Sourced.bare g) #[]

/-- A declared bar with the skips beside it; no declared weight, no ink. -/
private def barSide (ink : Color × Option String)
    (before after : Dim.SymGlue) : Option Dim.SymGlue → Array Block
  | some w => #[gapBlock before, .rule ink.1 ink.2 (Sourced.bare w), gapBlock after]
  | none => #[]

/-- One title bracketed by its declared bars, appended to the walk's
accumulator: the furniture above, the heading itself — a sibling, never
wrapped, so the centred walk still meets it — and the furniture below.
The gaps beside each bar are the engine's rhythm (`titleBarGap` to the
type, `titleBarSkip` outside) where the document declares none: the
venue contributes the bars' weights, the engine where they sit. -/
private def titleStep (st : ElementStyle) (ink : Color × Option String)
    (out : Array Block) (starred : Bool) (num : Option String)
    (title : Array Inline) : Array Block :=
  let above := barSide ink (st.ruleAboveSkip.getD titleBarSkip)
    (st.ruleAboveGap.getD titleBarGap) st.ruleAbove
  let below := barSide ink (st.ruleBelowGap.getD titleBarGap)
    (st.ruleBelowSkip.getD titleBarSkip) st.ruleBelow
  ((out ++ above).push (.section 0 starred num title)) ++ below

/-- Bracket a title block's level-0 heading with its declared bars: a
full-measure rule above and below at the declared weights, each standing
its gap from the type — the engine's rhythm (`titleBarGap`,
`titleBarSkip`) unless the document declares its own — the
NeurIPS-lineage title bars (`\@toptitlebar`/`\@bottomtitlebar` read for
the weights they declare, or a document's own
`\style{titlepage}{ rule-above = ... }`). Top level only,
deliberately: the title is the block `Elab.titleBlocks` pushes at the top
of the title block, and descending would let a nested heading take the
venue's furniture. Bars and skips are siblings of the heading, never
wrappers, so the centred walk still meets the heading itself; a gap is
emitted only beside its own bar, and a trailing skip with nothing after it
is no ink. The bars are decorative ink in the ink colour: `titleBars_text`
is the census statement that styling changes no content. -/
public def titleBarsList (st : ElementStyle) (ink : Color × Option String)
    (out : Array Block) (done : Bool) : List Block → Array Block
  | [] => out
  | b :: rest =>
    match b, done with
    | .section 0 starred num title, false =>
      titleBarsList st ink (titleStep st ink out starred num title) true rest
    | b, _ => titleBarsList st ink (out.push b) done rest

public def titleBars (st : ElementStyle) (ink : Color × Option String)
    (blocks : Array Block) : Array Block :=
  if st.ruleAbove.isNone && st.ruleBelow.isNone then blocks
  else titleBarsList st ink #[] false blocks.toList

private theorem blocksText_push (out : Array Block) (b : Block) :
    blocksText (out.push b) = blockTextOne (blocksText out) b := by
  simp [blocksText, Array.toList_push, blockTextList_append, blockTextList]

/-- The in-paragraph role is a name for the page's spacing, never text:
marking a list or a quote ships exactly the census it had. -/
public theorem inParagraph_text (acc : String) (b : Block) :
    blockTextOne acc (inParagraph b) = blockTextOne acc b := by
  unfold inParagraph
  cases b.partopsepEnv <;> simp [blockTextOne, blockTextList]

/-- Marking the environment an arm pushed keeps the sequence's census:
the one rewrite `markInParagraph` makes is `inParagraph_text`'s. -/
public theorem markInParagraph_text (inPar : Bool) (k : Nat) :
    Conserves blocksText (markInParagraph inPar k) := fun xs => by
  unfold markInParagraph
  split
  · next b _ hb =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    rw [Array.pop_push, blocksText_push, blocksText_push, inParagraph_text]
  · rfl
  · rfl

/-- A display's context is a name for its placement, never text: the
display it wraps ships the census the wrapper does. -/
private theorem displayCtxOf_text (acc : String) (b : Block) :
    blockTextOne acc (displayCtxOf b).2 = blockTextOne acc b := by
  unfold displayCtxOf
  split
  · split
    · next hd => simp [blockTextOne, hd, blockTextList]
    · rfl
  · rfl

/-- Marking a display keeps the sequence's census: whatever context it
records, the block pushed is the display itself or that display in a role. -/
public theorem markDisplay_text (inPar parEnd afterEnv : Bool) (k : Nat) :
    Conserves blocksText (markDisplay inPar parEnd afterEnv k) := fun xs => by
  unfold markDisplay
  split
  · next b _ hb =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    dsimp only
    split
    · rfl
    · rw [Array.pop_push, blocksText_push, blocksText_push]
      split <;> simp [blockTextOne, blockTextList, displayCtxOf_text]
  · rfl

private theorem blocksText_append_barSide (out : Array Block)
    (ink : Color × Option String) (before after : Dim.SymGlue)
    (w : Option Dim.SymGlue) :
    blocksText (out ++ barSide ink before after w) = blocksText out := by
  cases w <;>
    simp [barSide, gapBlock, blocksText, blockTextList_append, blockTextList,
      blockTextOne]

private theorem blocksText_titleStep (st : ElementStyle)
    (ink : Color × Option String) (out : Array Block) (starred : Bool)
    (num : Option String) (title : Array Inline) :
    blocksText (titleStep st ink out starred num title) =
      blocksText out ++ plainText title := by
  simp only [titleStep]
  rw [blocksText_append_barSide, blocksText_push, blocksText_append_barSide]
  simp [blockTextOne]

private theorem titleBarsList_text (st : ElementStyle) (ink : Color × Option String)
    (out : Array Block) (done : Bool) (l : List Block) :
    blocksText (titleBarsList st ink out done l) =
      blockTextList (blocksText out) l := by
  fun_induction titleBarsList st ink out done l <;>
    simp_all only [blockTextList, blocksText_push, blocksText_titleStep,
      blockTextOne]

/-- Styling never changes content: the bars are decorative ink, so the
title block's plain-text census under the styled built-in equals the
unstyled built-in's — the conservation the user reads as "the venue's
furniture added nothing and lost nothing". -/
public theorem titleBars_text (st : ElementStyle) (ink : Color × Option String) :
    Conserves blocksText (titleBars st ink) := by
  intro xs
  unfold titleBars
  split
  · rfl
  · rw [titleBarsList_text]
    simp [blocksText, blockTextList]

mutual

/-- Every `.section` level in document order: the document's heading
outline, the fact the outline diagnostics and the markdown preamble read.
A frame's body is walked (a deck's title heading stands inside the title
frame); a note is a side channel and never ships a heading. The
accumulator threads through, as every walk here does. -/
@[expose] public def headingLevels (xs : Array Block) : Array HeadingLevel := headingLevelList #[] xs.toList

@[expose] public def headingLevelList (out : Array HeadingLevel) : List Block → Array HeadingLevel
  | [] => out
  | b :: rest => headingLevelList (headingLevelOne out b) rest

@[expose] public def headingLevelOne (out : Array HeadingLevel) : Block → Array HeadingLevel
  | .section level _ _ _ => out.push level
  | .para _ => out
  | .equation _ _ => out
  | .list _ items => headingLevelItems out items.toList
  | .center body => headingLevelList out body.toList
  | .ragged _ body => headingLevelList out body.toList
  | .quote body => headingLevelList out body.toList
  | .abstract body => headingLevelList out body.toList
  | .titled _ _ body => headingLevelList out body.toList
  | .role _ body => headingLevelList out body.toList
  | .link _ body => headingLevelList out body.toList
  | .spaced _ body => headingLevelList out body.toList
  | .columns cols => headingLevelColumns out cols.toList
  | .onSteps _ body => headingLevelList out body.toList
  | .altSteps _ firstPage otherPage =>
    headingLevelList (headingLevelList out firstPage.toList) otherPage.toList
  | .only _ body => headingLevelList out body.toList
  | .nav _ body => headingLevelList out body.toList
  | .frame _ _ _ _ body => headingLevelList out body.toList
  | .note _ => out
  | .verbatim _ _ _ => out
  -- Lines hold inline content; no heading can stand in an algorithm.
  | .algorithm _ _ _ => out
  | .framefoot _ => out
  | .setPalette _ => out
  | .setTokens _ => out
  | .pagebreak => out
  | .logo _ => out
  | .rule _ _ _ => out
  | .picture _ => out
  -- Cells and captions hold inline content; no heading can stand in either.
  | .table _ _ _ _ _ _ => out
  | .float _ _ _ body _ => headingLevelList out body.toList
  -- The References heading is its own .section block; the list holds none.
  | .bibliography _ _ _ => out

@[expose] public def headingLevelItems (out : Array HeadingLevel) : List (Array Block) → Array HeadingLevel
  | [] => out
  | item :: rest => headingLevelItems (headingLevelList out item.toList) rest

@[expose] public def headingLevelColumns (out : Array HeadingLevel) : List (BoxWidth × Array Block) → Array HeadingLevel
  | [] => out
  | (_, body) :: rest => headingLevelColumns (headingLevelList out body.toList) rest

end

/-- Mutually exclusive readings share equal occurrences. Multiset difference
preserves repeated occurrences within either reading, unlike global deduplication.
The order is the first reading followed by the other reading's extra occurrences. -/
public def exclusiveOccurrences {α : Type u} [BEq α] (first other : Array α) : Array α :=
  first ++ (first.toList.foldl List.erase other.toList).toArray

private theorem eraseOccurrences_exact {α : Type u} [BEq α] [LawfulBEq α]
    (x : α) (first other : List α) :
    (first.foldl List.erase other).count x = other.count x - first.count x := by
  induction first generalizing other with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih, List.count_erase, List.count_cons]
    omega

/-- Exclusive readings preserve the larger multiplicity of every element:
shared occurrences appear once, and authored repeats in either arm survive. -/
public theorem exclusiveOccurrences_exact {α : Type u} [BEq α] [LawfulBEq α]
    (x : α) (first other : Array α) :
    (exclusiveOccurrences first other).toList.count x =
      max (first.toList.count x) (other.toList.count x) := by
  simp only [exclusiveOccurrences, Array.toList_append, List.count_append,
    eraseOccurrences_exact]
  omega

mutual

/-- Every footnote in document order, with its resolved mark number: equal
occurrences in mutually exclusive alternatives share one endnote. This is the
one flow the backends' endnote sections read (the HTML `doc-endnotes`
section, the markdown `[^k]` definitions). The accumulator threads
through, as every walk here does. -/
-- conserves: none — a projection of the notes alone: nothing is rewritten,
-- and the census the notes owe is `footnoteWrap_text` at the wrap site.
public def footnotesOf (xs : Array Block) : Array (Option Nat × Array Inline) :=
  footnoteBlockList #[] xs.toList

private def footnoteBlockList (out : Array (Option Nat × Array Inline)) :
    List Block → Array (Option Nat × Array Inline)
  | [] => out
  | b :: rest => footnoteBlockList (footnoteBlockOne out b) rest

private def footnoteBlockOne (out : Array (Option Nat × Array Inline)) :
    Block → Array (Option Nat × Array Inline)
  | .para content => footnoteInlineList out content.toList
  | .equation number content =>
    footnoteInlineList (footnoteInlineList out content.toList) number.toList
  | .section _ _ _ title => footnoteInlineList out title.toList
  | .list _ items => footnoteItems out items.toList
  | .center body => footnoteBlockList out body.toList
  | .ragged _ body => footnoteBlockList out body.toList
  | .quote body => footnoteBlockList out body.toList
  | .abstract body => footnoteBlockList out body.toList
  | .titled _ title body =>
    footnoteBlockList (footnoteInlineList out title.toList) body.toList
  | .role _ body => footnoteBlockList out body.toList
  | .link _ body => footnoteBlockList out body.toList
  | .spaced _ body => footnoteBlockList out body.toList
  | .columns cols => footnoteColumns out cols.toList
  | .onSteps _ body => footnoteBlockList out body.toList
  | .altSteps _ firstPage otherPage =>
    out ++ exclusiveOccurrences (footnoteBlockList #[] firstPage.toList)
      (footnoteBlockList #[] otherPage.toList)
  | .only _ body => footnoteBlockList out body.toList
  | .nav _ body => footnoteBlockList out body.toList
  | .frame title _ _ _ body =>
    footnoteBlockList (footnoteInlineList out title.toList) body.toList
  -- a speaker note is a side channel; its text never ships on a page
  | .note _ => out
  | .verbatim _ _ _ => out
  | .framefoot _ => out
  | .setPalette _ => out
  | .setTokens _ => out
  | .pagebreak => out
  | .logo _ => out
  | .rule _ _ _ => out
  | .picture _ => out
  | .table _ _ _ rows _ _ => footnoteTableRows out rows.toList
  | .algorithm _ _ lines => footnoteAlgLines out lines.toList
  -- the caption counts with its float, before the body, as its text does
  | .float _ _ _ body caption =>
    footnoteBlockList (footnoteInlineList out caption.toList) body.toList
  | .bibliography _ _ _ => out

private def footnoteTableRows (out : Array (Option Nat × Array Inline)) :
    List (Array (Array Inline)) → Array (Option Nat × Array Inline)
  | [] => out
  | row :: rest => footnoteTableRows (footnoteTableCells out row.toList) rest

private def footnoteTableCells (out : Array (Option Nat × Array Inline)) :
    List (Array Inline) → Array (Option Nat × Array Inline)
  | [] => out
  | cell :: rest => footnoteTableCells (footnoteInlineList out cell.toList) rest

private def footnoteItems (out : Array (Option Nat × Array Inline)) :
    List (Array Block) → Array (Option Nat × Array Inline)
  | [] => out
  | item :: rest => footnoteItems (footnoteBlockList out item.toList) rest

private def footnoteColumns (out : Array (Option Nat × Array Inline)) :
    List (BoxWidth × Array Block) → Array (Option Nat × Array Inline)
  | [] => out
  | (_, body) :: rest => footnoteColumns (footnoteBlockList out body.toList) rest

private def footnoteAlgLines (out : Array (Option Nat × Array Inline)) :
    List AlgLine → Array (Option Nat × Array Inline)
  | [] => out
  | l :: rest =>
    footnoteAlgLines (match l.comment with
      | some c => footnoteInlineList (footnoteInlineList out l.content.toList) c.toList
      | none => footnoteInlineList out l.content.toList) rest

private def footnoteInlineList (out : Array (Option Nat × Array Inline)) :
    List Inline → Array (Option Nat × Array Inline)
  | [] => out
  | x :: rest => footnoteInlineList (footnoteInlineOne out x) rest

private def footnoteInlineOne (out : Array (Option Nat × Array Inline)) :
    Inline → Array (Option Nat × Array Inline)
  | .footnote num body =>
    -- flow order: a note nested in another note's body follows its host
    footnoteInlineList (out.push (num, body)) body.toList
  | .styled _ body => footnoteInlineList out body.toList
  | .colored _ _ body => footnoteInlineList out body.toList
  | .located _ body => footnoteInlineList out body.toList
  | .role _ body => footnoteInlineList out body.toList
  | .link _ body => footnoteInlineList out body.toList
  | .decorated _ body => footnoteInlineList out body.toList
  | .onSteps _ body => footnoteInlineList out body.toList
  | .altSteps _ firstPage otherPage =>
    out ++ exclusiveOccurrences (footnoteInlineList #[] firstPage.toList)
      (footnoteInlineList #[] otherPage.toList)
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ => out

end

/-- A heading level in the author's own vocabulary. -/
private def levelName : HeadingLevel → String
  | .title => "the title"
  | .h1 => "a rank-one heading"
  | .h2 => "a rank-two heading"
  | .h3 => "a rank-three heading"
  | .h4 => "a rank-four heading"
  | .h5 => "a rank-five heading"
  | .h6 => "a rank-six heading"

/-- The broken-outline diagnostic W0320 fires: named so the completeness
theorem below can point at the pushed value's code. -/
private def outlineGapDiag (p l : HeadingLevel) : Diag :=
  Diag.of .W0320
    s!"heading levels skip a step: {levelName p} is followed by {levelName l}"
    (help := some "descend one rank at a time: 1, 2, 3, 4, 5, 6; \
add the missing heading or promote the deeper one (HTML §4.3.11, WCAG G141)")

private def outlineTitleDiag : Diag :=
  Diag.of .W0321
    "the document title follows another heading"
    (help := some "put \\maketitle before the first \\section, so the \
outline starts at its top")

/-- The outline walk over the heading levels, `prev` the level just read:
each element is judged against its lead — the gap first, then the
misplaced title — with one latch per code, so each fires once per
document, in encounter order. Recursion over the `List` with a threaded
accumulator, so `headings_no_skip_judged` can reason by induction where
the imperative loop this replaces could not. -/
private def outlineWalk (prev : HeadingLevel) (gapNamed titleNamed : Bool)
    (out : Array Diag) : List HeadingLevel → Array Diag
  | [] => out
  | l :: rest =>
    if headingRank l > headingRank prev + 1 && !gapNamed then
      if l == 0 && !titleNamed then
        outlineWalk l true true
          ((out.push (outlineGapDiag prev l)).push outlineTitleDiag) rest
      else
        outlineWalk l true titleNamed (out.push (outlineGapDiag prev l)) rest
    else
      if l == 0 && !titleNamed then
        outlineWalk l gapNamed true (out.push outlineTitleDiag) rest
      else
        outlineWalk l gapNamed titleNamed out rest

/-- Somewhere after a heading at `prev`, a heading exceeds its lead by
more than one level: the broken-outline fact `outlineWalk` judges. -/
private def outlineSkips (prev : HeadingLevel) : List HeadingLevel → Bool
  | [] => false
  | l :: rest => headingRank l > headingRank prev + 1 || outlineSkips l rest

/-- The document's outline skips a level: the fact W0320 exists to name
(HTML §4.3.11; WCAG technique G141). -/
public def outlineHasSkip (doc : Doc) : Bool :=
  match (headingLevels doc.body).toList with
  | [] => false
  | l :: rest => outlineSkips l rest

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
public def outlineDiags (doc : Doc) : Array Diag :=
  match (headingLevels doc.body).toList with
  | [] => #[]
  | l :: rest => outlineWalk l false false #[] rest

/-- A diagnostic already collected survives the rest of the walk. -/
private theorem outlineWalk_mem (d : Diag) :
    ∀ (ls : List HeadingLevel) (prev : HeadingLevel) (gN tN : Bool) (out : Array Diag),
      d ∈ out → d ∈ outlineWalk prev gN tN out ls
  | [], _, _, _, _, h => h
  | _ :: rest, _, _, _, _, h => by
    unfold outlineWalk
    split <;> split <;>
      exact outlineWalk_mem d rest _ _ _ _ (by
        first
        | exact h
        | exact Array.mem_push.mpr (Or.inl h)
        | exact Array.mem_push.mpr (Or.inl (Array.mem_push.mpr (Or.inl h))))

private theorem outlineWalk_finds :
    ∀ (ls : List HeadingLevel) (prev : HeadingLevel) (tN : Bool) (out : Array Diag),
      outlineSkips prev ls = true →
      ∃ d ∈ outlineWalk prev false tN out ls, d.code = "W0320"
  | l :: rest, prev, tN, out, hskip => by
    unfold outlineWalk
    by_cases hgap : headingRank l > headingRank prev + 1
    · refine ⟨outlineGapDiag prev l, ?_, by
        unfold outlineGapDiag
        rw [Diag.of_code_exact]
        exact DiagCode.w0320_code_exact⟩
      simp only [hgap, decide_true, Bool.not_false, Bool.and_true, ite_true]
      split <;>
        exact outlineWalk_mem _ rest _ _ _ _ (by simp [Array.mem_push])
    · have hrest : outlineSkips l rest = true := by
        unfold outlineSkips at hskip
        simpa [hgap] using hskip
      simp only [hgap, decide_false, Bool.false_and, Bool.false_eq_true,
        ite_false]
      split
      · exact outlineWalk_finds rest l true _ hrest
      · exact outlineWalk_finds rest l tN out hrest

/-- The heading-structure judge is complete: a document whose outline
skips a level (a heading more than one level deeper than its lead —
`outlineHasSkip`, the fact HTML §4.3.11's conformance rule and WCAG
technique G141 both state) always ships a W0320 among its outline
diagnostics. Weak heading structure is then a reported fact, never a
reader's discovery: the theorem closes the gap between "the judge
exists" and "no document escapes it". -/
public theorem headings_no_skip_judged (doc : Doc)
    (h : outlineHasSkip doc = true) :
    ∃ d ∈ outlineDiags doc, d.code = "W0320" := by
  unfold outlineHasSkip at h
  unfold outlineDiags
  split at h
  · exact absurd h (by simp)
  · exact outlineWalk_finds _ _ false #[] h

/-- Is this node a physical-page placeholder (`\pagenumber` /
`\pagecount`)? The physical sequence's only spellings — what
`Layout.substPage` resolves, and what the frame sequence must never be
mixed with silently (`footerSequenceDiags`). The descent that carries the
question over content is the fold's, declared once (`hasPhysicalPage`);
this leaf answers for one node, and any constructor that is not one of
the two spellings is not a placeholder. -/
@[expose] public def isPhysicalPage : Inline → Bool
  | .pageNumber => true
  | .pageCount => true
  | _ => false

/-- Does this inline content carry a physical-page placeholder anywhere?
`anyInline` over the one leaf predicate. -/
@[expose] public def hasPhysicalPage (xs : Array Inline) : Bool :=
  anyInline isPhysicalPage xs

/-- Is this slot the frame sequence's? The counting model keeps two distinct
sequences: the frame numbering (`Ir.frameNumbers`, rendered only by
`ChromeSlot.render`) and the physical pages (`\pagenumber`/`\pagecount`,
rendered only by `Layout.substPage`) — a stepped frame advances one and not
the other. -/
public def ChromeSlot.isFrameSequence : ChromeSlot → Bool
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
public def footerSequenceDiags (doc : Doc) : Array Diag := Id.run do
  unless doc.docClass.record.chrome && doc.foot.isNone && !doc.chromeDeclared do
    return #[]
  let frameSlot := (doc.chrome.footerLeft.map ChromeSlot.isFrameSequence).getD false
    || (doc.chrome.footerRight.map ChromeSlot.isFrameSequence).getD false
  unless frameSlot do return #[]
  let mut out : Array Diag := #[]
  for b in doc.body do
    if let .framefoot xs := b then
      if hasPhysicalPage xs && out.isEmpty then
        out := out.push (Diag.of .W0332
          "the footer mixes the physical page number with the frame number; \
a stepped frame advances one and not the other"
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
public theorem frame_sequence_carries_no_physical (s : ChromeSlot)
    (sec : Array Inline) (n total : Nat) (hs : s.isFrameSequence = true) :
    hasPhysicalPage (s.render sec n total) = false := by
  cases s with
  | sectionTitle => simp [ChromeSlot.isFrameSequence] at hs
  | frameNumber =>
    simp [ChromeSlot.render, hasPhysicalPage, anyInline, foldInlines,
      foldInlineList, foldInline, isPhysicalPage]
  | frameFraction =>
    simp [ChromeSlot.render, hasPhysicalPage, anyInline, foldInlines,
      foldInlineList, foldInline, isPhysicalPage]

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

private theorem algLineText_chain (l1 l2 : List AlgLine) (acc : String) :
    algLineText acc (l1 ++ l2) = algLineText (algLineText acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [algLineText]
  | cons l rest ih => cases hc : l.comment <;> simp [algLineText, hc, ih]

private theorem blockTextItems_chain (l1 l2 : List (Array Block)) (acc : String) :
    blockTextItems acc (l1 ++ l2) = blockTextItems (blockTextItems acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextItems]
  | cons item rest ih => simp [blockTextItems, ih]

private theorem blockTextColumns_chain (l1 l2 : List (BoxWidth × Array Block))
    (acc : String) :
    blockTextColumns acc (l1 ++ l2)
      = blockTextColumns (blockTextColumns acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextColumns]
  | cons col rest ih => simp [blockTextColumns, ih]

private theorem blockTextTableRows_chain (l1 l2 : List (Array (Array Inline)))
    (acc : String) :
    blockTextTableRows acc (l1 ++ l2)
      = blockTextTableRows (blockTextTableRows acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextTableRows]
  | cons row rest ih => simp [blockTextTableRows, ih]

private theorem blockTextTableCells_chain (l1 l2 : List (Array Inline))
    (acc : String) :
    blockTextTableCells acc (l1 ++ l2)
      = blockTextTableCells (blockTextTableCells acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextTableCells]
  | cons cell rest ih => simp [blockTextTableCells, ih]

mutual

private theorem dimInlineList_text (cover : Cover) (k : Nat) (pending : Bool)
    (xs : List Inline) (out : Array Inline) :
    plainTextList (dimInlineList cover k pending out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [dimInlineList, plainTextList]
  | x :: rest =>
    rw [dimInlineList, dimInlineList_text cover k pending rest]
    simp [plainTextList, plainTextList_append, dimInline_text cover k pending x,
      String.append_assoc]

private theorem dimInline_text (cover : Cover) (k : Nat) (pending : Bool) (x : Inline) :
    plainTextOne (dimInline cover k pending x) = plainTextOne x := by
  match x with
  | .styled st body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k pending body.toList #[], plainTextList]
  | .footnote n body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k pending body.toList #[], plainTextList]
  | .colored c nm body =>
    rw [dimInline]
    by_cases h : pending = true
    · simp [h, plainTextOne, dimInlineList_text cover k true body.toList #[], plainTextList]
    · simp [h, plainTextOne, dimInlineList_text cover k false body.toList #[], plainTextList]
  | .located n body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k pending body.toList #[], plainTextList]
  | .role n body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k pending body.toList #[], plainTextList]
  | .link u body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k pending body.toList #[], plainTextList]
  | .decorated kind body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k pending body.toList #[], plainTextList]
  | .onSteps spec body =>
    rw [dimInline]
    by_cases h : (!pending && spec.pending k) = true
    · simp [h, plainTextOne, plainTextList,
        dimInlineList_text cover k true body.toList #[]]
    · simp [h, plainTextOne, dimInlineList_text cover k pending body.toList #[],
        plainTextList]
  | .altSteps spec firstPage otherPage =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k pending firstPage.toList #[],
      dimInlineList_text cover k pending otherPage.toList #[], plainTextList]
  | .image _ _ _ =>
    -- the walk leaves an image node whole (raster content dims in the
    -- backends' hands), and its text census is empty either way
    rfl
  | .formula _ _ _ =>
    -- the walk leaves a formula node whole (a pending formula dims in the
    -- backends' hands); its census is its source, untouched on both sides
    rfl
  | .text _ | .math _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _
  | .label _ | .ref _ _ _ _
  | .icon _ _ | .cite _ _ =>
    rfl

end

/-- A covered or dimmed line keeps every character, comment included: the
cover's wrapper recolours, as a paragraph's does. -/
private theorem dimAlgLines_text (cover : Cover) (k : Nat) (pending : Bool)
    (ls : List AlgLine) (out : Array AlgLine) (acc : String) :
    algLineText acc (dimAlgLines cover k pending out ls).toList
      = algLineText (algLineText acc out.toList) ls := by
  match ls with
  | [] => simp [dimAlgLines, algLineText]
  | l :: rest =>
    rw [dimAlgLines, dimAlgLines_text cover k pending rest]
    rw [Array.toList_push, algLineText_chain]
    by_cases h : pending = true
    · cases hc : l.comment with
      | none =>
        by_cases he : l.content.isEmpty
        · simp [h, hc, he, algLineText]
        · simp [h, hc, he, algLineText, plainText, plainTextList, plainTextOne,
            dimInlineList_text cover k true l.content.toList #[]]
      | some c =>
        by_cases he : l.content.isEmpty
        · by_cases hce : c.isEmpty
          · simp [h, hc, he, hce, algLineText]
          · simp [h, hc, he, hce, algLineText, plainText, plainTextList,
              plainTextOne, dimInlineList_text cover k true c.toList #[]]
        · by_cases hce : c.isEmpty
          · simp [h, hc, he, hce, algLineText, plainText, plainTextList,
              plainTextOne, dimInlineList_text cover k true l.content.toList #[]]
          · simp [h, hc, he, hce, algLineText, plainText, plainTextList,
              plainTextOne, dimInlineList_text cover k true l.content.toList #[],
              dimInlineList_text cover k true c.toList #[]]
    · cases hc : l.comment with
      | none =>
        simp [h, hc, algLineText, plainText, plainTextList,
          dimInlineList_text cover k false l.content.toList #[]]
      | some c =>
        simp [h, hc, algLineText, plainText, plainTextList,
          dimInlineList_text cover k false l.content.toList #[],
          dimInlineList_text cover k false c.toList #[]]

/-- A covered or dimmed cell keeps every character: the cover's cell wrapper
recolours, as a paragraph's does. -/
private theorem dimTableCells_text (cover : Cover) (k : Nat) (pending : Bool)
    (cells : List (Array Inline))
    (out : Array (Array Inline)) (acc : String) :
    blockTextTableCells acc (dimTableCells cover k pending out cells).toList
      = blockTextTableCells (blockTextTableCells acc out.toList) cells := by
  match cells with
  | [] => simp [dimTableCells, blockTextTableCells]
  | cell :: rest =>
    rw [dimTableCells, dimTableCells_text cover k pending rest _ acc]
    by_cases h : pending = true
    · by_cases hc : cell.isEmpty
      · simp [h, hc, blockTextTableCells, blockTextTableCells_chain]
      · simp [h, hc, blockTextTableCells, blockTextTableCells_chain, plainText,
          plainTextList, plainTextOne, dimInlineList_text cover k true cell.toList #[]]
    · simp [h, blockTextTableCells, blockTextTableCells_chain, plainText,
        dimInlineList_text cover k false cell.toList #[], plainTextList]

private theorem dimTableRows_text (cover : Cover) (k : Nat) (pending : Bool)
    (rows : List (Array (Array Inline)))
    (out : Array (Array (Array Inline))) (acc : String) :
    blockTextTableRows acc (dimTableRows cover k pending out rows).toList
      = blockTextTableRows (blockTextTableRows acc out.toList) rows := by
  match rows with
  | [] => simp [dimTableRows, blockTextTableRows]
  | row :: rest =>
    rw [dimTableRows, dimTableRows_text cover k pending rest _ acc]
    simp [blockTextTableRows, blockTextTableRows_chain,
      dimTableCells_text cover k pending row.toList #[], blockTextTableCells]

mutual

private theorem dimBlockList_text (cover : Cover) (k : Nat) (pending : Bool)
    (xs : List Block) (out : Array Block) (acc : String) :
    blockTextList acc (dimBlockList cover k pending out xs).toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [dimBlockList, blockTextList]
  | b :: rest =>
    rw [dimBlockList, dimBlockList_text cover k pending rest]
    simp [blockTextList, blockTextList_chain, dimBlock_text cover k pending b]

private theorem dimBlock_text (cover : Cover) (k : Nat) (pending : Bool) (b : Block)
    (acc : String) :
    blockTextOne acc (dimBlock cover k pending b) = blockTextOne acc b := by
  match b with
  | .para content =>
    rw [dimBlock]
    by_cases h : pending = true
    · simp [h, blockTextOne, plainText, plainTextList, plainTextOne,
        dimInlineList_text cover k true content.toList #[]]
    · simp [h, blockTextOne, plainText,
        dimInlineList_text cover k false content.toList #[], plainTextList]
  | .equation num content =>
    rw [dimBlock]
    by_cases h : pending = true
    · simp [h, blockTextOne, plainText, plainTextList, plainTextOne,
        dimInlineList_text cover k true content.toList #[]]
    · simp [h, blockTextOne, plainText,
        dimInlineList_text cover k false content.toList #[], plainTextList]
  | .list o items =>
    rw [dimBlock]
    simp [blockTextOne, dimItems_text cover k pending items.toList #[] acc, blockTextItems]
  | .center body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending body.toList #[] acc, blockTextList]
  | .ragged _ body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending body.toList #[] acc, blockTextList]
  | .quote body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending body.toList #[] acc, blockTextList]
  | .abstract body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending body.toList #[] acc, blockTextList]
  | .titled kind title body =>
    rw [dimBlock]
    simp [blockTextOne, plainText,
      dimInlineList_text cover k pending title.toList #[], plainTextList,
      dimBlockList_text cover k pending body.toList #[] _, blockTextList]
  | .role n body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending body.toList #[] acc, blockTextList]
  | .link target body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending body.toList #[] acc, blockTextList]
  | .spaced g body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending body.toList #[] acc, blockTextList]
  | .columns cols =>
    rw [dimBlock]
    simp [blockTextOne, dimColumns_text cover k pending cols.toList #[] acc, blockTextColumns]
  | .onSteps spec body =>
    -- No case split: the mode flip is just the argument the recursion takes.
    rw [dimBlock]
    simp [blockTextOne,
      dimBlockList_text cover k (pending || spec.pending k) body.toList #[] acc,
      blockTextList]
  | .altSteps spec firstPage otherPage =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending firstPage.toList #[],
      dimBlockList_text cover k pending otherPage.toList #[], blockTextList]
  | .only targets body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending body.toList #[] acc, blockTextList]
  | .nav spec body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending body.toList #[] acc, blockTextList]
  -- A logo declaration is page furniture: the walk never repaints it, so
  -- its census — the declaration's own inline text — is untouched. The
  -- verbatim recolour and the picture recolour keep their text census by
  -- construction: neither constructor's census reads a colour.
  | .logo _ => rfl
  -- The verbatim body's census reads no colour; the caption dims as a
  -- float's does, and dimming conserves its text.
  | .verbatim c s spec =>
    rw [dimBlock]
    cases hc : spec.caption with
    | none => simp [blockTextOne, ListingSpec.capText, hc]
    | some p =>
      simp [blockTextOne, ListingSpec.capText, hc, plainText, plainTextList,
        dimInlineList_text cover k pending p.2.toList #[]]
  | .section _ _ _ _ | .note _ | .frame _ _ _ _ _ | .framefoot _
  | .setPalette _ | .setTokens _
  | .rule _ _ _ | .picture _ | .pagebreak | .bibliography _ _ _ => rfl
  | .algorithm n sm lines =>
    rw [dimBlock]
    show algLineText acc (dimAlgLines cover k pending #[] lines.toList).toList = _
    rw [dimAlgLines_text cover k pending lines.toList #[] acc]
    rfl
  | .table cols pl pr rows rules spans =>
    rw [dimBlock]
    simp [blockTextOne, dimTableRows_text cover k pending rows.toList #[] acc,
      blockTextTableRows]
  | .float fk num ca body caption =>
    rw [dimBlock]
    by_cases h : pending = true
    · by_cases hc : caption.isEmpty
      · simp [h, hc, blockTextOne,
          dimBlockList_text cover k true body.toList #[] _, blockTextList]
      · simp [h, hc, blockTextOne, plainText, plainTextList, plainTextOne,
          dimInlineList_text cover k true caption.toList #[],
          dimBlockList_text cover k true body.toList #[] _, blockTextList]
    · simp [h, blockTextOne, plainText,
        dimInlineList_text cover k false caption.toList #[], plainTextList,
        dimBlockList_text cover k false body.toList #[] _, blockTextList]

private theorem dimItems_text (cover : Cover) (k : Nat) (pending : Bool)
    (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (dimItems cover k pending out items).toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [dimItems, blockTextItems]
  | item :: rest =>
    rw [dimItems, dimItems_text cover k pending rest]
    simp [blockTextItems, blockTextItems_chain,
      dimBlockList_text cover k pending item.toList #[], blockTextList]

private theorem dimColumns_text (cover : Cover) (k : Nat) (pending : Bool)
    (cols : List (BoxWidth × Array Block))
    (out : Array (BoxWidth × Array Block)) (acc : String) :
    blockTextColumns acc (dimColumns cover k pending out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [dimColumns, blockTextColumns]
  | (w, body) :: rest =>
    rw [dimColumns, dimColumns_text cover k pending rest]
    simp [blockTextColumns, blockTextColumns_chain,
      dimBlockList_text cover k pending body.toList #[], blockTextList]

end

/-- Nothing vanishes: page `k` of a stepped frame carries every character
the frame carries — dimming recolours pending content, it never hides it,
in either mode of the one walk. The union of what the steps show is
therefore the whole content. -/
public theorem dimBlocks_text (cover : Cover) (k : Nat) :
    Conserves blocksText (dimBlocks cover k) := fun xs => by
  simp [blocksText, dimBlocks, dimBlockList_text cover k false xs.toList #[] "",
    blockTextList]

/-- `algorithm_text`: the algorithm block's census is exactly its lines'
declared content and comments — display flags are settings and the
keywords a kind implies are generated by the backends (`AlgLine.rendered`),
so neither is ever counted, exactly as caption prefixes are not. -/
public theorem algorithm_text (numbered semis : Bool) (lines : Array AlgLine) :
    blocksText #[Block.algorithm numbered semis lines]
      = algLineText "" lines.toList := by rfl

-- The item-step flatten: unwrapping loses no text. A leading `\item<2->`
-- wrapper gives its item its paragraph, nothing recoloured, nothing
-- reordered, so the block census is fixed. Same
-- accumulator-lemma-then-mutual-induction shape as the dim walk above.

private theorem flattenLeadStep_text (item : Array Block) (acc : String) :
    blockTextList acc (flattenLeadStep item).toList
      = blockTextList acc item.toList := by
  unfold flattenLeadStep
  split
  next spec body h =>
    have h0 : item.toList[0]? = some (Block.onSteps spec body) := by simpa using h
    cases wl : item.toList with
    | nil => simp [wl] at h0
    | cons y rest =>
      rw [wl] at h0
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      have hlen : item.size - 1 = rest.length := by
        have h1 := congrArg List.length wl
        simp at h1
        omega
      split
      next p hb =>
        have hb0 : body.toList[0]? = some (Block.para p) := by simpa using hb
        cases wb : body.toList with
        | nil => simp [wb] at hb0
        | cons z more =>
          rw [wb] at hb0
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb0
          subst hb0
          have hblen : body.size - 1 = more.length := by
            have h1 := congrArg List.length wb
            simp at h1
            omega
          by_cases hs : body.size ≤ 1
          · have hm : more = [] := by
              have h1 := congrArg List.length wb
              simp at h1
              cases more with
              | nil => rfl
              | cons _ _ => simp at h1; omega
            subst hm
            simp [hs, wl, wb, hlen, blockTextList, blockTextOne]
          · simp [hs, wl, wb, hlen, hblen, blockTextList, blockTextOne]
      next hb =>
        have hb0 : body.toList = [] := by
          rcases body with ⟨l⟩
          cases l with
          | nil => rfl
          | cons z more => simp at hb
        simp [wl, hb0, hlen, blockTextList, blockTextOne]
      all_goals simp [wl]
  all_goals rfl

mutual

private theorem unwrapItemStepList_text (xs : List Block) (out : Array Block)
    (acc : String) :
    blockTextList acc (unwrapItemStepList out xs).toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [unwrapItemStepList, blockTextList]
  | b :: rest =>
    rw [unwrapItemStepList, unwrapItemStepList_text rest]
    simp [blockTextList, blockTextList_chain, unwrapItemStep_text b]

private theorem unwrapItemStep_text (b : Block) (acc : String) :
    blockTextOne acc (unwrapItemStep b) = blockTextOne acc b := by
  match b with
  | .list o items =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepItems_text items.toList #[] acc,
      blockTextItems]
  | .center body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .ragged _ body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .quote body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .abstract body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .titled kind title body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] _,
      blockTextList]
  | .role n body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .link target body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .spaced g body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .columns cols =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepCols_text cols.toList #[] acc,
      blockTextColumns]
  | .onSteps spec body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .altSteps spec firstPage otherPage =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text firstPage.toList #[],
      unwrapItemStepList_text otherPage.toList #[], blockTextList]
  | .only targets body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .nav spec body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .frame t s v _ body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] _,
      blockTextList]
  | .float k n ca body caption =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] _,
      blockTextList]
  | .para _ | .equation _ _ | .section _ _ _ _ | .verbatim _ _ _ | .note _ | .framefoot _
  | .pagebreak
  | .setPalette _ | .setTokens _ | .algorithm _ _ _
  | .logo _ | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _
  | .bibliography _ _ _ => rfl

private theorem unwrapItemStepItems_text (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (unwrapItemStepItems out items).toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [unwrapItemStepItems, blockTextItems]
  | item :: rest =>
    rw [unwrapItemStepItems, unwrapItemStepItems_text rest]
    simp [blockTextItems, blockTextItems_chain, flattenLeadStep_text,
      unwrapItemStepList_text item.toList #[], blockTextList]

private theorem unwrapItemStepCols_text (cols : List (BoxWidth × Array Block))
    (out : Array (BoxWidth × Array Block)) (acc : String) :
    blockTextColumns acc (unwrapItemStepCols out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [unwrapItemStepCols, blockTextColumns]
  | (w, body) :: rest =>
    rw [unwrapItemStepCols, unwrapItemStepCols_text rest]
    simp [blockTextColumns, blockTextColumns_chain,
      unwrapItemStepList_text body.toList #[], blockTextList]

end

/-- Unwrapping item steps loses no text: the marker pre-pass flattens a
leading `\item<2->` wrapper, it never drops the item's content
(arch-faithful I1). -/
public theorem unwrapItemSteps_text : Conserves blocksText unwrapItemSteps := fun xs => by
  simp [blocksText, unwrapItemSteps, unwrapItemStepList_text xs.toList #[] "",
    blockTextList]

/-- A drawn decoration is never content: the text census
reads straight through the wrap, so `\underline` and `\sout` can neither add
nor hide a character — the conservation half of the decoration convention (its
rules ride a sibling line; `decoration_no_growth` in Layout is the metric
half). -/
public theorem decorated_text (kind : Decoration) :
    Conserves plainText (fun xs => #[Inline.decorated kind xs]) :=
  wrap_text (.decorated kind) fun _ => rfl

-- Float numbering conserves the census: the pass writes the `num` field
-- and nothing else, so no caption and no body content moves. Same
-- accumulator-lemma-then-mutual-induction shape as the walks above.

mutual

private theorem numberFloatList_text (c : FloatCtr) (acc : Array Block)
    (bs : List Block) (s : String) :
    blockTextList s ((numberFloatList c acc bs).2).toList
      = blockTextList (blockTextList s acc.toList) bs := by
  match bs with
  | [] => simp [numberFloatList, blockTextList]
  | b :: rest =>
    show blockTextList s ((numberFloatList (numberFloatOne c b).1
      (acc.push (numberFloatOne c b).2) rest).2).toList = _
    rw [numberFloatList_text (numberFloatOne c b).1
      (acc.push (numberFloatOne c b).2) rest s]
    rw [Array.toList_push, blockTextList_chain]
    simp [blockTextList, numberFloatOne_text c b]

private theorem numberFloatOne_text (c : FloatCtr) (b : Block) (s : String) :
    blockTextOne s (numberFloatOne c b).2 = blockTextOne s b := by
  match b with
  | .para _ | .equation _ _ | .section _ _ _ _ | .note _ | .verbatim _ _ _ | .logo _
  | .bibliography _ _ _ | .algorithm _ _ _
  | .framefoot _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ => rfl
  | .list o items =>
    simp [numberFloatOne, blockTextOne,
      numberFloatItems_text c #[] items.toList, blockTextItems]
  | .center body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .ragged _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .quote body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .abstract body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .titled kind title body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .role _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .link _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .spaced _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .columns cols =>
    simp [numberFloatOne, blockTextOne,
      numberFloatCols_text c #[] cols.toList, blockTextColumns]
  | .onSteps _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .altSteps _ firstPage otherPage =>
    simp [numberFloatOne, blockTextOne, numberFloatList_text, blockTextList]
  | .only _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .nav _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .frame _ _ _ _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .float kind _ capAbove body caption =>
    simp [numberFloatOne, blockTextOne, numberFloatList_text, blockTextList]

private theorem numberFloatItems_text (c : FloatCtr) (acc : Array (Array Block))
    (items : List (Array Block)) (s : String) :
    blockTextItems s ((numberFloatItems c acc items).2).toList
      = blockTextItems (blockTextItems s acc.toList) items := by
  match items with
  | [] => simp [numberFloatItems, blockTextItems]
  | item :: rest =>
    show blockTextItems s ((numberFloatItems (numberFloatList c #[] item.toList).1
      (acc.push (numberFloatList c #[] item.toList).2) rest).2).toList = _
    rw [numberFloatItems_text (numberFloatList c #[] item.toList).1
      (acc.push (numberFloatList c #[] item.toList).2) rest s]
    rw [Array.toList_push, blockTextItems_chain]
    simp [blockTextItems, numberFloatList_text c #[] item.toList, blockTextList]

private theorem numberFloatCols_text (c : FloatCtr)
    (acc : Array (BoxWidth × Array Block))
    (cols : List (BoxWidth × Array Block)) (s : String) :
    blockTextColumns s ((numberFloatCols c acc cols).2).toList
      = blockTextColumns (blockTextColumns s acc.toList) cols := by
  match cols with
  | [] => simp [numberFloatCols, blockTextColumns]
  | (w, body) :: rest =>
    show blockTextColumns s ((numberFloatCols (numberFloatList c #[] body.toList).1
      (acc.push (w, (numberFloatList c #[] body.toList).2)) rest).2).toList = _
    rw [numberFloatCols_text (numberFloatList c #[] body.toList).1
      (acc.push (w, (numberFloatList c #[] body.toList).2)) rest s]
    rw [Array.toList_push, blockTextColumns_chain]
    simp [blockTextColumns, numberFloatList_text c #[] body.toList, blockTextList]

end

/-- Numbering assigns numbers and nothing else: the text census is fixed,
so no caption and no content is touched by the pass — the prefix a backend
sets in front of a caption (`numberedCaption`) is furniture the backend
adds, like a list marker, never a rewrite of the document. -/
public theorem numberFloats_text : Conserves blocksText numberFloats := fun xs => by
  simp [blocksText, numberFloats, numberFloatList_text {} #[] xs.toList "",
    blockTextList]

-- The role-realization walk: recolour role-named runs per ground, rewrite
-- palettes where they stand. Structural recursion through `List`, as the
-- walks above; the palette in force threads through the walk (flow scope:
-- a `.setPalette` inside a body reaches what follows it, exactly as the
-- contrast judge and the layout read it).

/-- The per-run recolour a realization pass applies: the palette in force,
the local ground when one stands (`none` reads the palette's own page),
the run's role name when it has one, and the declared colour; the result
is what ships. `Contrast.realizeDoc` instantiates it with the realization
plan's lookups; the walk decides only *where* each ground stands — the
same places the contrast judge reads (the frame-title bar, a titled
block's bar, the standout inversion, else the page), so a pair the judge
realized is rewritten exactly where it was judged. -/
public abbrev RoleRecolor := Palette → Option Color → Option String → Color → Color

/-- A declaration ends a frame's local ground even when its palette equals
the preceding one. The epoch also prevents frame exit from restoring a
ground whose declaration has been superseded inside the body. -/
private structure RoleRecolorState where
  pal : Palette
  ground : Option Color := none
  epoch : Nat := 0

mutual

public def recolorRolesInlines (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (out : Array Inline) : List Inline → Array Inline
  | [] => out
  | x :: rest =>
    recolorRolesInlines recolor pal ground
      (out.push (recolorRolesInline recolor pal ground x)) rest

private def recolorRolesInline (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) : Inline → Inline
  | .colored c nm body =>
    .colored (recolor pal ground nm c) nm
      (recolorRolesInlines recolor pal ground #[] body.toList)
  | .styled st body => .styled st (recolorRolesInlines recolor pal ground #[] body.toList)
  | .located n body => .located n (recolorRolesInlines recolor pal ground #[] body.toList)
  | .role n body => .role n (recolorRolesInlines recolor pal ground #[] body.toList)
  | .link u body => .link u (recolorRolesInlines recolor pal ground #[] body.toList)
  | .decorated kind body => .decorated kind (recolorRolesInlines recolor pal ground #[] body.toList)
  | .onSteps spec body => .onSteps spec (recolorRolesInlines recolor pal ground #[] body.toList)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (recolorRolesInlines recolor pal ground #[] firstPage.toList)
      (recolorRolesInlines recolor pal ground #[] otherPage.toList)
  | .footnote n body => .footnote n (recolorRolesInlines recolor pal ground #[] body.toList)
  -- A formula's colours are realized as a run's are, on the same ground.
  | .formula d src body => .formula d src (body.mapInk fun c nm => recolor pal ground nm c)
  | .text s => .text s
  | .math d src => .math d src
  | .image src size alt => .image src size alt
  | .icon s l => .icon s l
  | .label k => .label k
  | .ref k p t tg => .ref k p t tg
  | .cite t keys => .cite t keys
  | .fill => .fill
  | .hspace g keep => .hspace g keep
  | .rule w h r => .rule w h r
  | .strut h => .strut h
  | .italicCorr m => .italicCorr m
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak e => .linebreak e


end

mutual

private def recolorRolesList (repal : Palette → Palette) (recolor : RoleRecolor)
    (cx : RoleRecolorState) (out : Array Block) :
    List Block → Array Block × RoleRecolorState
  | [] => (out, cx)
  | b :: rest =>
    let r := recolorRolesBlock repal recolor cx b
    recolorRolesList repal recolor r.2 (out.push r.1) rest

private def recolorRolesBlock (repal : Palette → Palette) (recolor : RoleRecolor)
    (cx : RoleRecolorState) : Block → Block × RoleRecolorState
  | .para content =>
    (.para (recolorRolesInlines recolor cx.pal cx.ground #[] content.toList), cx)
  | .equation num content =>
    (.equation (recolorRolesInlines recolor cx.pal cx.ground #[] num.toList)
      (recolorRolesInlines recolor cx.pal cx.ground #[] content.toList), cx)
  -- A heading's title is judged on the page wherever it stands (the
  -- judge's headingCx carries no local ground); the walk mirrors it.
  | .section l st num title =>
    (.section l st num (recolorRolesInlines recolor cx.pal none #[] title.toList), cx)
  | .list o items =>
    let r := recolorRolesItems repal recolor cx #[] items.toList
    (.list o r.1, r.2)
  | .center body =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.center r.1, r.2)
  | .ragged s body =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.ragged s r.1, r.2)
  | .quote body =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.quote r.1, r.2)
  | .abstract body =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.abstract r.1, r.2)
  -- The title sits on the bar when the palette in force declares one, on
  -- the page otherwise (`titledLook`, the one resolving site — the same
  -- ground the judge reads); the body keeps the enclosing ground.
  | .titled kind title body =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.titled kind
      (recolorRolesInlines recolor cx.pal (titledLook cx.pal kind).bar #[] title.toList)
      r.1, r.2)
  | .role n body =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.role n r.1, r.2)
  | .link target body =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.link target r.1, r.2)
  | .spaced g body =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.spaced g r.1, r.2)
  | .columns cols =>
    let r := recolorRolesColumns repal recolor cx #[] cols.toList
    (.columns r.1, r.2)
  | .onSteps spec body =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.onSteps spec r.1, r.2)
  | .altSteps spec firstPage otherPage =>
    let ra := recolorRolesList repal recolor cx #[] firstPage.toList
    let ro := recolorRolesList repal recolor ra.2 #[] otherPage.toList
    (.altSteps spec ra.1 ro.1, ro.2)
  | .only targets body =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.only targets r.1, r.2)
  | .nav spec body =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.nav spec r.1, r.2)
  -- The title sits on the frame-title bar when the palette in force
  -- declares one; a standout frame's body sits on the inversion, and a
  -- title page with a declared ground on that ground (`titleGroundOf`) —
  -- the grounds the judge reads, at the palette in force at the frame.
  | .frame title standout valign br body =>
    let bodyGround := if standout then
        some ((cx.pal.find? "standoutbg").getD ((cx.pal.find? "fg").getD Color.black))
      else (titleGroundOf cx.pal valign).or cx.ground
    let r := recolorRolesList repal recolor { cx with ground := bodyGround } #[] body.toList
    (.frame (recolorRolesInlines recolor cx.pal (cx.pal.find? "frametitlebg") #[] title.toList)
      standout valign br r.1,
      { r.2 with ground := if r.2.epoch == cx.epoch then cx.ground else none })
  | .framefoot content =>
    (.framefoot (recolorRolesInlines recolor cx.pal (Design.ofPalette cx.pal).footline.bar
      #[] content.toList), cx)
  -- The epoch boundary: the palette is rewritten where it stands, and the
  -- walk's context switches to the declared (pre-rewrite) state, the one
  -- the judge keyed its plan by.
  | .setPalette p =>
    (.setPalette (repal p), { pal := p, ground := none, epoch := cx.epoch + 1 })
  | .setTokens tk => (.setTokens tk, cx)
  | .pagebreak => (.pagebreak, cx)
  -- A note is a side channel, verbatim carries no role-named runs, a logo
  -- is furniture, a rule is decorative ink: the judge reads none of them,
  -- so the walk leaves each whole.
  | .note body => (.note body, cx)
  | .verbatim c s sp => (.verbatim c s sp, cx)
  -- Lines are judged where they stand (`Contrast.usesBlock` descends into
  -- content and comment), so the realizer rewrites exactly there.
  | .algorithm n sm lines =>
    (.algorithm n sm (recolorRolesAlgLines recolor cx.pal cx.ground #[] lines.toList), cx)
  | .logo content => (.logo content, cx)
  | .rule c nm th => (.rule c nm th, cx)
  -- A label is a run like any other: it ships the plan's ink for its
  -- pairing on the ground under it — a node's fill, else the ground the
  -- picture stands on — so one expression on one ground is one ink,
  -- whether it is set in a paragraph or in a drawing.
  | .picture p =>
    (.picture { p with shapes := recolorRolesShapes recolor cx.pal cx.ground #[] p.shapes.toList },
      cx)
  | .table cols pl pr rows rules spans =>
    (.table cols pl pr (recolorRolesTableRows recolor cx.pal cx.ground #[] rows.toList) rules spans, cx)
  | .float fk num ca body caption =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    (.float fk num ca r.1
      (recolorRolesInlines recolor cx.pal cx.ground #[] caption.toList), r.2)
  | .bibliography src style items =>
    (.bibliography src style
      (recolorRolesBibItems recolor cx.pal cx.ground #[] items.toList), cx)

private def recolorRolesItems (repal : Palette → Palette) (recolor : RoleRecolor)
    (cx : RoleRecolorState) (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block) × RoleRecolorState
  | [] => (out, cx)
  | item :: rest =>
    let r := recolorRolesList repal recolor cx #[] item.toList
    recolorRolesItems repal recolor r.2 (out.push r.1) rest

private def recolorRolesColumns (repal : Palette → Palette) (recolor : RoleRecolor)
    (cx : RoleRecolorState) (out : Array (BoxWidth × Array Block)) :
    List (BoxWidth × Array Block) → Array (BoxWidth × Array Block) × RoleRecolorState
  | [] => (out, cx)
  | (w, body) :: rest =>
    let r := recolorRolesList repal recolor cx #[] body.toList
    recolorRolesColumns repal recolor r.2 (out.push (w, r.1)) rest

private def recolorRolesTableRows (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (out : Array (Array (Array Inline))) :
    List (Array (Array Inline)) → Array (Array (Array Inline))
  | [] => out
  | row :: rest =>
    recolorRolesTableRows recolor pal ground
      (out.push (recolorRolesTableCells recolor pal ground #[] row.toList)) rest

private def recolorRolesTableCells (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (out : Array (Array Inline)) :
    List (Array Inline) → Array (Array Inline)
  | [] => out
  | cell :: rest =>
    recolorRolesTableCells recolor pal ground
      (out.push (recolorRolesInlines recolor pal ground #[] cell.toList)) rest

private def recolorRolesBibItems (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (out : Array BibItem) :
    List BibItem → Array BibItem
  | [] => out
  | item :: rest =>
    recolorRolesBibItems recolor pal ground
      (out.push { item with
        content := recolorRolesInlines recolor pal ground #[] item.content.toList }) rest

private def recolorRolesAlgLines (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (out : Array AlgLine) : List AlgLine → Array AlgLine
  | [] => out
  | l :: rest =>
    recolorRolesAlgLines recolor pal ground (out.push
      { depth := l.depth
        kind := l.kind
        content := recolorRolesInlines recolor pal ground #[] l.content.toList
        comment := match l.comment with
          | some c => some (recolorRolesInlines recolor pal ground #[] c.toList)
          | none => Option.none }) rest

/-- A picture's shapes in drawing order, each label recoloured on the ground
under its anchor (`Pic.fillUnder` over the shapes drawn before it); every
other shape keeps its paint. -/
private def recolorRolesShapes (recolor : RoleRecolor) (pal : Palette) (ground : Option Color)
    (drawn : Array Pic.Shape) : List Pic.Shape → Array Pic.Shape
  | [] => drawn
  | s :: rest =>
    let s' := match s with
      | .label x y content c sc al =>
        let g := (Pic.fillUnder drawn x y).or ground
        .label x y (recolorRolesInlines recolor pal g #[] content.toList) (recolor pal g none c)
          sc al
      | .rect x y w h c => .rect x y w h c
      | .circle x y r st fl => .circle x y r st fl
      | .frame x y w h st fl => .frame x y w h st fl
      | .edge segs st tip => .edge segs st tip
    recolorRolesShapes recolor pal ground (drawn.push s') rest


end

/-- The realization entry: the whole body walked once, page ground, the
document's own palette the opening epoch. -/
public def recolorRoles (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) (xs : Array Block) : Array Block :=
  (recolorRolesList repal recolor { pal } #[] xs.toList).1

private theorem blockTextBibItems_chain (l1 l2 : List BibItem) (acc : String) :
    blockTextBibItems acc (l1 ++ l2)
      = blockTextBibItems (blockTextBibItems acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextBibItems]
  | cons item rest ih => simp [blockTextBibItems, ih]

mutual

private theorem recolorRolesInlines_text (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (xs : List Inline) (out : Array Inline) :
    plainTextList (recolorRolesInlines recolor pal ground out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [recolorRolesInlines, plainTextList]
  | x :: rest =>
    rw [recolorRolesInlines, recolorRolesInlines_text recolor pal ground rest]
    simp [plainTextList, plainTextList_append,
      recolorRolesInline_text recolor pal ground x, String.append_assoc]

private theorem recolorRolesInline_text (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (x : Inline) :
    plainTextOne (recolorRolesInline recolor pal ground x) = plainTextOne x := by
  match x with
  | .colored c nm body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .styled st body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .located n body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .role n body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .link u body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .decorated kind body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .onSteps spec body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .altSteps spec firstPage otherPage =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground firstPage.toList #[],
      recolorRolesInlines_text recolor pal ground otherPage.toList #[], plainTextList]
  | .footnote n body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .formula d src body =>
    rw [recolorRolesInline]
    simp [plainTextOne, formulaFloor_ink_id]
  | .text _ | .math _ _ | .image _ _ _ | .icon _ _ | .label _
  | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount
  | .linebreak _ => rfl

end

private theorem recolorRolesTableCells_text (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (cells : List (Array Inline))
    (out : Array (Array Inline)) (acc : String) :
    blockTextTableCells acc (recolorRolesTableCells recolor pal ground out cells).toList
      = blockTextTableCells (blockTextTableCells acc out.toList) cells := by
  match cells with
  | [] => simp [recolorRolesTableCells, blockTextTableCells]
  | cell :: rest =>
    rw [recolorRolesTableCells, recolorRolesTableCells_text recolor pal ground rest]
    simp [blockTextTableCells, blockTextTableCells_chain, plainText,
      recolorRolesInlines_text recolor pal ground cell.toList #[], plainTextList]

private theorem recolorRolesTableRows_text (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (rows : List (Array (Array Inline)))
    (out : Array (Array (Array Inline))) (acc : String) :
    blockTextTableRows acc (recolorRolesTableRows recolor pal ground out rows).toList
      = blockTextTableRows (blockTextTableRows acc out.toList) rows := by
  match rows with
  | [] => simp [recolorRolesTableRows, blockTextTableRows]
  | row :: rest =>
    rw [recolorRolesTableRows, recolorRolesTableRows_text recolor pal ground rest]
    simp [blockTextTableRows, blockTextTableRows_chain,
      recolorRolesTableCells_text recolor pal ground row.toList #[], blockTextTableCells]

private theorem recolorRolesBibItems_text (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (items : List BibItem)
    (out : Array BibItem) (acc : String) :
    blockTextBibItems acc (recolorRolesBibItems recolor pal ground out items).toList
      = blockTextBibItems (blockTextBibItems acc out.toList) items := by
  match items with
  | [] => simp [recolorRolesBibItems, blockTextBibItems]
  | item :: rest =>
    rw [recolorRolesBibItems, recolorRolesBibItems_text recolor pal ground rest]
    simp [blockTextBibItems, blockTextBibItems_chain, plainText,
      recolorRolesInlines_text recolor pal ground item.content.toList #[], plainTextList]

private theorem recolorRolesAlgLines_text (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (ls : List AlgLine) (out : Array AlgLine)
    (acc : String) :
    algLineText acc (recolorRolesAlgLines recolor pal ground out ls).toList
      = algLineText (algLineText acc out.toList) ls := by
  match ls with
  | [] => simp [recolorRolesAlgLines, algLineText]
  | l :: rest =>
    rw [recolorRolesAlgLines, recolorRolesAlgLines_text recolor pal ground rest]
    rw [Array.toList_push, algLineText_chain]
    cases hc : l.comment with
    | none =>
      simp [algLineText, hc, plainText, plainTextList,
        recolorRolesInlines_text recolor pal ground l.content.toList #[]]
    | some c =>
      simp [algLineText, hc, plainText, plainTextList,
        recolorRolesInlines_text recolor pal ground l.content.toList #[],
        recolorRolesInlines_text recolor pal ground c.toList #[]]

mutual

private theorem recolorRolesList_text (repal : Palette → Palette) (recolor : RoleRecolor)
    (cx : RoleRecolorState) (xs : List Block)
    (out : Array Block) (acc : String) :
    blockTextList acc (recolorRolesList repal recolor cx out xs).1.toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [recolorRolesList, blockTextList]
  | b :: rest =>
    rw [recolorRolesList,
      recolorRolesList_text repal recolor
        (recolorRolesBlock repal recolor cx b).2 rest]
    simp [blockTextList, blockTextList_chain,
      recolorRolesBlock_text repal recolor cx b]

private theorem recolorRolesBlock_text (repal : Palette → Palette) (recolor : RoleRecolor)
    (cx : RoleRecolorState) (b : Block) (acc : String) :
    blockTextOne acc (recolorRolesBlock repal recolor cx b).1
      = blockTextOne acc b := by
  match b with
  | .para content =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor cx.pal cx.ground content.toList #[], plainTextList]
  | .equation num content =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor cx.pal cx.ground content.toList #[],
      recolorRolesInlines_text recolor cx.pal cx.ground num.toList #[], plainTextList]
  | .section l st num title =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor cx.pal none title.toList #[], plainTextList]
  | .list o items =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesItems_text repal recolor cx items.toList #[] acc,
      blockTextItems]
  | .center body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor cx body.toList #[] acc, blockTextList]
  | .ragged _ body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor cx body.toList #[] acc, blockTextList]
  | .quote body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor cx body.toList #[] acc, blockTextList]
  | .abstract body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor cx body.toList #[] acc, blockTextList]
  | .titled kind title body =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor cx.pal (titledLook cx.pal kind).bar title.toList #[],
      plainTextList,
      recolorRolesList_text repal recolor cx body.toList #[] _, blockTextList]
  | .role n body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor cx body.toList #[] acc, blockTextList]
  | .link target body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor cx body.toList #[] acc, blockTextList]
  | .spaced g body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor cx body.toList #[] acc, blockTextList]
  | .columns cols =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesColumns_text repal recolor cx cols.toList #[] acc,
      blockTextColumns]
  | .onSteps spec body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor cx body.toList #[] acc, blockTextList]
  | .altSteps spec firstPage otherPage =>
    rw [recolorRolesBlock]
    simp [blockTextOne, recolorRolesList_text, blockTextList]
  | .only targets body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor cx body.toList #[] acc, blockTextList]
  | .nav spec body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor cx body.toList #[] acc, blockTextList]
  | .frame title standout valign _ body =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor cx.pal (cx.pal.find? "frametitlebg") title.toList #[],
      plainTextList,
      recolorRolesList_text repal recolor
        { cx with ground :=
            if standout then
              some ((cx.pal.find? "standoutbg").getD ((cx.pal.find? "fg").getD Color.black))
            else (titleGroundOf cx.pal valign).or cx.ground } body.toList #[] _,
      blockTextList]
  | .framefoot content =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor cx.pal (Design.ofPalette cx.pal).footline.bar
        content.toList #[], plainTextList]
  | .setPalette _ | .setTokens _ | .pagebreak | .note _ | .verbatim _ _ _
  | .logo _ | .rule _ _ _ | .picture _ => rfl
  | .algorithm n sm lines =>
    rw [recolorRolesBlock]
    show algLineText acc
      (recolorRolesAlgLines recolor cx.pal cx.ground #[] lines.toList).toList = _
    rw [recolorRolesAlgLines_text recolor cx.pal cx.ground lines.toList #[] acc]
    rfl
  | .table cols pl pr rows rules spans =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesTableRows_text recolor cx.pal cx.ground rows.toList #[] acc,
      blockTextTableRows]
  | .float fk num ca body caption =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor cx.pal cx.ground caption.toList #[], plainTextList,
      recolorRolesList_text repal recolor cx body.toList #[] _, blockTextList]
  | .bibliography src style items =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesBibItems_text recolor cx.pal cx.ground items.toList #[] acc,
      blockTextBibItems]

private theorem recolorRolesItems_text (repal : Palette → Palette) (recolor : RoleRecolor)
    (cx : RoleRecolorState) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (recolorRolesItems repal recolor cx out items).1.toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [recolorRolesItems, blockTextItems]
  | item :: rest =>
    rw [recolorRolesItems,
      recolorRolesItems_text repal recolor
        (recolorRolesList repal recolor cx #[] item.toList).2 rest]
    simp [blockTextItems, blockTextItems_chain,
      recolorRolesList_text repal recolor cx item.toList #[], blockTextList]

private theorem recolorRolesColumns_text (repal : Palette → Palette) (recolor : RoleRecolor)
    (cx : RoleRecolorState)
    (cols : List (BoxWidth × Array Block))
    (out : Array (BoxWidth × Array Block)) (acc : String) :
    blockTextColumns acc (recolorRolesColumns repal recolor cx out cols).1.toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [recolorRolesColumns, blockTextColumns]
  | (w, body) :: rest =>
    rw [recolorRolesColumns,
      recolorRolesColumns_text repal recolor
        (recolorRolesList repal recolor cx #[] body.toList).2 rest]
    simp [blockTextColumns, blockTextColumns_chain,
      recolorRolesList_text repal recolor cx body.toList #[], blockTextList]

end

/-- Realization recolours, it never rewrites content: the text census is
fixed through the whole walk, whatever the plan's recolour and palette
rewrite do — a realized document says exactly what the declared one
said. -/
public theorem recolorRoles_text (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) : Conserves blocksText (recolorRoles repal recolor pal) := fun xs => by
  simp [blocksText, recolorRoles,
    recolorRolesList_text repal recolor { pal } xs.toList #[] "", blockTextList]

-- Backend conditionals: `keepFor` is one backend's view of the document,
-- and `keepFor_covers` is what stops a conditional from becoming a silent
-- delete. Structural recursion through `List`, as the walks above.

/-- The backend names an `{ifbackend}` target may spell: one per emitter,
exactly the values `\output{ formats = ... }` accepts (`Cli.Args.emitOne`
mirrors this list, and each backend passes its own entry to `keepFor`). -/
public def backendNames : List String := ["pdf", "html", "md"]

/-- Does backend `t` keep this block? Only a conditional can exclude one. -/
@[expose] public def keptBy (t : String) : Block → Bool
  | .only targets _ => targets.contains t
  | .para _ | .equation _ _ | .section _ _ _ _ | .list _ _ | .center _ | .ragged _ _
  | .quote _ | .abstract _
  | .role _ _ | .link _ _
  | .titled _ _ _
  | .spaced _ _
  | .verbatim _ _ _ | .columns _ | .onSteps _ _ | .note _ | .logo _
  | .altSteps _ _ _
  | .frame _ _ _ _ _ | .framefoot _ | .setPalette _ | .setTokens _
  | .rule _ _ _ | .nav _ _ | .picture _ | .pagebreak | .algorithm _ _ _
  | .table _ _ _ _ _ _ | .float _ _ _ _ _ | .bibliography _ _ _ => true

mutual

/-- The document as backend `t` sees it: an `.only` block whose targets
exclude `t` is dropped whole, everything else is kept, and the walk carries
into every body so a nested conditional resolves against its own targets.
Each backend applies this once at its entry, with its own name — the drop
decision lives here and nowhere else, so no backend can improvise a
different reading of the same target set. -/
@[expose] public def keepForOne (t : String) : Block → Block
  | .only targets body => .only targets (keepForList t body.toList).toArray
  | .nav spec body => .nav spec (keepForList t body.toList).toArray
  | .list o items => .list o (keepForItems t items.toList).toArray
  | .center body => .center (keepForList t body.toList).toArray
  | .ragged s body => .ragged s (keepForList t body.toList).toArray
  | .quote body => .quote (keepForList t body.toList).toArray
  | .abstract body => .abstract (keepForList t body.toList).toArray
  | .titled kind title body => .titled kind title (keepForList t body.toList).toArray
  | .role n body => .role n (keepForList t body.toList).toArray
  | .link target body => .link target (keepForList t body.toList).toArray
  | .spaced g body => .spaced g (keepForList t body.toList).toArray
  | .columns cols => .columns (keepForColumns t cols.toList).toArray
  | .onSteps spec body => .onSteps spec (keepForList t body.toList).toArray
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (keepForList t firstPage.toList).toArray (keepForList t otherPage.toList).toArray
  | .note body => .note (keepForList t body.toList).toArray
  | .frame ti st v br body => .frame ti st v br (keepForList t body.toList).toArray
  | .para c => .para c
  | .equation n c => .equation n c
  | .section l st num title => .section l st num title
  | .verbatim c s sp => .verbatim c s sp
  | .logo c => .logo c
  | .framefoot c => .framefoot c
  | .setPalette pal => .setPalette pal
  | .setTokens tk => .setTokens tk
  | .pagebreak => .pagebreak
  | .rule c n th => .rule c n th
  | .picture p => .picture p
  -- Cells hold inlines: no conditional can nest in a table. A float's
  -- body is blocks, so the walk carries in, as through a frame.
  | .table c pl pr rows rules spans => .table c pl pr rows rules spans
  -- Lines hold inlines: no conditional can nest in an algorithm.
  | .algorithm n sm lines => .algorithm n sm lines
  | .float k n ca body caption => .float k n ca (keepForList t body.toList).toArray caption
  -- Entries hold inlines: no conditional can nest in a reference list.
  | .bibliography src style items => .bibliography src style items

@[expose] public def keepForList (t : String) : List Block → List Block
  | [] => []
  | b :: rest =>
    match keptBy t b with
    | true => keepForOne t b :: keepForList t rest
    | false => keepForList t rest

public def keepForItems (t : String) : List (Array Block) → List (Array Block)
  | [] => []
  | item :: rest => (keepForList t item.toList).toArray :: keepForItems t rest

public def keepForColumns (t : String) :
    List (BoxWidth × Array Block) → List (BoxWidth × Array Block)
  | [] => []
  | (w, body) :: rest => (w, (keepForList t body.toList).toArray) :: keepForColumns t rest

end

@[expose] public def keepFor (t : String) (xs : Array Block) : Array Block :=
  (keepForList t xs.toList).toArray

/-- Algorithm text leaves: each line's declared content is one leaf, its
comment another — a line survives a backend's view whole or not at all,
as a cell does. -/
private def algTextLeaves (acc : List String) : List AlgLine → List String
  | [] => acc
  | l :: rest =>
    algTextLeaves (match l.comment with
      | some c => plainText c :: plainText l.content :: acc
      | none => plainText l.content :: acc) rest

mutual

/-- Every text leaf of the blocks — each paragraph's, title's, and verbatim
block's plain text as one element (most recent first; the census is read as
a set). The backend-conditional conservation theorem ranges over leaves
rather than `blocksText`'s one concatenated string because a leaf survives
`keepFor` whole or not at all: a character's membership in the
concatenation could be satisfied by coincidence, a whole surviving leaf
cannot be. -/
private def textLeavesList (acc : List String) : List Block → List String
  | [] => acc
  | b :: rest => textLeavesList (textLeavesOne acc b) rest

private def textLeavesOne (acc : List String) : Block → List String
  | .para content => plainText content :: acc
  | .equation _ content => plainText content :: acc
  | .section _ _ _ title => plainText title :: acc
  | .verbatim _ s spec =>
    match spec.caption with
    | some (_, cap) => s :: plainText cap :: acc
    | none => s :: acc
  | .logo content => plainText content :: acc
  | .framefoot content => plainText content :: acc
  -- A stateful declaration carries no text leaf.
  | .setPalette _ => acc
  | .setTokens _ => acc
  | .pagebreak => acc
  | .list _ items => textLeavesItems acc items.toList
  | .center body => textLeavesList acc body.toList
  | .ragged _ body => textLeavesList acc body.toList
  | .quote body => textLeavesList acc body.toList
  | .abstract body => textLeavesList acc body.toList
  | .titled _ title body => textLeavesList (plainText title :: acc) body.toList
  | .role _ body => textLeavesList acc body.toList
  | .link _ body => textLeavesList acc body.toList
  | .spaced _ body => textLeavesList acc body.toList
  | .columns cols => textLeavesColumns acc cols.toList
  | .onSteps _ body => textLeavesList acc body.toList
  | .altSteps _ firstPage otherPage =>
    textLeavesList (textLeavesList acc firstPage.toList) otherPage.toList
  | .note body => textLeavesList acc body.toList
  | .only _ body => textLeavesList acc body.toList
  | .nav _ body => textLeavesList acc body.toList
  | .frame title _ _ _ body => textLeavesList (plainText title :: acc) body.toList
  -- A rule is decorative ink; it carries no text (as `blockTextOne` reads it).
  | .rule _ _ _ => acc
  -- A picture's labels reach the census through the shipped runs, as
  -- `blockTextOne` reads it.
  | .picture _ => acc
  -- Each cell is one leaf: it survives a backend's view whole or not at
  -- all, which is what the conservation theorem needs to range over. The
  -- caption is a leaf beside its float's body, as a frame's title is.
  | .table _ _ _ rows _ _ => textLeavesTableRows acc rows.toList
  | .algorithm _ _ lines => algTextLeaves acc lines.toList
  | .float _ _ _ body caption => textLeavesList (plainText caption :: acc) body.toList
  -- Each entry is one leaf, as a cell is: it survives a backend's view
  -- whole or not at all.
  | .bibliography _ _ items => textLeavesBibItems acc items.toList

private def textLeavesBibItems (acc : List String) : List BibItem → List String
  | [] => acc
  | item :: rest => textLeavesBibItems (plainText item.content :: acc) rest

private def textLeavesTableRows (acc : List String) :
    List (Array (Array Inline)) → List String
  | [] => acc
  | row :: rest => textLeavesTableRows (textLeavesTableCells acc row.toList) rest

private def textLeavesTableCells (acc : List String) : List (Array Inline) → List String
  | [] => acc
  | cell :: rest => textLeavesTableCells (plainText cell :: acc) rest

private def textLeavesItems (acc : List String) : List (Array Block) → List String
  | [] => acc
  | item :: rest => textLeavesItems (textLeavesList acc item.toList) rest

private def textLeavesColumns (acc : List String) :
    List (BoxWidth × Array Block) → List String
  | [] => acc
  | (_, body) :: rest => textLeavesColumns (textLeavesList acc body.toList) rest

end

public def textLeaves (xs : Array Block) : List String := textLeavesList [] xs.toList

mutual

/-- No content is addressed to no backend: along every nesting path, each
`.only` node's targets keep at least one member of `avail` — the ambient
set, `backendNames` at the top and the path intersection inside a
conditional, so an `{ifbackend}{pdf}` inside an `{ifbackend}{html}`
addresses the empty set whatever each node spells alone. Elaboration
performs the same intersection as it walks in and fires E0334 exactly where
this returns false (pinned by test; `Elab` is monadic, so the
correspondence is not itself a theorem). -/
private def orphanFreeList (avail : List String) : List Block → Bool
  | [] => true
  | b :: rest => orphanFreeOne avail b && orphanFreeList avail rest

private def orphanFreeOne (avail : List String) : Block → Bool
  | .only targets body =>
    let eff := avail.filter (fun a => targets.contains a)
    !eff.isEmpty && orphanFreeList eff body.toList
  | .list _ items => orphanFreeItems avail items.toList
  | .center body => orphanFreeList avail body.toList
  | .ragged _ body => orphanFreeList avail body.toList
  | .quote body => orphanFreeList avail body.toList
  | .abstract body => orphanFreeList avail body.toList
  | .titled _ _ body => orphanFreeList avail body.toList
  | .role _ body => orphanFreeList avail body.toList
  | .link _ body => orphanFreeList avail body.toList
  | .spaced _ body => orphanFreeList avail body.toList
  | .columns cols => orphanFreeColumns avail cols.toList
  | .onSteps _ body => orphanFreeList avail body.toList
  | .altSteps _ firstPage otherPage =>
    orphanFreeList avail firstPage.toList && orphanFreeList avail otherPage.toList
  | .note body => orphanFreeList avail body.toList
  | .nav _ body => orphanFreeList avail body.toList
  | .frame _ _ _ _ body => orphanFreeList avail body.toList
  | .para _ | .equation _ _ | .section _ _ _ _ | .verbatim _ _ _ | .logo _ | .framefoot _
  | .setPalette _ | .setTokens _ | .algorithm _ _ _
  | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ | .pagebreak
  | .bibliography _ _ _ => true
  | .float _ _ _ body _ => orphanFreeList avail body.toList

private def orphanFreeItems (avail : List String) : List (Array Block) → Bool
  | [] => true
  | item :: rest => orphanFreeList avail item.toList && orphanFreeItems avail rest

private def orphanFreeColumns (avail : List String) :
    List (BoxWidth × Array Block) → Bool
  | [] => true
  | (_, body) :: rest =>
    orphanFreeList avail body.toList && orphanFreeColumns avail rest

end

public def orphanFree (avail : List String) (xs : Array Block) : Bool :=
  orphanFreeList avail xs.toList

-- The accumulator lemmas: a leaf census over `acc` is the census over `[]`
-- appended to `acc`, so membership statements can be read off `mem_append`.

private theorem algTextLeaves_acc (acc : List String) (ls : List AlgLine) :
    algTextLeaves acc ls = algTextLeaves [] ls ++ acc := by
  induction ls generalizing acc with
  | nil => simp [algTextLeaves]
  | cons l rest ih =>
    cases hc : l.comment with
    | none =>
      rw [algTextLeaves, algTextLeaves]
      simp only [hc]
      rw [ih (plainText l.content :: acc), ih [plainText l.content]]
      simp
    | some c =>
      rw [algTextLeaves, algTextLeaves]
      simp only [hc]
      rw [ih (plainText c :: plainText l.content :: acc),
        ih [plainText c, plainText l.content]]
      simp

private theorem textLeavesTableCells_acc (acc : List String)
    (cells : List (Array Inline)) :
    textLeavesTableCells acc cells = textLeavesTableCells [] cells ++ acc := by
  induction cells generalizing acc with
  | nil => simp [textLeavesTableCells]
  | cons cell rest ih =>
    rw [textLeavesTableCells, textLeavesTableCells, ih (plainText cell :: acc),
      ih [plainText cell]]
    simp

private theorem textLeavesTableRows_acc (acc : List String)
    (rows : List (Array (Array Inline))) :
    textLeavesTableRows acc rows = textLeavesTableRows [] rows ++ acc := by
  induction rows generalizing acc with
  | nil => simp [textLeavesTableRows]
  | cons row rest ih =>
    rw [textLeavesTableRows, textLeavesTableRows,
      ih (textLeavesTableCells acc row.toList),
      ih (textLeavesTableCells [] row.toList),
      textLeavesTableCells_acc acc row.toList]
    simp

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
  | .equation _ c => simp [textLeavesOne]
  | .section l st num title => simp [textLeavesOne]
  | .verbatim c s sp => cases hc : sp.caption <;> simp [textLeavesOne, hc]
  | .logo c => simp [textLeavesOne]
  | .framefoot c => simp [textLeavesOne]
  | .setPalette pal => simp [textLeavesOne]
  | .setTokens tk => simp [textLeavesOne]
  | .pagebreak => simp [textLeavesOne]
  | .rule c n th => simp [textLeavesOne]
  | .picture p => simp [textLeavesOne]
  | .algorithm n sm lines =>
    rw [textLeavesOne, textLeavesOne]
    exact algTextLeaves_acc acc lines.toList
  | .list o items =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesItems_acc acc items.toList
  | .center body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .ragged _ body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .quote body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .abstract body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .titled k t body =>
    rw [textLeavesOne, textLeavesOne,
      textLeavesList_acc (plainText t :: acc) body.toList,
      textLeavesList_acc [plainText t] body.toList]
    simp
  | .role n body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .link target body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .spaced g body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .columns cols =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesColumns_acc acc cols.toList
  | .onSteps spec body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .altSteps spec firstPage otherPage =>
    rw [textLeavesOne, textLeavesOne, textLeavesList_acc acc firstPage.toList,
      textLeavesList_acc (textLeavesList [] firstPage.toList ++ acc) otherPage.toList,
      textLeavesList_acc (textLeavesList [] firstPage.toList) otherPage.toList]
    simp [List.append_assoc]
  | .note body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .only targets body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .nav spec body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .frame title st v _ body =>
    rw [textLeavesOne, textLeavesOne,
      textLeavesList_acc (plainText title :: acc) body.toList,
      textLeavesList_acc [plainText title] body.toList]
    simp
  | .table c pl pr rows rules spans =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesTableRows_acc acc rows.toList
  | .float k n ca body caption =>
    rw [textLeavesOne, textLeavesOne,
      textLeavesList_acc (plainText caption :: acc) body.toList,
      textLeavesList_acc [plainText caption] body.toList]
    simp
  | .bibliography src style items =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesBibItems_acc acc items.toList

private theorem textLeavesBibItems_acc (acc : List String) (items : List BibItem) :
    textLeavesBibItems acc items = textLeavesBibItems [] items ++ acc := by
  match items with
  | [] => simp [textLeavesBibItems]
  | item :: rest =>
    rw [textLeavesBibItems, textLeavesBibItems,
      textLeavesBibItems_acc (plainText item.content :: acc) rest,
      textLeavesBibItems_acc [plainText item.content] rest]
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
    (cols : List (BoxWidth × Array Block)) :
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
private theorem keepForList_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
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

private theorem keepForOne_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (b : Block) (h : orphanFreeOne avail b = true) :
    ∀ s ∈ textLeavesOne [] b,
      ∃ t ∈ avail, keptBy t b = true ∧ s ∈ textLeavesOne [] (keepForOne t b) := by
  match b with
  | .para c =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .equation n c =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .section l st num title =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .verbatim c str sp =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .logo c =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .framefoot c =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .setPalette pal =>
    intro s hs
    simp [textLeavesOne] at hs
  | .setTokens tk =>
    intro s hs
    simp [textLeavesOne] at hs
  | .rule c n th =>
    intro s hs
    simp [textLeavesOne] at hs
  | .picture p =>
    intro s hs
    simp [textLeavesOne] at hs
  | .pagebreak =>
    intro s hs
    simp [textLeavesOne] at hs
  | .table c pl pr rows rules spans =>
    -- kept whole by every backend: its own leaves survive untouched
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .algorithm n sm lines =>
    -- kept whole by every backend, as a table is
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .bibliography src style items =>
    -- kept whole by every backend, as a table is
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .float k n ca body caption =>
    intro s hs
    rw [textLeavesOne, textLeavesList_acc [plainText caption] body.toList,
      List.mem_append] at hs
    cases hs with
    | inr hcap =>
      refine ⟨t0, h0, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText caption]
          ((keepForList t0 body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inr hcap)
    | inl hbody =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hbody
      refine ⟨t, ht, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText caption]
          ((keepForList t body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inl (by simpa using hmem))
  | .center body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .ragged _ body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .quote body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .titled k ti body =>
    intro s hs
    rw [textLeavesOne, textLeavesList_acc [plainText ti] body.toList,
      List.mem_append] at hs
    cases hs with
    | inr hcap =>
      refine ⟨t0, h0, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText ti]
          ((keepForList t0 body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inr hcap)
    | inl hbody =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hbody
      refine ⟨t, ht, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText ti]
          ((keepForList t body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inl (by simpa using hmem))
  | .abstract body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .role n body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .link target body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .spaced g body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .onSteps spec body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .altSteps spec firstPage otherPage =>
    intro s hs
    rw [orphanFreeOne, Bool.and_eq_true] at h
    rw [textLeavesOne, textLeavesList_acc, List.mem_append] at hs
    cases hs with
    | inl hso =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 otherPage.toList h.2 s hso
      refine ⟨t, ht, rfl, ?_⟩
      rw [keepForOne, textLeavesOne, textLeavesList_acc, List.mem_append]
      exact .inl (by simpa using hmem)
    | inr hsa =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 firstPage.toList h.1 s hsa
      refine ⟨t, ht, rfl, ?_⟩
      rw [keepForOne, textLeavesOne, textLeavesList_acc, List.mem_append]
      exact .inr (by simpa using hmem)
  | .note body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .nav spec body =>
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
  | .frame title st v _ body =>
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

private theorem keepForItems_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
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

private theorem keepForColumns_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (cols : List (BoxWidth × Array Block))
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
condition whose violation elaboration diagnoses as E0334) — every declared
text leaf survives in at least one backend's kept document: the union over
the backends of what each `keepFor` keeps is the declared content. This is
the conservation theorem for the backend conditional, the one that stops
`{ifbackend}` from becoming a silent delete: dropping is only ever the
complement of another backend's keeping, or a named diagnostic. Stated over
the same `plainText` census machinery as the overlay conservation theorems
(`dimBlocks_text`), lifted to whole leaves because
`keepFor` drops whole subtrees. -/
public theorem keepFor_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (xs : Array Block) (h : orphanFree avail xs = true) :
    ∀ s ∈ textLeaves xs, ∃ t ∈ avail, s ∈ textLeaves (keepFor t xs) := by
  intro s hs
  obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 xs.toList h s hs
  exact ⟨t, ht, by simpa [textLeaves, keepFor] using hmem⟩

-- Content is backend-free: `onlyFree` is the premise (no `{ifbackend}`
-- anywhere), `keepFor_id` the statement. Structural recursion through
-- `List`, on `keepForList_covers`' skeleton.

mutual

/-- No backend conditional stands anywhere in the blocks: the premise under
which every backend's view is the whole document (`keepFor_id`). -/
@[expose] public def onlyFreeList : List Block → Bool
  | [] => true
  | b :: rest => onlyFreeOne b && onlyFreeList rest

@[expose] public def onlyFreeOne : Block → Bool
  | .only _ _ => false
  | .list _ items => onlyFreeItems items.toList
  | .center body => onlyFreeList body.toList
  | .ragged _ body => onlyFreeList body.toList
  | .quote body => onlyFreeList body.toList
  | .abstract body => onlyFreeList body.toList
  | .titled _ _ body => onlyFreeList body.toList
  | .role _ body => onlyFreeList body.toList
  | .link _ body => onlyFreeList body.toList
  | .spaced _ body => onlyFreeList body.toList
  | .columns cols => onlyFreeColumns cols.toList
  | .onSteps _ body => onlyFreeList body.toList
  | .altSteps _ firstPage otherPage =>
    onlyFreeList firstPage.toList && onlyFreeList otherPage.toList
  | .note body => onlyFreeList body.toList
  | .nav _ body => onlyFreeList body.toList
  | .frame _ _ _ _ body => onlyFreeList body.toList
  | .float _ _ _ body _ => onlyFreeList body.toList
  | .para _ | .equation _ _ | .section _ _ _ _ | .verbatim _ _ _ | .logo _ | .framefoot _
  | .setPalette _ | .setTokens _ | .rule _ _ _ | .picture _ | .algorithm _ _ _
  | .table _ _ _ _ _ _ | .pagebreak | .bibliography _ _ _ => true

public def onlyFreeItems : List (Array Block) → Bool
  | [] => true
  | item :: rest => onlyFreeList item.toList && onlyFreeItems rest

public def onlyFreeColumns : List (BoxWidth × Array Block) → Bool
  | [] => true
  | (_, body) :: rest => onlyFreeList body.toList && onlyFreeColumns rest

end

@[expose] public def onlyFree (xs : Array Block) : Bool := onlyFreeList xs.toList

mutual

public theorem keepForList_id (t : String) (xs : List Block)
    (h : onlyFreeList xs = true) : keepForList t xs = xs := by
  match xs with
  | [] => rfl
  | b :: rest =>
    rw [onlyFreeList, Bool.and_eq_true] at h
    have hk : keptBy t b = true := by
      cases b
      case only => exact absurd h.1 (by simp [onlyFreeOne])
      all_goals rfl
    rw [keepForList_kept t b rest hk, keepForOne_id t b h.1,
      keepForList_id t rest h.2]

public theorem keepForOne_id (t : String) (b : Block)
    (h : onlyFreeOne b = true) : keepForOne t b = b := by
  match b with
  | .only targets body => exact absurd h (by simp [onlyFreeOne])
  | .para c => rfl
  | .equation n c => rfl
  | .section l st num title => rfl
  | .verbatim c s sp => rfl
  | .logo c => rfl
  | .framefoot c => rfl
  | .setPalette pal => rfl
  | .setTokens tk => rfl
  | .pagebreak => rfl
  | .rule c n th => rfl
  | .picture p => rfl
  | .table c pl pr rows rules spans => rfl
  | .algorithm n sm lines => rfl
  | .bibliography src style items => rfl
  | .list o items =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForItems_id t items.toList h]
  | .center body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .ragged _ body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .quote body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .abstract body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .titled kind title body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .role n body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .link target body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .spaced g body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .columns cols =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForColumns_id t cols.toList h]
  | .onSteps spec body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .altSteps spec firstPage otherPage =>
    rw [onlyFreeOne, Bool.and_eq_true] at h
    simp [keepForOne, keepForList_id t firstPage.toList h.1,
      keepForList_id t otherPage.toList h.2]
  | .note body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .nav spec body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .frame ti st v _ body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .float k n ca body caption =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]

public theorem keepForItems_id (t : String) (items : List (Array Block))
    (h : onlyFreeItems items = true) : keepForItems t items = items := by
  match items with
  | [] => rfl
  | item :: rest =>
    rw [onlyFreeItems, Bool.and_eq_true] at h
    rw [keepForItems, keepForList_id t item.toList h.1,
      keepForItems_id t rest h.2]

public theorem keepForColumns_id (t : String) (cols : List (BoxWidth × Array Block))
    (h : onlyFreeColumns cols = true) : keepForColumns t cols = cols := by
  match cols with
  | [] => rfl
  | (w, body) :: rest =>
    rw [onlyFreeColumns, Bool.and_eq_true] at h
    rw [keepForColumns, keepForList_id t body.toList h.1,
      keepForColumns_id t rest h.2]

end

/-- **Content is backend-free.** The elaborated body of a document with no
`{ifbackend}` is identical whichever backend consumes it: every backend's
view (`keepFor` under its own name) is the whole document. The modulus is
exactly `keepFor`, applied once at each backend's entry — `Layout.run`,
`HtmlDoc.emitTree`, `MarkdownDoc.emit` — and nowhere else, so with no
conditional declared, "one source, N artifacts" ranges over the identical
block tree; what a backend then renders of a shared node (a nav as
outline, a note as nothing) is that medium's declared semantics, never a
different document. -/
public theorem keepFor_id (t : String) (xs : Array Block) (h : onlyFree xs = true) :
    keepFor t xs = xs := by
  rw [keepFor, keepForList_id t xs.toList h]


/-- The block face of `bibRefs`: the same leaf over a body not yet
assembled onto a `Doc` — the no-bibliography citation judge (Elab) reads
it where only the blocks exist. -/
public def bibRefsBlocks (blocks : Array Block) : Array String :=
  foldBlocks (fun out b => match b with
    | .bibliography src _ _ => if src.isEmpty || out.contains src then out else out.push src
    | _ => out) (fun out _ => out) #[] blocks

/-- The document's own reference list: the items of every `thebibliography`
(a `.bibliography` naming no `.bib` source), in document order. Nothing is
requested for them — their text is the document's. -/
public def ownBibItemsBlocks (blocks : Array Block) : Array BibItem :=
  foldBlocks (fun out b => match b with
    | .bibliography "" _ items => items.foldl (·.push ·) out
    | _ => out) (fun out _ => out) #[] blocks

/-- Every `.bib` source the document's `\bibliography` markers name, in
document order, deduplicated: the request value the CLI driver fulfils by
reading each file beside the document and handing its text to `Bib.apply`.
Files are effects, so the core never opens one — `imageRefs`' shape. -/
public def bibRefs (doc : Doc) : Array String := bibRefsBlocks doc.body

/-- The document's declared bibliography style: the first
`\bibliographystyle` in document order, `none` when nothing declared —
LaTeX keeps one bibliography style per document. -/
public def bibStyleName (doc : Doc) : Option String :=
  (foldBlocks (fun out b => match b with
    | .bibliography _ (some s) _ => out.push s
    | _ => out) (fun out _ => out) #[] doc.body)[0]?

-- Image walks: the request an image node states, and the caption an image
-- inherits.

/-- One image-source leaf into the collect: each `.image`'s source,
deduplicated, in document order. -/
private def imageSrcPush (out : Array String)
    (x : Inline) : Array String :=
  match x with
  | .image src _ _ => if out.contains src then out else out.push src
  | _ => out

/-- Every image source the inlines reference, in document order: a
`foldInlines` leaf, so the descent — `.role` and `.footnote` bodies
included — is the fold's, declared once and never re-decided here. An
image inside a footnote once shipped a silent placeholder because a
hand-rolled copy of this walk skipped those two arms while layout's
placement did not. -/
public def imageSrcsInlines (out : Array String) (xs : Array Inline) : Array String :=
  foldInlines imageSrcPush out xs

/-- The block face: `foldBlocks` with the same leaf. A `.bibliography`'s
items are formatted renderings and `Bib.apply` builds no image node, so
the fold's refusal to descend them loses nothing. -/
public def imageSrcsBlocks (out : Array String) (xs : Array Block) : Array String :=
  foldBlocks (fun out _ => out) imageSrcPush out xs

/-- Every inline region a backend sets beside the body — the running head
and foot, the logo state, the headline band, the corner logos, and each
style's templates, author font, marker and title-slot parts — as one list, so a walk
over "the whole document" is declared once: `foldDoc` reads these,
`mapDoc` rewrites them, and a resolver and a census cannot disagree on
what the document is. -/
public def furnitureInlines (doc : Doc) : Array (Array Inline) :=
  optRegion doc.head ++ optRegion doc.foot ++ optRegion doc.logo ++
    (match doc.headline with
      | some hl => #[hl.title, hl.author, hl.institute]
      | none => #[]) ++
    optRegion doc.logoLeft ++ optRegion doc.logoRight ++
    doc.styles.entries.flatMap fun (_, st) =>
      optRegion st.font ++ optRegion st.authorFont ++ optRegion st.marker ++
        st.slots.flatMap fun slot =>
          slot.parts.flatMap fun part => #[part.content] ++ optRegion part.font
where
  /-- An optional region as zero or one entries. -/
  optRegion : Option (Array Inline) → Array (Array Inline)
    | some r => #[r]
    | none => #[]

/-- `foldInlines` over the whole document: the body through `foldBlocks`,
then every furniture region, in `furnitureInlines`' order. A collector may
also read block-owned content through `fb`, as it can in `foldBlocks`. -/
@[expose] public def foldDoc (fi : α → Inline → α) (acc : α) (doc : Doc)
    (fb : α → Block → α := fun acc _ => acc) : α :=
  (furnitureInlines doc).foldl (fun acc r => foldInlines fi acc r)
    (foldBlocks fb fi acc doc.body)

/-- The rewrite face of `foldDoc`: `fb` rewrites the body, `fi` each
furniture region — the same regions, so a resolver that runs through here
reaches every node a census through `foldDoc` counts. -/
@[expose] public def mapDoc (fi : Array Inline → Array Inline) (fb : Array Block → Array Block)
    (doc : Doc) : Doc :=
  { doc with
    body := fb doc.body
    head := doc.head.map fi
    foot := doc.foot.map fi
    logo := doc.logo.map fi
    headline := doc.headline.map fun hl =>
      { title := fi hl.title, author := fi hl.author, institute := fi hl.institute }
    logoLeft := doc.logoLeft.map fi
    logoRight := doc.logoRight.map fi
    styles := { doc.styles with entries := doc.styles.entries.map fun (nm, st) =>
      (nm, { st with
        font := st.font.map fi
        authorFont := st.authorFont.map fi
        marker := st.marker.map fi
        slots := st.slots.map fun slot =>
          { slot with parts := slot.parts.map fun part =>
            { part with content := fi part.content, font := part.font.map fi } } }) } }

private theorem optRegion_map (fi : Array Inline → Array Inline) (o : Option (Array Inline)) :
    furnitureInlines.optRegion (o.map fi) = (furnitureInlines.optRegion o).map fi := by
  cases o <;> simp [furnitureInlines.optRegion]

/-- `mapDoc` rewrites exactly the regions `foldDoc` reads: the furniture of
the mapped document is the furniture of the original, each region through
`fi`. What lets a resolver through `mapDoc` discharge a census through
`foldDoc` (`Bib.apply_no_cite`). -/
public theorem furnitureInlines_mapDoc (fi : Array Inline → Array Inline)
    (fb : Array Block → Array Block) (doc : Doc) :
    furnitureInlines (mapDoc fi fb doc) = (furnitureInlines doc).map fi := by
  unfold furnitureInlines mapDoc
  rw [← Array.toList_inj]
  cases doc.headline <;>
    simp [optRegion_map, Array.toList_append, Array.toList_map, Array.toList_flatMap,
      List.flatMap_map, List.map_flatMap, List.map_append]

/-- The list fold over an appended list folds the halves in turn. -/
public theorem foldInlineList_append (fi : α → Inline → α) (acc : α) (l₁ l₂ : List Inline) :
    foldInlineList fi acc (l₁ ++ l₂) = foldInlineList fi (foldInlineList fi acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons x rest ih => rw [List.cons_append, foldInlineList, foldInlineList, ih]

public theorem foldBlockList_append (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (l₁ l₂ : List Block) :
    foldBlockList fb fi acc (l₁ ++ l₂) = foldBlockList fb fi (foldBlockList fb fi acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons b rest ih => rw [List.cons_append, foldBlockList, foldBlockList, ih]

public theorem foldBlockItems_append (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (l₁ l₂ : List (Array Block)) :
    foldBlockItems fb fi acc (l₁ ++ l₂) = foldBlockItems fb fi (foldBlockItems fb fi acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons b rest ih => rw [List.cons_append, foldBlockItems, foldBlockItems, ih]

public theorem foldBlockCols_append (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (l₁ l₂ : List (BoxWidth × Array Block)) :
    foldBlockCols fb fi acc (l₁ ++ l₂) = foldBlockCols fb fi (foldBlockCols fb fi acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons b rest ih =>
    obtain ⟨w, body⟩ := b
    rw [List.cons_append, foldBlockCols, foldBlockCols, ih]

/-- Folding a pushed block: the array first, then the block. -/
public theorem foldBlockList_push (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (out : Array Block) (b : Block) :
    foldBlockList fb fi acc (out.push b).toList = foldBlock fb fi (foldBlockList fb fi acc out.toList) b := by
  rw [Array.toList_push, foldBlockList_append]
  rfl

/-- Every image the document references, deduplicated, in document order:
the request value the CLI driver fulfils by reading and decoding each file
into the `Image.Store` layout and the backends consume. Files are effects,
so the core never opens one — the same shape as fonts. -/
public def imageRefs (doc : Doc) : Array String := foldDoc imageSrcPush #[] doc

/-- The asset selector belongs to an image's identity: two includes of
different pages in one PDF must not share a store entry. The generic fold
visits every document region, including furniture. -/
private def imageRequestPush (out : Array Image.Request) : Inline → Array Image.Request
  | .image src spec _ =>
    let req := spec.request src
    if out.contains req then out else out.push req
  | .text _ | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _
  | .located _ _ | .role _ _ | .link _ _ | .label _ | .ref _ _ _ _ | .decorated _ _ | .fill
  | .hspace _ _ | .rule _ _ _ | .pageNumber | .pageCount | .linebreak _
  | .strut _ | .italicCorr _ | .onSteps _ _ | .altSteps _ _ _ | .icon _ _
  | .cite _ _ | .footnote _ _ => out

public def imageRequests (doc : Doc) : Array Image.Request :=
  foldDoc imageRequestPush #[] doc

/-- The image-source spelling of a boundary picture: an `.image` whose
source is this prefix plus the request's content hash. The driver fulfils
it from the boundary cache instead of the filesystem. -/
public def picSrcPrefix : String := "leantex-pic:"

/-- FNV-1a, two seeds, 32 hex digits. Over a picture body it is the
picture's identity (`pictureSrcs`, the image source); over the wrapped
request it is the boundary cache key — a content hash, so an unchanged
request never re-runs the tool and a changed one always does. -/
public def picHash (s : String) : String := Id.run do
  let hex (x : UInt64) : String := Id.run do
    let digits := "0123456789abcdef".toList
    let mut out := ""
    let mut v := x
    for _ in [0:16] do
      out := String.ofList [(digits[(v % 16).toNat]?.getD '0')] ++ out
      v := v / 16
    return out
  let fnv (seed : UInt64) : UInt64 := Id.run do
    let mut h := seed
    for byte in s.toUTF8 do
      h := (h ^^^ byte.toUInt64) * 1099511628211
    return h
  return hex (fnv 14695981039346656037) ++ hex (fnv 1099511628211)

/-- xcolor's name grammar: a colour name is a maximal run of ASCII letters
and digits. Every such run of a picture body, deduplicated in first-seen
order. The over-approximation — a prose word spelled like a palette role
— costs one harmless `\definecolor`, and is what keeps this a total
tokenizer rather than a TikZ option parser. -/
private def colorNamesFlush (cur : String) (acc : Array String) : Array String :=
  if cur.isEmpty || acc.contains cur then acc else acc.push cur

private def colorNamesGo : List Char → String → Array String → Array String
  | [], cur, acc => colorNamesFlush cur acc
  | c :: rest, cur, acc =>
    if c.isAlphanum then colorNamesGo rest (cur.push c) acc
    else colorNamesGo rest "" (colorNamesFlush cur acc)

public def colorNames (body : String) : Array String := colorNamesGo body.toList "" #[]

/-- The palette roles a picture body mentions, each with the palette's
value: exactly the names the body spells that the palette resolves
(`paletteDecls_covers`, `_mem`), read from the same palette both backends
read through `Design.ofDoc` (`paletteDecls_agree`). -/
public def paletteDecls (pal : Palette) (body : String) : Array (String × Color) :=
  (colorNames body).filterMap fun n => (pal.find? n).map (n, ·)

/-- A CMYK component in thousandths as xcolor's `0`–`1` real, shortest
spelling (`0`, `0.83`, `1`). -/
public def cmykPart (v : Nat) : String :=
  if v = 0 then "0"
  else if v ≥ 1000 then "1"
  else
    let s := toString v
    let padded := "".pushn '0' (3 - s.length) ++ s
    "0." ++ String.ofList (padded.toList.reverse.dropWhile (· == '0')).reverse

/-- One palette role as the `\definecolor` the boundary tool reads. An
explicit source model keeps its exact validated components; computed/native
colours fall back to the model carried by the IR. -/
public def colorDeclLine : String × Color → String
  | (n, c) => match c.pdfModel with
    | some (.rgb r g b) => s!"\\definecolor\{{n}}\{rgb}\{{r},{g},{b}}\n"
    | some (.gray v) => s!"\\definecolor\{{n}}\{gray}\{{v}}\n"
    | some (.cmyk cy m y k) => s!"\\definecolor\{{n}}\{cmyk}\{{cy},{m},{y},{k}}\n"
    | none => match c.cmyk with
      | some (cy, m, y, k) =>
        s!"\\definecolor\{{n}}\{cmyk}\{{cmykPart cy},{cmykPart m},{cmykPart y},{cmykPart k}}\n"
      | none => s!"\\definecolor\{{n}}\{RGB}\{{c.r},{c.g},{c.b}}\n"

/-- The document's declared font roles, projected into the standalone's
preamble: fontspec's `\setmainfont`/`\setsansfont`/`\setmonofont` for the
body, sans and mono families, and `unicode-math`'s `\setmathfont` for the
math face — so a picture's text and formulas set in the page's own faces
(`pictureRefs_design_projects`). A family declared as a file name resolves
against the document's font dir, which the boundary tool cannot see from
its build directory; only a named family travels. -/
public def fontLines (fonts : FontSpec) : String :=
  let named (f : Option String) : Option String := f.filter fun fam =>
    !(fam.endsWith ".ttf" || fam.endsWith ".otf" || fam.endsWith ".ttc")
  let role (cmd : String) (f : Option String) : String :=
    match named f with
    | some fam => s!"\\{cmd}\{{fam}}\n"
    | none => ""
  let faces := role "setmainfont" fonts.body ++ role "setsansfont" fonts.sans ++
    role "setmonofont" fonts.mono
  let math := match named fonts.math with
    | some fam =>
      let opts := fonts.mathSources.options
      let load := if opts.isEmpty then "\\usepackage{unicode-math}\n"
        else s!"\\usepackage[{String.intercalate "," opts.toList}]\{unicode-math}\n"
      load ++ s!"\\setmathfont\{{fam}}\n"
    | none => ""
  if faces.isEmpty && math.isEmpty then "" else "\\usepackage{fontspec}\n" ++ faces ++ math

/-- TeX's control-word grammar (TeXbook ch. 7): a backslash and the
maximal run of letters after it. Every such name a stretch of source
spells, deduplicated in first-seen order. The over-approximation — a name
inside a comment or a verbatim run — costs one harmless definition, and is
what keeps this a total tokenizer rather than a TeX mouth, the same trade
`colorNames` makes for xcolor's name grammar. -/
private def ctrlNamesFlush (cur : Option String) (acc : Array String) : Array String :=
  match cur with
  | none => acc
  | some n => if n.isEmpty || acc.contains n then acc else acc.push n

private def ctrlNamesGo : List Char → Option String → Array String → Array String
  | [], cur, acc => ctrlNamesFlush cur acc
  | c :: rest, some n, acc =>
    if c.isAlpha then ctrlNamesGo rest (some (n.push c)) acc
    else ctrlNamesGo rest (if c == '\\' then some "" else none) (ctrlNamesFlush (some n) acc)
  | c :: rest, none, acc =>
    ctrlNamesGo rest (if c == '\\' then some "" else none) acc

public def ctrlNames (src : String) : Array String := ctrlNamesGo src.toList none #[]

/-- Consume each reachable declaration once, adding the names its body
spells. Removing the declaration supplies the termination measure, including
cycles and repeated names; no round budget stands in for closure.
`macroReachNames_contract` states both root retention and closure. -/
public def macroReachNames (pending : List (String × String)) (ns : Array String) : Array String :=
  match _h : pending.find? (fun p => ns.contains p.1) with
  | none => ns
  | some p => macroReachNames (pending.erase p) (ns ++ ctrlNames p.2)
termination_by pending.length
decreasing_by
  have hp := List.mem_of_find?_eq_some _h
  rw [List.length_erase_of_mem hp]
  have hn := List.length_pos_of_mem hp
  omega

/-- The document's own macro definitions a picture body reaches: every
definition whose name the body spells, and transitively every definition
those bodies spell, in document order. The reachable set rather than all of
them, for the reason the palette arm filters too (`paletteDecls_mem`): a
document's definition of a name TeX or TikZ already owns is the picture's
to see only where the picture asks for it, and the cache key then moves
only when a definition the picture reads moves. -/
public def macroDecls (macros : Array (String × String)) (body : String) : Array (String × String) :=
  let ns := macroReachNames macros.toList (ctrlNames body)
  macros.filter fun p => ns.contains p.1

/-- The carried definitions as the standalone's preamble reads them, one
per line. -/
public def macroDeclLines (macros : Array (String × String)) : String :=
  macros.foldl (fun s p => s ++ p.2 ++ "\n") ""

/-- Wrap one picture body for the boundary: `\documentclass{standalone}`,
the preamble declarations a standalone needs (package loads and set lines,
collected from the document), the document's font roles (`fontLines`), the
palette roles the request mentions (`paletteDecls`, as `colorDeclLine`s),
the document's own macro definitions the body reaches (`macroDecls`), and
the picture as written. The macros come last in the preamble: a document
that defined a name defined it for its own pictures too, whatever the
packages above spell. The request is a pure function of the document: two
runs over one document state byte-identical requests, so the cache key
means something. Determinism here is definitional — no theorem states a
pure function's purity, and `boundaryChecks` checks the bytes agree. -/
public def wrapStandalone (preamble fonts : String) (colors : Array (String × Color))
    (macros : Array (String × String)) (body : String) : String :=
  "\\documentclass{standalone}\n\\usepackage{tikz}\n" ++ preamble ++ fonts ++
    colors.foldl (fun s c => s ++ colorDeclLine c) "" ++ macroDeclLines macros ++
    "\\begin{document}\n\\begin{tikzpicture}" ++ body ++
    "\\end{tikzpicture}\n\\end{document}\n"

/-- The request one picture body states, formed from the finished
document: the driver calls `pictureRefs` after contrast realization, so a
role the realizer moved is moved in the picture too — the picture's
`alert` is the page's `alert`. The carried preamble and the body are both
dependency roots: a TikZ style can name a macro or colour that the body
never spells. The colour scan also reads every reachable macro definition,
so the same closure that makes a macro travel makes its colours travel. -/
public def pictureRequest (doc : Doc) (body : String) : String :=
  let roots := doc.picturePreamble ++ body
  let macros := macroDecls doc.pictureMacros roots
  wrapStandalone doc.picturePreamble (fontLines doc.fonts)
    (paletteDecls doc.palette (macroDeclLines macros ++ roots)) macros body

/-- The boundary requests the shipped tree actually states: `pictureSrcs`
filtered to the ids an `.image` node still references — a picture pruned
with its frame asks for nothing, exactly as a pruned `\bibliography` does
— each wrapped at this site (`pictureRequest`), so the request reads the
document's design as both backends do. -/
public def pictureRefs (doc : Doc) : Array (String × String) :=
  let srcs := imageRefs doc
  (doc.pictureSrcs.filter fun (h, _) => srcs.contains (picSrcPrefix ++ h)).map
    fun (h, body) => (h, pictureRequest doc body)

/-- **Referenced roles are covered.** A name the body spells that the
palette resolves is declared in the request, with the palette's value. -/
public theorem paletteDecls_covers (pal : Palette) (body n : String) (c : Color)
    (hn : n ∈ colorNames body) (hc : pal.find? n = some c) :
    (n, c) ∈ paletteDecls pal body := by
  unfold paletteDecls
  rw [Array.mem_filterMap]
  exact ⟨n, hn, by simp [hc]⟩

/-- **The picture's colour is the page's.** Every value the standalone
defines for a name is the value `Palette.find?` answers — the one read
`Design.ofDoc` makes for both backends. -/
public theorem paletteDecls_agree (pal : Palette) (body n : String) (c : Color)
    (h : (n, c) ∈ paletteDecls pal body) : pal.find? n = some c := by
  unfold paletteDecls at h
  rw [Array.mem_filterMap] at h
  obtain ⟨m, _, hm⟩ := h
  cases hf : pal.find? m with
  | none => simp [hf] at hm
  | some c' =>
    simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hf

/-- **Exactly the mentioned names.** No role rides that the body does not
spell — the locality of the cache key (`paletteDecls_local_exact`) rests
on it. -/
public theorem paletteDecls_mem (pal : Palette) (body n : String) (c : Color)
    (h : (n, c) ∈ paletteDecls pal body) : n ∈ colorNames body := by
  unfold paletteDecls at h
  rw [Array.mem_filterMap] at h
  obtain ⟨m, hm, he⟩ := h
  cases hf : pal.find? m with
  | none => simp [hf] at he
  | some c' =>
    simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact hm

private theorem filterMap_congr_mem {α β : Type} (f g : α → Option β) : ∀ (l : List α),
    (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons]
    rw [h a (List.mem_cons_self ..),
      filterMap_congr_mem f g l fun x hx => h x (List.mem_cons.mpr (Or.inr hx))]

/-- **An unrelated palette edit leaves the request untouched.** Two
palettes agreeing on every name the body spells produce one declaration
list — so the request, hence the boundary cache key, moves only when a
role the picture mentions moves. -/
public theorem paletteDecls_local_exact (pal pal' : Palette) (body : String)
    (h : ∀ n ∈ colorNames body, pal.find? n = pal'.find? n) :
    paletteDecls pal body = paletteDecls pal' body := by
  unfold paletteDecls
  apply Array.ext'
  simp only [Array.toList_filterMap]
  apply filterMap_congr_mem
  intro n hn
  rw [h n (Array.mem_def.mpr hn)]

/-- Every root remains, and every reached declaration's dependencies remain.
The step consumes one declaration; it covers that declaration from the new
roots and every other declaration from the remaining worklist. -/
public theorem macroReachNames_contract (pending : List (String × String)) (ns : Array String) :
    (∀ n ∈ ns, n ∈ macroReachNames pending ns) ∧
    (∀ p ∈ pending, p.1 ∈ macroReachNames pending ns →
      ∀ n ∈ ctrlNames p.2, n ∈ macroReachNames pending ns) := by
  induction pending, ns using macroReachNames.induct with
  | case1 pending ns h =>
    rw [macroReachNames, h]
    refine ⟨fun _ h => h, ?_⟩
    intro p hp hn
    exact False.elim ((List.find?_eq_none.mp h p hp) (Array.contains_iff_mem.mpr hn))
  | case2 pending ns p h ih =>
    rw [macroReachNames, h]
    refine ⟨fun n hn => ih.1 n (Array.mem_append_left _ hn), ?_⟩
    intro q hq hn n hdep
    by_cases he : q = p
    · subst q
      exact ih.1 n (Array.mem_append_right _ hdep)
    · exact ih.2 q ((List.mem_erase_of_ne he).mpr hq) hn n hdep

/-- **A definition the picture spells is carried.** A control sequence the
body spells that the document itself defined is declared in the request the
wrapper produces — the closure property the preamble's closed list could
not have: a list closed over the commands the engine knows cannot hold a
name the document invented, so the boundary tool met an undefined control
sequence and drew nothing. `macroDecls_fixed_point` supplies the transitive
half for definitions reached only through another carried definition. -/
public theorem macroDecls_covers (macros : Array (String × String)) (body n d : String)
    (hn : n ∈ ctrlNames body) (hm : (n, d) ∈ macros) :
    (n, d) ∈ macroDecls macros body := by
  simp only [macroDecls]
  refine Array.mem_filter.mpr ⟨hm, ?_⟩
  exact Array.contains_iff_mem.mpr
    ((macroReachNames_contract macros.toList (ctrlNames body)).1 n hn)

/-- The carried definitions are closed under reference: a definition whose
name another carried definition spells is carried too. This holds for every
declaration array, including cycles and repeated names. -/
public theorem macroDecls_fixed_point (macros : Array (String × String)) (body n d : String)
    (hm : (n, d) ∈ macros)
    (hr : ∃ p ∈ macroDecls macros body, n ∈ ctrlNames p.2) :
    (n, d) ∈ macroDecls macros body := by
  obtain ⟨p, hp, hn⟩ := hr
  simp only [macroDecls] at hp ⊢
  obtain ⟨hm', hp⟩ := Array.mem_filter.mp hp
  refine Array.mem_filter.mpr ⟨hm, Array.contains_iff_mem.mpr ?_⟩
  exact (macroReachNames_contract macros.toList (ctrlNames body)).2 p
    (Array.mem_def.mp hm') (Array.contains_iff_mem.mp hp) n hn

/-- **Only the document's own definitions ride.** Nothing reaches the
boundary that the document did not declare: the request's macro block is
drawn from `pictureMacros`, so the standalone can shadow a package's
command only where the document shadowed it first. -/
public theorem macroDecls_mem (macros : Array (String × String)) (body : String)
    (p : String × String) (h : p ∈ macroDecls macros body) : p ∈ macros :=
  (Array.mem_filter.mp h).1

/-- **The boundary request projects the document's design.** Every
request `pictureRefs` states is one picture body of `pictureSrcs`
wrapped with the document's preamble, its declared font roles
(`fontLines doc.fonts`), the palette roles the request mentions
(`paletteDecls doc.palette`) and the macro definitions its preamble and
body reach (`macroDecls doc.pictureMacros`) — the same `fonts` and `palette`
both backends read through `Design.ofDoc`. No backend theorem stands behind
this one: the PDF embeds the tool's drawing and the HTML embeds a
rasterization of the same drawing — one fulfilment, two projections. -/
public theorem pictureRefs_design_projects (doc : Doc) (id w : String)
    (h : (id, w) ∈ pictureRefs doc) :
    ∃ body, (id, body) ∈ doc.pictureSrcs ∧
      w = wrapStandalone doc.picturePreamble (fontLines doc.fonts)
        (paletteDecls doc.palette
          (macroDeclLines (macroDecls doc.pictureMacros (doc.picturePreamble ++ body)) ++
            (doc.picturePreamble ++ body)))
        (macroDecls doc.pictureMacros (doc.picturePreamble ++ body)) body := by
  unfold pictureRefs at h
  rw [Array.mem_map] at h
  obtain ⟨⟨id', body⟩, hmem, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨body, (Array.mem_filter.mp hmem).1, rfl⟩

/-- **The boundary request is environment-free.** What a document requests
at the boundary (`pictureRefs`) is a function of the document alone — the
picture bodies, the shipped tree, and the document's own design (its
preamble lines, font roles and palette, all declaration values) — never
of the fulfilment side: repinning the tool field leaves every request
untouched. The other half of the statement is structural, not provable
here: the request is formed in the pure core (`Elab`'s picture arm routes
on the door's presence — a declaration value — and
`wrapStandalone`/`picHash` take no tool), which cannot read PATH, so
whether a tool exists on the machine decides *fulfilment* only — run,
serve from the warm cache, or W0379 (`Main.resolvePictures`) — and, for a
picture the rendered subset draws in part, withdrawal: a request no tool
drew is withdrawn and a second elaboration draws that picture natively
(`Cli.Boundary.withdraw`). Every request is still stated by the first
elaboration, from the document alone. The
executable half — pinning the default tool elaborates to the identical
`Doc` — runs in `boundaryChecks`. -/
public theorem boundary_request_env_free (doc : Doc) (t : Option String) :
    pictureRefs { doc with pictureTool := t } = pictureRefs doc := by rfl

-- The logo: one resolving site for its state sequence and its alignment,
-- read by both backends.

/-- The logo in force at position `k` of a keyed declaration sequence: the
last span whose key is at or before `k`, else the initial state `init` (the
preamble `\logo`) — beamer's stateful declaration, where an empty body
clears (`\logo{}` after a frame is how a deck scopes a logo to one frame).
The one resolving site: the PDF's furniture pass keys the spans by page
index and reads each page's logo here, and the HTML deck walk keys them by
body position and reads each frame's logo here — never a second
interpretation of the sequence (`logo_frames_agree`). -/
public def logoInForce (init : Option (Array Inline))
    (spans : Array (Nat × Array Inline)) (k : Nat) : Option (Array Inline) :=
  spans.foldl (fun acc s => if s.1 ≤ k then some s.2 else acc) init

/-- The list spine of `logo_frames_agree`: the fold reads a key only
through its comparison against the read point, so any rekeying that
preserves those comparisons preserves the fold. -/
private theorem logoInForceList_rekey (f : Nat → Nat) (k : Nat) :
    ∀ (l : List (Nat × Array Inline)),
      (∀ s ∈ l, (f s.1 ≤ f k) ↔ (s.1 ≤ k)) →
      ∀ (init : Option (Array Inline)),
        l.foldl (fun acc s => if f s.1 ≤ f k then some s.2 else acc) init =
          l.foldl (fun acc s => if s.1 ≤ k then some s.2 else acc) init := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons s rest ih =>
    intro h init
    simp only [List.foldl_cons]
    have hs := h s (List.mem_cons_self ..)
    have hrest := fun t ht => h t (List.mem_cons_of_mem _ ht)
    simp only [hs]
    exact ih hrest _

/-- The cross-backend agreement, stated over the shared resolving function:
`logoInForce` is invariant under any rekeying that preserves each
declaration's position relative to the read point. The PDF keys the spans
by page index and reads at a page; the HTML deck keys the same declarations
by body position and reads at a frame — the map from body position to page
index preserves order against every declaration (a `\logo` before a frame
is placed before the frame's page opens, a clear after it only after the
page closed), so the two projections resolve the same state, frame for
page. The artifact-level census over a deck (Tests, `deckLogoChecks`)
holds the rendered halves to this. -/
public theorem logo_frames_agree (init : Option (Array Inline))
    (spans : Array (Nat × Array Inline)) (f : Nat → Nat) (k : Nat)
    (h : ∀ s ∈ spans, (f s.1 ≤ f k) ↔ (s.1 ≤ k)) :
    logoInForce init (spans.map fun s => (f s.1, s.2)) (f k) =
      logoInForce init spans k := by
  unfold logoInForce
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map,
    List.foldl_map]
  exact logoInForceList_rekey f k spans.toList
    (fun s hs => h s (by simpa using hs)) init

/-- The logo's declared alignment in the furniture band — the one resolving
site both backends read: the document's `\style{logo}{ align = ... }`,
else `right`, the beamer default placement the engine keeps (beamer's
default outer theme hangs `\insertlogo` at the lower-right corner:
beamerouterthemedefault.sty, the `sidebar right` template's
`\llap{\insertlogo\hskip0.1cm}` at the sidebar's bottom). Vertical
placement is not a knob: the logo rides the furniture band at the page
bottom, as the foot does. -/
public def logoAlign (styles : Styles) : String :=
  ((styles.find? "logo").bind (·.align)).getD "right"

/-- Every image source the logo state ships — the preamble `\logo` and each
body declaration's content. A logo is decorative furniture by role
(WCAG 2.2 SC 1.1.1: content that is pure decoration needs no text
alternative and is implemented so assistive technology can ignore it — the
HTML backend ships `alt=""` on these), so the no-alternative census counts
these sources as decorative, never as missing. -/
public def logoImageSrcs (doc : Doc) : Array String :=
  let out := foldBlocks (fun out b => match b with
    | .logo c => imageSrcsInlines out c
    | _ => out) (fun out _ => out) #[] doc.body
  let out := match doc.logo with | some l => imageSrcsInlines out l | none => out
  let out := match doc.logoLeft with | some l => imageSrcsInlines out l | none => out
  match doc.logoRight with | some r => imageSrcsInlines out r | none => out

private structure SansAltCensus where
  missing : Array String := #[]
  pictures : Nat := 0

/-- One image node's contribution to the no-alternative census: an
`.image` whose `alt` is `.undeclared`, its `src` collected once — a
`.decorative` image is the conforming state (WCAG 2.2 SC 1.1.1: pure
decoration, implemented so assistive technology can ignore it). A leaf
projection of the shared fold — the fold recurses, so this leaf reads
only the node itself; `imageSrcPush`'s shape. -/
private def sansAltStep (out : SansAltCensus) (x : Inline) : SansAltCensus :=
  match x with
  | .image src _ alt =>
    if alt == .undeclared && !out.missing.contains src then
      { out with missing := out.missing.push src }
    else out
  | _ => out

/-- The census key of a native picture: `picture#k`, where `k` is its
index among all native pictures in document order. Counting every native
picture keeps the key stable when a later caption fills its alternative. -/
public def picKeyPrefix : String := "picture#"

/-- One native picture's contribution to the no-alternative census. The
artifact-facing `alternative` is judged, so label words and a caption both
satisfy the same value the HTML and PDF project. -/
private def sansAltPicStep (out : SansAltCensus) (b : Block) : SansAltCensus :=
  match b with
  | .picture pic =>
    let key := picKeyPrefix ++ toString out.pictures
    { missing := if pic.alternative == .undeclared then out.missing.push key else out.missing
      pictures := out.pictures + 1 }
  | _ => out

/-- Every non-text object the artifacts ship with no text alternative,
deduplicated by source for images and keyed by native-picture position, in
document order. The backends read the body and the running head and foot,
so the census reads the same regions (`imageRefs`' scope for shipped ink).
A figure's caption has already become its object's `alt` by elaboration
(`setAltBlocks`), so a captioned figure is not counted — and a logo's
images are not counted either: a logo is decorative furniture by role
(`logoImageSrcs`), so its missing alternative is the conforming state,
never a defect. A native picture (`picKeyPrefix`) is judged with file
images (`altDiags`). A boundary picture (`picSrcPrefix`) is counted too —
the route changes who drew the box, not what an accessibility reader gets —
but judged after fulfilment by `picAltDiags`. The two faces partition this
census (`alt_judged_complete`); N0023 names trust, not loss. -/
public def imagesSansAlt (doc : Doc) : Array String :=
  let out := foldBlocks sansAltPicStep sansAltStep {} doc.body
  let out := match doc.head with | some h => foldInlines sansAltStep out h | none => out
  let out := match doc.foot with | some f => foldInlines sansAltStep out f | none => out
  out.missing.filter (fun src => !(logoImageSrcs doc).contains src)

/-- The picture faces' one message and help, native and boundary alike.
The key is an internal census identity, so the message stays in the
author's words and names every available declaration. -/
public def pictureSansAltMessage : String :=
  "this picture ships no text alternative; assistive technology " ++
    "reads nothing in its place (WCAG 2.2 SC 1.1.1)"

public def pictureSansAltHelp : String :=
  "describe the picture — \\begin{tikzpicture}[alt={...}] — mark it " ++
    "decorative with [artifact], or caption a figure around it; an empty " ++
    "alt= says nothing"

/-- The text-alternative judge's file-image and native-picture face (WCAG
2.2 SC 1.1.1, Non-text Content). One diagnostic per distinct object; a
file source or native-picture key provides the structured subject and its
recorded span. The caller attributes the written trigger from source
evidence; the IR judge invents no surface spelling. Boundary pictures are
judged by `picAltDiags` after the driver has fulfilled them. -/
public def altDiags (doc : Doc) (spanOf : String → Option Span := fun _ => none) :
    Array Diag :=
  ((imagesSansAlt doc).filter fun src => !src.startsWith picSrcPrefix).map fun src =>
    let span := spanOf src
    if src.startsWith picKeyPrefix then
      Diag.of .N0376 pictureSansAltMessage span
        (help := some pictureSansAltHelp) (subject := some src)
    else
      Diag.of .N0376
        (s!"image '{src}' ships no text alternative; assistive technology " ++
          "reads nothing in its place (WCAG 2.2 SC 1.1.1)")
        span
        (help := some ("describe the image — \\includegraphics[alt={...}] — " ++
          "mark it decorative with [artifact], or caption its figure: the " ++
          "caption becomes the alternative"))
        (subject := some src)

/-- The judge's boundary-picture face, read by the driver after fulfilment:
`shipped` says whether the picture's drawn box embeds — a picture the tool
failed on ships a placeholder box, not an image, and E0382 has named that
loss, so naming it here too would name one loss twice. -/
public def picAltDiags (doc : Doc) (spanOf : String → Option Span)
    (shipped : String → Bool) : Array Diag :=
  ((imagesSansAlt doc).filter fun src =>
      src.startsWith picSrcPrefix && shipped src).map fun src =>
    let span := spanOf src
    Diag.of .N0376 pictureSansAltMessage span
      (help := some pictureSansAltHelp) (subject := some src)

private theorem length_filter_partition (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter (fun a => !p a)).length = l.length
  | [] => rfl
  | a :: l => by
    have ih := length_filter_partition p l
    cases h : p a <;> simp [h] <;> omega

private theorem size_filter_partition (p : α → Bool) (as : Array α) :
    (as.filter (fun a => !p a)).size + (as.filter p).size = as.size := by
  have h1 := congrArg List.length (Array.toList_filter (p := fun a => !p a) (xs := as))
  have h2 := congrArg List.length (Array.toList_filter (p := p) (xs := as))
  have h3 := length_filter_partition p as.toList
  simp only [Array.length_toList] at h1 h2 h3
  omega

/-- The two faces judge exactly the census, together: every shipped image
with no text alternative is named by the file-image face or the picture
face (with every picture shipped), and by only one. An image cannot
escape without escaping the fold whose arms are all explicit — weak
accessibility of images is a reported fact, never a discovery. -/
public theorem alt_judged_complete (doc : Doc) (spanOf : String → Option Span) :
    (altDiags doc spanOf).size + (picAltDiags doc spanOf (fun _ => true)).size =
      (imagesSansAlt doc).size := by
  rw [altDiags, picAltDiags, Array.size_map, Array.size_map]
  simp only [Bool.and_true]
  exact size_filter_partition (fun src => src.startsWith picSrcPrefix)
    (imagesSansAlt doc)

/-- The text a link's body offers the accessibility tree: its plain text
(icon labels and reference texts included, as `plainTextOne` reads them)
together with each contained image's declared alternative — WCAG 2.2
SC 2.4.4 takes a link's purpose from its link text, and technique H30
names the `alt` of an image inside the link as that text. -/
public def linkReading (body : Array Inline) : String :=
  foldInlines
    (fun s x => match x with | .image _ _ alt => s ++ alt.text | _ => s)
    (plainText body) body

/-- One link node's contribution to the no-text census: a `.link` whose
body reads as nothing (`linkReading`), its target collected once. A leaf
projection of the shared fold, `sansAltStep`'s shape — the fold visits
the `.link` node itself before its body, so no link escapes the census
without escaping the fold, whose arms are all explicit. -/
private def sansTextLinkStep (out : Array String)
    (x : Inline) : Array String :=
  match x with
  | .link url body =>
    if (linkReading body).isEmpty && !out.contains url then out.push url
    else out
  | _ => out

private def sansTextBlockLinkStep (out : Array String)
    (b : Block) : Array String :=
  match b with
  | .link target body =>
    if (blockLinkReading body).isEmpty && !out.contains target then out.push target else out
  | .para _ | .equation _ _ | .section _ _ _ _ | .list _ _ | .center _ | .ragged _ _
  | .spaced _ _ | .role _ _ | .quote _ | .abstract _ | .titled _ _ _ | .verbatim _ _ _
  | .algorithm _ _ _ | .columns _ | .onSteps _ _ | .altSteps _ _ _ | .note _ | .only _ _
  | .nav _ _ | .logo _ | .pagebreak | .frame _ _ _ _ _ | .framefoot _ | .setPalette _
  | .setTokens _ | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ | .float _ _ _ _ _
  | .bibliography _ _ _ => out

/-- Every link the artifacts ship with no reading — no text, no icon
label, no image alternative — deduplicated by target, in document order:
the backends read the body, the running head and foot, and the logo, so
the census reads the same regions (`imageRefs`' scope for shipped ink). -/
public def linksSansText (doc : Doc) : Array String :=
  let out := foldBlocks sansTextBlockLinkStep sansTextLinkStep #[] doc.body
  let out := match doc.head with | some h => foldInlines sansTextLinkStep out h | none => out
  let out := match doc.foot with | some f => foldInlines sansTextLinkStep out f | none => out
  match doc.logo with | some l => foldInlines sansTextLinkStep out l | none => out

/-- The link-purpose judge (WCAG 2.2 SC 2.4.4, Link Purpose (In Context):
the purpose of each link can be determined from the link text; sufficient
technique H30). One diagnostic per distinct target: a link a reader can
follow and an assistive reader cannot name is a per-link fact, and the
target names which. -/
public def linkDiags (doc : Doc) : Array Diag :=
  (linksSansText doc).map fun url =>
    Diag.of .W0377
      (s!"link '{url}' carries no text; assistive technology reads " ++
        "nothing to name its purpose (WCAG 2.2 SC 2.4.4)")
      (help := some ("give the link visible text — \\href{...}{words} — " ++
        "or an image with alt inside it"))

/-- The judge is silent exactly when no shipped link lacks a reading:
`linkDiags` is a per-offender map over the census (`linksSansText`, a
leaf projection of the shared fold), so an unnameable link is a reported
fact, never a discovery — `alt_judged_complete`'s shape. -/
public theorem links_judged_complete (doc : Doc) :
    linkDiags doc = #[] ↔ linksSansText doc = #[] := by
  rw [← Array.size_eq_zero_iff, ← Array.size_eq_zero_iff, linkDiags,
    Array.size_map]

mutual

/-- One leaf-parameterised map hosts every leaf rewrite over the tree.
`f` rewrites childless nodes. `finish` combines a completed sibling array,
after its children have been mapped, so a transparent wrapper can be
spliced out without a second structural walk. The default keeps every
wrapper and sibling unchanged. -/
@[expose] public def mapInlines (f : Inline → Inline) (xs : Array Inline)
    (finish : Array Inline → Array Inline := id) : Array Inline :=
  mapInlineList f #[] xs.toList finish

@[expose] public def mapInlineList (f : Inline → Inline) (out : Array Inline) (xs : List Inline)
    (finish : Array Inline → Array Inline := id) : Array Inline :=
  match xs with
  | [] => finish out
  | x :: rest => mapInlineList f (out.push (mapInline f x finish)) rest finish

@[expose] public def mapInline (f : Inline → Inline) (x : Inline)
    (finish : Array Inline → Array Inline := id) : Inline :=
  match x with
  | .styled st body => .styled st (mapInlineList f #[] body.toList finish)
  | .colored c n body => .colored c n (mapInlineList f #[] body.toList finish)
  | .located span body => .located span (mapInlineList f #[] body.toList finish)
  | .role n body => .role n (mapInlineList f #[] body.toList finish)
  | .link u body => .link u (mapInlineList f #[] body.toList finish)
  | .decorated kind body => .decorated kind (mapInlineList f #[] body.toList finish)
  | .onSteps spec body => .onSteps spec (mapInlineList f #[] body.toList finish)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (mapInlineList f #[] firstPage.toList finish)
      (mapInlineList f #[] otherPage.toList finish)
  | .footnote n body => .footnote n (mapInlineList f #[] body.toList finish)
  | .text s => f (.text s)
  | .math d src => f (.math d src)
  | .formula d src body => f (.formula d src body)
  | .image src size alt => f (.image src size alt)
  | .icon s l => f (.icon s l)
  | .label k => f (.label k)
  | .ref k p t tg => f (.ref k p t tg)
  | .cite tx keys => f (.cite tx keys)
  | .fill => f .fill
  | .hspace g keep => f (.hspace g keep)
  | .rule w h r => f (.rule w h r)
  | .strut h => f (.strut h)
  | .italicCorr m => f (.italicCorr m)
  | .pageNumber => f .pageNumber
  | .pageCount => f .pageCount
  | .linebreak e => f (.linebreak e)

end

@[expose] public def mapTableCells (f : Inline → Inline) (out : Array (Array Inline))
    (cells : List (Array Inline)) (finish : Array Inline → Array Inline := id) :
    Array (Array Inline) :=
  match cells with
  | [] => out
  | cell :: rest =>
    mapTableCells f (out.push (mapInlines f cell finish)) rest finish

@[expose] public def mapTableRows (f : Inline → Inline) (out : Array (Array (Array Inline)))
    (rows : List (Array (Array Inline))) (finish : Array Inline → Array Inline := id) :
    Array (Array (Array Inline)) :=
  match rows with
  | [] => out
  | row :: rest =>
    mapTableRows f (out.push (mapTableCells f #[] row.toList finish)) rest finish

@[expose] public def mapBibItems (f : Inline → Inline) (out : Array BibItem) (items : List BibItem)
    (finish : Array Inline → Array Inline := id) : Array BibItem :=
  match items with
  | [] => out
  | i :: rest =>
    mapBibItems f (out.push { i with content := mapInlines f i.content finish }) rest finish

@[expose] public def mapAlgLines (f : Inline → Inline) (out : Array AlgLine) (ls : List AlgLine)
    (finish : Array Inline → Array Inline := id) : Array AlgLine :=
  match ls with
  | [] => out
  | l :: rest =>
    mapAlgLines f (out.push
      { depth := l.depth
        kind := l.kind
        content := mapInlines f l.content finish
        comment := l.comment.map (mapInlines f · finish) }) rest finish

mutual

/-- The block face of the generic map: `gp` rewrites native pictures, `f`
childless inlines, `finish` completed inline regions, and `listing` the
listing specification after its caption is mapped. Every block wrapper
keeps its shape and ordering. Existing leaf-only callers use the identity
defaults; annotation erasure uses the same descent. -/
@[expose] public def mapBlocksPic (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (xs : Array Block) (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Array Block :=
  mapBlockList gp f #[] xs.toList finish listing

/-- The generic map with every picture passed through untouched: a label's
inlines are not this map's leaves. A rewrite that must reach the text a
label paints — alphabet resolution, location erasure — maps labels through
`mapBlocksPic`; each caller of this one says why its rewrite need not. -/
@[expose] public def mapBlocks (f : Inline → Inline) (xs : Array Block)
    (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Array Block :=
  mapBlocksPic id f xs finish listing

@[expose] public def mapBlockList (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (out : Array Block) (bs : List Block) (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Array Block :=
  match bs with
  | [] => out
  | b :: rest =>
    mapBlockList gp f (out.push (mapBlock gp f b finish listing)) rest finish listing

@[expose] public def mapBlock (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline) (b : Block)
    (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Block :=
  match b with
  | .para content => .para (mapInlines f content finish)
  | .equation n content => .equation (mapInlines f n finish) (mapInlines f content finish)
  | .section l st n title => .section l st n (mapInlines f title finish)
  | .list o items => .list o (mapBlockItems gp f #[] items.toList finish listing)
  | .center body => .center (mapBlockList gp f #[] body.toList finish listing)
  | .ragged s body => .ragged s (mapBlockList gp f #[] body.toList finish listing)
  | .quote body => .quote (mapBlockList gp f #[] body.toList finish listing)
  | .abstract body => .abstract (mapBlockList gp f #[] body.toList finish listing)
  | .titled kind title body =>
    .titled kind (mapInlines f title finish) (mapBlockList gp f #[] body.toList finish listing)
  | .role n body => .role n (mapBlockList gp f #[] body.toList finish listing)
  | .link target body => .link target (mapBlockList gp f #[] body.toList finish listing)
  | .spaced g body => .spaced g (mapBlockList gp f #[] body.toList finish listing)
  | .columns cols => .columns (mapBlockCols gp f #[] cols.toList finish listing)
  | .onSteps spec body => .onSteps spec (mapBlockList gp f #[] body.toList finish listing)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (mapBlockList gp f #[] firstPage.toList finish listing)
      (mapBlockList gp f #[] otherPage.toList finish listing)
  | .only targets body => .only targets (mapBlockList gp f #[] body.toList finish listing)
  | .nav spec body => .nav spec (mapBlockList gp f #[] body.toList finish listing)
  | .note body => .note (mapBlockList gp f #[] body.toList finish listing)
  | .frame title st v br body =>
    .frame (mapInlines f title finish) st v br (mapBlockList gp f #[] body.toList finish listing)
  | .framefoot content => .framefoot (mapInlines f content finish)
  | .float k num ca body caption =>
    .float k num ca (mapBlockList gp f #[] body.toList finish listing)
      (mapInlines f caption finish)
  | .table c pl pr rows rules spans =>
    .table c pl pr (mapTableRows f #[] rows.toList finish) rules spans
  | .algorithm n sm ls => .algorithm n sm (mapAlgLines f #[] ls.toList finish)
  | .logo content => .logo (mapInlines f content finish)
  | .bibliography src style items =>
    .bibliography src style (mapBibItems f #[] items.toList finish)
  | .verbatim c s spec =>
    .verbatim c s (listing { spec with caption := spec.caption.map fun (n, cap) =>
      (n, mapInlines f cap finish) })
  | .setPalette pal => .setPalette pal
  | .setTokens tk => .setTokens tk
  | .pagebreak => .pagebreak
  | .rule c n th => .rule c n th
  | .picture pic => .picture (gp pic)

public def mapBlockItems (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (out : Array (Array Block)) (items : List (Array Block))
    (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Array (Array Block) :=
  match items with
  | [] => out
  | item :: rest =>
    mapBlockItems gp f (out.push (mapBlockList gp f #[] item.toList finish listing))
      rest finish listing

public def mapBlockCols (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (out : Array (BoxWidth × Array Block)) (cols : List (BoxWidth × Array Block))
    (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Array (BoxWidth × Array Block) :=
  match cols with
  | [] => out
  | (w, body) :: rest =>
    mapBlockCols gp f (out.push (w, mapBlockList gp f #[] body.toList finish listing))
      rest finish listing

end

/-- Resolve one formula leaf; every wrapper is owned by `mapInlines`, so the
leaf function cannot skip a title, caption, table cell, note, or furniture
region. -/
@[expose] public def resolveMathAlphaInline (coverage : Math.MathAlphabetCoverage) : Inline → Inline
  | .formula display src body =>
    .formula display src (Math.resolveMathAlphas coverage body)
  | .styled st body => .styled st body
  | .colored c n body => .colored c n body
  | .located n body => .located n body
  | .role n body => .role n body
  | .link u body => .link u body
  | .decorated kind body => .decorated kind body
  | .onSteps spec body => .onSteps spec body
  | .altSteps spec active otherwise => .altSteps spec active otherwise
  | .footnote n body => .footnote n body
  | .text s => .text s
  | .math display src => .math display src
  | .image src size alt => .image src size alt
  | .icon c label => .icon c label
  | .label key => .label key
  | .ref key form text target => .ref key form text target
  | .cite text keys => .cite text keys
  | .fill => .fill
  | .hspace g keep => .hspace g keep
  | .rule w h raise => .rule w h raise
  | .strut g => .strut g
  | .italicCorr maybe => .italicCorr maybe
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak extra => .linebreak extra

/-- A formula leaf is already resolved after one pass. -/
public theorem resolveMathAlphaInline_fixed_point (coverage : Math.MathAlphabetCoverage)
    (x : Inline) :
    resolveMathAlphaInline coverage (resolveMathAlphaInline coverage x) =
      resolveMathAlphaInline coverage x := by
  cases x <;> simp only [resolveMathAlphaInline, Math.resolveMathAlphas_fixed_point]

/-- The picture face of alphabet resolution. A label paints its formulas in
both backends — the face census asks glyphs for them — so they resolve as a
caption's do; skipping them shipped an unresolved alphabet node, which MathML
frames as an error and the page sets in the source glyphs. -/
@[expose] public def resolveMathAlphaPicture (coverage : Math.MathAlphabetCoverage)
    (pic : Pic.Picture) : Pic.Picture :=
  pic.mapLabels (mapInlines (resolveMathAlphaInline coverage))

/-- A formula and the authored location enclosing it. The canonical formula
text is not source evidence: the lexical trigger lives on the stored span. -/
public structure MathRequest where
  body : Math.MList
  source : Option Span

/-- The two existing consumers read different regions: alphabet resolution
rewrites notes and style templates, whereas face loading follows the painted
scalar census, which excludes them. Both read picture labels, whose formulas
both backends paint (`mathRequests_resolve_covers`). -/
public inductive MathRequestScope where
  | alphabets
  | face
  deriving BEq, DecidableEq

private def mathRequestInlines : CtxFold (Option Span × Bool) (Array MathRequest) where
  openBlock := fun ctx out _ => (out, ctx)
  closeBlock := fun _ out _ => out
  openInline := fun ctx out x => match x with
    | .located span _ => (out, (ctx.1.orElse (fun _ => some span), ctx.2))
    | .formula _ _ body =>
      (if ctx.2 then out.push ⟨body, ctx.1⟩ else out, ctx)
    | .text _ | .math _ _ | .styled _ _ | .colored _ _ _ | .role _ _
    | .link _ _ | .decorated _ _ | .onSteps _ _ | .altSteps _ _ _
    | .footnote _ _ | .image _ _ _ | .icon _ _ | .label _ | .ref _ _ _ _
    | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _
    | .pageNumber | .pageCount | .linebreak _ => (out, ctx)
  closeInline := fun _ out _ => out

/-- Entering a block for the request census: a note closes the face scope
over its content, and the block-owned regions `foldCtxBlock` does not descend
into — a listing caption, formatted references, picture labels — are read
here, under the block's context. -/
private def mathRequestOpen (scope : MathRequestScope) (ctx : Option Span × Bool)
    (out : Array MathRequest) (b : Block) : Array MathRequest × (Option Span × Bool) :=
  let read := foldCtxInlines mathRequestInlines ctx
  match b with
  | .note _ => (out, (ctx.1, ctx.2 && scope == .alphabets))
  | .verbatim _ _ spec =>
    (match spec.caption with
      | some (_, caption) => read out caption
      | none => out, ctx)
  | .bibliography _ _ items =>
    (items.foldl (fun acc item => read acc item.content) out, ctx)
  | .picture pic => (pic.labelContents.foldl read out, ctx)
  | .para _ | .equation _ _ | .section _ _ _ _ | .list _ _ | .center _
  | .ragged _ _ | .quote _ | .abstract _ | .titled _ _ _ | .role _ _
  | .link _ _ | .spaced _ _ | .columns _ | .onSteps _ _ | .altSteps _ _ _
  | .only _ _ | .nav _ _ | .frame _ _ _ _ _ | .framefoot _
  | .float _ _ _ _ _ | .table _ _ _ _ _ _ | .algorithm _ _ _ | .logo _
  | .setPalette _ | .setTokens _ | .pagebreak | .rule _ _ _ => (out, ctx)

private def mathRequestFold (scope : MathRequestScope) :
    CtxFold (Option Span × Bool) (Array MathRequest) :=
  { mathRequestInlines with openBlock := mathRequestOpen scope }

/-- Formula requests in the shared context fold's document order.
A location binds only its own descendants; siblings cannot
borrow it. Outermost locations retain a macro's authored call site.

The face scope reads the regions of `Layout.docMathScalars` — a corpus check
holds the two to one scalar set (`mathCensusRegionChecks`); the alphabet
scope is the regions `resolveMathAlphas` rewrites — body, furniture, notes,
style templates, listing captions, formatted references and picture labels
— and `missingMathAlphas` is defined over it. Holding the scope to the
rewrite is `mathRequests_resolve_covers` in one direction only: a region
the rewrite reaches and this fold misses resolves without a note. Neither
scope changes which formulas are resolved or request a face. -/
public def mathRequests (scope : MathRequestScope) (doc : Doc) : Array MathRequest :=
  let body := foldCtxBlocks (mathRequestFold scope) (none, true) #[] doc.body
  let furniture := match scope with
    | .alphabets => furnitureInlines doc
    | .face =>
      furnitureInlines.optRegion doc.head ++ furnitureInlines.optRegion doc.foot ++
        (match doc.headline with
          | some hl => #[hl.title, hl.author, hl.institute]
          | none => #[]) ++
        furnitureInlines.optRegion doc.logoLeft ++ furnitureInlines.optRegion doc.logoRight
  furniture.foldl (fun out xs => foldCtxInlines mathRequestInlines (none, true) out xs) body

/-- One request's missing alphabets onto a census that keeps first use
and drops repeats. -/
private def noteRequestAlphas (coverage : Math.MathAlphabetCoverage)
    (out : Array Math.MathAlphabet) (r : MathRequest) : Array Math.MathAlphabet :=
  (Math.missingMathAlphas coverage r.body).foldl (fun out a =>
    if out.contains a then out else out.push a) out

/-- Every alphabet whose used range the selected symbol face lacks over a
request census, deduplicated in first-use order. -/
public def missingAlphasOf (coverage : Math.MathAlphabetCoverage)
    (requests : Array MathRequest) : Array Math.MathAlphabet :=
  requests.foldl (noteRequestAlphas coverage) #[]

/-- Every alphabet whose used range the selected symbol face lacks,
deduplicated in first-use order over the alphabet census's requests — the
body and furniture, notes, style templates, listing captions, formatted
references and picture labels: the requests each note takes its source
from, so which alphabets are named and where cannot read two region lists. -/
public def missingMathAlphas (coverage : Math.MathAlphabetCoverage)
    (doc : Doc) : Array Math.MathAlphabet :=
  missingAlphasOf coverage (mathRequests .alphabets doc)

/-- The first actual formula needing glyphs, before a face is selected.
An unsourced request stays unsourced rather than borrowing a later site. -/
public def mathFaceRequest (doc : Doc) : Option MathRequest :=
  (mathRequests .face doc).find? fun r => !(Math.MList.scalarsList #[] r.body).isEmpty

/-- A selected face request belongs to the painted census and really asks
for at least one scalar; an empty formula cannot own the automatic-face note. -/
public theorem mathFaceRequest_covers (doc : Doc) (request : MathRequest)
    (h : mathFaceRequest doc = some request) :
    request ∈ mathRequests .face doc ∧
      (Math.MList.scalarsList #[] request.body).isEmpty = false := by
  refine ⟨Array.mem_of_find?_eq_some h, ?_⟩
  simpa using Array.find?_some h

/-- Resolve typed math-alphabet scopes in the shared IR before the scalar
fallback census and both backends. The returned diagnostics are one per
alphabet, never one per glyph; isolated holes in a supported range remain
mapped and therefore keep the ordinary per-character fallback path. -/
@[expose] public def resolveMathAlphas (coverage : Math.MathAlphabetCoverage) (family : String)
    (doc : Doc) : Doc × Array Diag :=
  let leaf := resolveMathAlphaInline coverage
  let resolved := mapDoc (mapInlines leaf)
    (mapBlocksPic (resolveMathAlphaPicture coverage) leaf) doc
  let requests := mathRequests .alphabets doc
  let diags := (missingAlphasOf coverage requests).map fun a =>
    let source := (requests.find? fun r =>
      (Math.missingMathAlphas coverage r.body).contains a).bind (·.source)
    Diag.of .N0018
      s!"'{family}' has no {a.styleLabel} alphabet for the characters used; ordinary math source glyphs stand"
      source
      (help := some "write \\fonts{ math = \"...\" } with a face that carries this alphabet")
      (subject := some ("math-alpha:" ++ a.name))
      (trigger := source.bind (·.pos.command))
  (resolved, diags)

/-- Every located alphabet note is witnessed by a formula in the sourced
census that actually lacks the named alphabet. An earlier supported formula
or a different alphabet's loss cannot supply its origin. -/
public theorem resolveMathAlphas_origin_covers (coverage : Math.MathAlphabetCoverage)
    (family : String) (doc : Doc) (d : Diag) (span : Span)
    (hd : d ∈ (resolveMathAlphas coverage family doc).2) (hs : d.span = some span) :
    ∃ a, a ∈ missingMathAlphas coverage doc ∧
      d.subject = some ("math-alpha:" ++ a.name) ∧
      ∃ request, request ∈ mathRequests .alphabets doc ∧
        request.source = some span ∧
          (Math.missingMathAlphas coverage request.body).contains a = true := by
  obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hd
  refine ⟨a, ha, ?_, ?_⟩
  · rw [Diag.of_record_exact]
  · rw [Diag.of_record_exact] at hs
    obtain ⟨request, hr, hsource⟩ := Option.bind_eq_some_iff.mp hs
    exact ⟨request, Array.mem_of_find?_eq_some hr, hsource,
      Array.find?_some (p := fun r : MathRequest =>
        (Math.missingMathAlphas coverage r.body).contains a) hr⟩

/-- The N0018 census is `_named`: `resolveMathAlphas` emits exactly one
diagnostic per missing alphabet, each carrying that alphabet's key as its
subject (`math-alpha:<name>`). Since `missingMathAlphas` is derived from the
same `remaps` the resolver keeps scalars by (`Math.missingCharAlpha_kept`),
the census cannot drift from what rendered: the IR owner is the single
subject-bearing owner of the whole-alphabet loss, and the per-character
Layout path (W0016) sees only remapped scalars this census never names. -/
public theorem resolveMathAlphas_named (coverage : Math.MathAlphabetCoverage)
    (family : String) (doc : Doc) :
    (resolveMathAlphas coverage family doc).2.map (·.subject) =
      (missingMathAlphas coverage doc).map
        (fun a => some ("math-alpha:" ++ a.name)) := by
  simp [resolveMathAlphas, missingMathAlphas, Diag.of_subject, Array.map_map, Function.comp]

/-- Expose the completed-region combiner without changing the generic map's walk. -/
public theorem mapInlineList_finish_exact (f : Inline → Inline) (out : Array Inline)
    (xs : List Inline) (finish : Array Inline → Array Inline) :
    mapInlineList f out xs finish =
      finish (out.toList ++ xs.map (mapInline f · finish)).toArray := by
  induction xs generalizing out with
  | nil => simp [mapInlineList]
  | cons x xs ih =>
    rw [mapInlineList, ih]
    simp [Array.toList_push, List.append_assoc]

public theorem mapInlineList_toList (f : Inline → Inline) (out : Array Inline) (xs : List Inline) :
    (mapInlineList f out xs).toList = out.toList ++ xs.map (mapInline f) := by
  simp only [mapInlineList_finish_exact, id_eq, List.toList_toArray]

mutual

private theorem mapMathInline_fixed_point (coverage : Math.MathAlphabetCoverage) (x : Inline) :
    mapInline (resolveMathAlphaInline coverage) (mapInline (resolveMathAlphaInline coverage) x)
      = mapInline (resolveMathAlphaInline coverage) x := by
  match x with
  | .styled st body
  | .colored c n body
  | .located n body | .role n body
  | .link u body
  | .decorated kind body
  | .onSteps spec body
  | .footnote n body =>
    simp only [mapInline]; congr 1; apply Array.toList_inj.mp
    simp [mapInlineList_toList, mapMathInlineElems_fixed_point coverage body.toList]
  | .altSteps spec firstPage otherPage =>
    simp only [mapInline]
    congr 1 <;>
      · apply Array.toList_inj.mp
        simp [mapInlineList_toList, mapMathInlineElems_fixed_point coverage firstPage.toList,
          mapMathInlineElems_fixed_point coverage otherPage.toList]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _
  | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
    simp only [mapInline, resolveMathAlphaInline, Math.resolveMathAlphas_fixed_point]

private theorem mapMathInlineElems_fixed_point (coverage : Math.MathAlphabetCoverage) :
    ∀ xs : List Inline,
      ((xs.map (mapInline (resolveMathAlphaInline coverage))).map
        (mapInline (resolveMathAlphaInline coverage)))
        = xs.map (mapInline (resolveMathAlphaInline coverage))
  | [] => rfl
  | y :: rest => by
    simp only [List.map_cons]
    rw [mapMathInline_fixed_point coverage y, mapMathInlineElems_fixed_point coverage rest]

end

/-- Resolving an inline region twice resolves it once. -/
public theorem mapMathInlines_fixed_point (coverage : Math.MathAlphabetCoverage)
    (xs : Array Inline) :
    mapInlines (resolveMathAlphaInline coverage)
        (mapInlines (resolveMathAlphaInline coverage) xs)
      = mapInlines (resolveMathAlphaInline coverage) xs := by
  apply Array.toList_inj.mp
  simp [mapInlines, mapInlineList_toList, mapMathInlineElems_fixed_point coverage xs.toList]

private theorem map_map_fixed_point {α : Type _} (f : α → α) (h : ∀ a, f (f a) = f a)
    (l : List α) : (l.map f).map f = l.map f := by
  rw [List.map_map]
  exact List.map_congr_left (fun a _ => h a)

public theorem mapBlockList_toList (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline) :
    ∀ (out : Array Block) (bs : List Block),
      (mapBlockList gp f out bs).toList = out.toList ++ bs.map (mapBlock gp f)
  | _, [] => by simp [mapBlockList]
  | out, b :: rest => by
    rw [mapBlockList, mapBlockList_toList gp f (out.push (mapBlock gp f b)) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapBlockItems_toList (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline) :
    ∀ (out : Array (Array Block)) (items : List (Array Block)),
      (mapBlockItems gp f out items).toList
        = out.toList ++ items.map (fun it => mapBlockList gp f #[] it.toList)
  | _, [] => by simp [mapBlockItems]
  | out, it :: rest => by
    rw [mapBlockItems,
      mapBlockItems_toList gp f (out.push (mapBlockList gp f #[] it.toList)) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapBlockCols_toList (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline) :
    ∀ (out : Array (BoxWidth × Array Block)) (cols : List (BoxWidth × Array Block)),
      (mapBlockCols gp f out cols).toList
        = out.toList ++ cols.map (fun c => (c.1, mapBlockList gp f #[] c.2.toList))
  | _, [] => by simp [mapBlockCols]
  | out, (w, body) :: rest => by
    rw [mapBlockCols,
      mapBlockCols_toList gp f (out.push (w, mapBlockList gp f #[] body.toList)) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapTableCells_toList (f : Inline → Inline) :
    ∀ (out : Array (Array Inline)) (cells : List (Array Inline)),
      (mapTableCells f out cells).toList = out.toList ++ cells.map (mapInlines f)
  | _, [] => by simp [mapTableCells]
  | out, cell :: rest => by
    rw [mapTableCells, mapTableCells_toList f (out.push (mapInlines f cell)) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapTableRows_toList (f : Inline → Inline) :
    ∀ (out : Array (Array (Array Inline))) (rows : List (Array (Array Inline))),
      (mapTableRows f out rows).toList
        = out.toList ++ rows.map (fun row => mapTableCells f #[] row.toList)
  | _, [] => by simp [mapTableRows]
  | out, row :: rest => by
    rw [mapTableRows, mapTableRows_toList f (out.push (mapTableCells f #[] row.toList)) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapAlgLines_toList (f : Inline → Inline) :
    ∀ (out : Array AlgLine) (ls : List AlgLine),
      (mapAlgLines f out ls).toList
        = out.toList ++ ls.map (fun l => ({ depth := l.depth, kind := l.kind, content := mapInlines f l.content, comment := l.comment.map (mapInlines f) } : AlgLine))
  | _, [] => by simp [mapAlgLines]
  | out, l :: rest => by
    rw [mapAlgLines, mapAlgLines_toList f (out.push { depth := l.depth, kind := l.kind, content := mapInlines f l.content, comment := l.comment.map (mapInlines f) }) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapBibItems_toList (f : Inline → Inline) :
    ∀ (out : Array BibItem) (items : List BibItem),
      (mapBibItems f out items).toList
        = out.toList ++ items.map (fun i => { i with content := mapInlines f i.content })
  | _, [] => by simp [mapBibItems]
  | out, i :: rest => by
    rw [mapBibItems, mapBibItems_toList f (out.push { i with content := mapInlines f i.content }) rest]
    simp [Array.toList_push, List.append_assoc]

private theorem resolveMathAlphaPicture_fixed_point (coverage : Math.MathAlphabetCoverage)
    (pic : Pic.Picture) :
    resolveMathAlphaPicture coverage (resolveMathAlphaPicture coverage pic)
      = resolveMathAlphaPicture coverage pic := by
  simp only [resolveMathAlphaPicture, Pic.Picture.mapLabels_comp]
  congr 1
  exact funext (mapMathInlines_fixed_point coverage)

private theorem mapMathTableCells_fixed_point (coverage : Math.MathAlphabetCoverage)
    (cells : List (Array Inline)) :
    mapTableCells (resolveMathAlphaInline coverage) #[]
        (mapTableCells (resolveMathAlphaInline coverage) #[] cells).toList
      = mapTableCells (resolveMathAlphaInline coverage) #[] cells := by
  apply Array.toList_inj.mp
  simp only [mapTableCells_toList, List.nil_append]
  exact map_map_fixed_point (mapInlines (resolveMathAlphaInline coverage)) (mapMathInlines_fixed_point coverage) _

private theorem mapMathTableRows_fixed_point (coverage : Math.MathAlphabetCoverage)
    (rows : List (Array (Array Inline))) :
    mapTableRows (resolveMathAlphaInline coverage) #[]
        (mapTableRows (resolveMathAlphaInline coverage) #[] rows).toList
      = mapTableRows (resolveMathAlphaInline coverage) #[] rows := by
  apply Array.toList_inj.mp
  simp only [mapTableRows_toList, List.nil_append]
  refine map_map_fixed_point (fun row => mapTableCells (resolveMathAlphaInline coverage) #[] row.toList)
    (fun row => ?_) _
  exact mapMathTableCells_fixed_point coverage row.toList

private theorem mapMathAlgLines_fixed_point (coverage : Math.MathAlphabetCoverage) (ls : List AlgLine) :
    mapAlgLines (resolveMathAlphaInline coverage) #[]
        (mapAlgLines (resolveMathAlphaInline coverage) #[] ls).toList
      = mapAlgLines (resolveMathAlphaInline coverage) #[] ls := by
  apply Array.toList_inj.mp
  simp only [mapAlgLines_toList, List.nil_append]
  apply map_map_fixed_point
  intro l
  have hcomment : (l.comment.map (mapInlines (resolveMathAlphaInline coverage))).map
      (mapInlines (resolveMathAlphaInline coverage))
      = l.comment.map (mapInlines (resolveMathAlphaInline coverage)) := by
    cases l.comment with
    | none => rfl
    | some c => simp [mapMathInlines_fixed_point coverage]
  simp only [mapMathInlines_fixed_point coverage, hcomment]

private theorem mapMathBibItems_fixed_point (coverage : Math.MathAlphabetCoverage) (items : List BibItem) :
    mapBibItems (resolveMathAlphaInline coverage) #[]
        (mapBibItems (resolveMathAlphaInline coverage) #[] items).toList
      = mapBibItems (resolveMathAlphaInline coverage) #[] items := by
  apply Array.toList_inj.mp
  simp only [mapBibItems_toList, List.nil_append]
  apply map_map_fixed_point
  intro i
  simp [mapMathInlines_fixed_point coverage]

mutual

private theorem mapMathBlock_fixed_point (coverage : Math.MathAlphabetCoverage) (b : Block) :
    mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage)
        (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) b)
      = mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) b := by
  match b with
  | .para content => simp only [mapBlock, mapMathInlines_fixed_point coverage]
  | .equation n content => simp only [mapBlock, mapMathInlines_fixed_point coverage]
  | .section l st n title => simp only [mapBlock, mapMathInlines_fixed_point coverage]
  | .framefoot content => simp only [mapBlock, mapMathInlines_fixed_point coverage]
  | .logo content => simp only [mapBlock, mapMathInlines_fixed_point coverage]
  | .list o items =>
    simp only [mapBlock]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockItems_toList, List.nil_append]
    exact mapMathBlockItemsElems_fixed_point coverage items.toList
  | .columns cols =>
    simp only [mapBlock]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockCols_toList, List.nil_append]
    exact mapMathBlockColsElems_fixed_point coverage cols.toList
  | .center body
  | .ragged s body
  | .quote body
  | .abstract body
  | .role n body
  | .link target body
  | .spaced g body
  | .onSteps spec body
  | .only targets body
  | .nav spec body
  | .note body =>
    simp only [mapBlock]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockList_toList, List.nil_append]
    exact mapMathBlockElems_fixed_point coverage body.toList
  | .titled kind title body =>
    simp only [mapBlock, mapMathInlines_fixed_point coverage]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockList_toList, List.nil_append]
    exact mapMathBlockElems_fixed_point coverage body.toList
  | .frame title st v br body =>
    simp only [mapBlock, mapMathInlines_fixed_point coverage]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockList_toList, List.nil_append]
    exact mapMathBlockElems_fixed_point coverage body.toList
  | .float k num ca body caption =>
    simp only [mapBlock, mapMathInlines_fixed_point coverage]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockList_toList, List.nil_append]
    exact mapMathBlockElems_fixed_point coverage body.toList
  | .altSteps spec firstPage otherPage =>
    simp only [mapBlock]
    congr 1 <;>
      · apply Array.toList_inj.mp
        simp only [mapBlockList_toList, List.nil_append]
        first
          | exact mapMathBlockElems_fixed_point coverage firstPage.toList
          | exact mapMathBlockElems_fixed_point coverage otherPage.toList
  | .table c pl pr rows rules spans =>
    simp only [mapBlock]
    rw [mapMathTableRows_fixed_point coverage rows.toList]
  | .algorithm n sm lines =>
    simp only [mapBlock]
    rw [mapMathAlgLines_fixed_point coverage lines.toList]
  | .bibliography src style items =>
    simp only [mapBlock]
    rw [mapMathBibItems_fixed_point coverage items.toList]
  | .verbatim c s spec =>
    cases hc : spec.caption with
    | none => simp [mapBlock, hc]
    | some pr => simp [mapBlock, hc, mapMathInlines_fixed_point coverage]
  | .picture pic => simp only [mapBlock, resolveMathAlphaPicture_fixed_point coverage pic]
  | .setPalette _ | .setTokens _ | .pagebreak | .rule _ _ _ =>
    simp only [mapBlock]

private theorem mapMathBlockElems_fixed_point (coverage : Math.MathAlphabetCoverage) :
    ∀ bs : List Block,
      ((bs.map (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))).map
        (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage)))
        = bs.map (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))
  | [] => rfl
  | b :: rest => by
    simp only [List.map_cons]
    rw [mapMathBlock_fixed_point coverage b, mapMathBlockElems_fixed_point coverage rest]

private theorem mapMathBlockItemsElems_fixed_point (coverage : Math.MathAlphabetCoverage) :
    ∀ its : List (Array Block),
      ((its.map (fun it => mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] it.toList)).map
        (fun it => mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] it.toList))
        = its.map (fun it => mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] it.toList)
  | [] => rfl
  | it :: rest => by
    have h : mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[]
        (mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] it.toList).toList
        = mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] it.toList := by
      apply Array.toList_inj.mp
      simp only [mapBlockList_toList, List.nil_append]
      exact mapMathBlockElems_fixed_point coverage it.toList
    simp only [List.map_cons]
    rw [h, mapMathBlockItemsElems_fixed_point coverage rest]

private theorem mapMathBlockColsElems_fixed_point (coverage : Math.MathAlphabetCoverage) :
    ∀ cols : List (BoxWidth × Array Block),
      ((cols.map (fun c => (c.1, mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] c.2.toList))).map
        (fun c => (c.1, mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] c.2.toList)))
        = cols.map (fun c => (c.1, mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] c.2.toList))
  | [] => rfl
  | c :: rest => by
    have h : mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[]
        (mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] c.2.toList).toList
        = mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] c.2.toList := by
      apply Array.toList_inj.mp
      simp only [mapBlockList_toList, List.nil_append]
      exact mapMathBlockElems_fixed_point coverage c.2.toList
    simp only [List.map_cons]
    rw [h, mapMathBlockColsElems_fixed_point coverage rest]

end

private theorem mapMathBlocks_fixed_point (coverage : Math.MathAlphabetCoverage) (xs : Array Block) :
    mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) xs)
      = mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) xs := by
  apply Array.toList_inj.mp
  simp only [mapBlocksPic, mapBlockList_toList, List.nil_append]
  exact mapMathBlockElems_fixed_point coverage xs.toList

/-- Document mapping composes region by region, including style templates. -/
private theorem mapDoc_comp (fi fi' : Array Inline → Array Inline)
    (fb fb' : Array Block → Array Block) (doc : Doc) :
    mapDoc fi fb (mapDoc fi' fb' doc) = mapDoc (fi ∘ fi') (fb ∘ fb') doc := by
  simp [mapDoc, Option.map_map, Function.comp]
  congr 1

private theorem mapMathDoc_fixed_point (coverage : Math.MathAlphabetCoverage) (doc : Doc) :
    mapDoc (mapInlines (resolveMathAlphaInline coverage))
        (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))
        (mapDoc (mapInlines (resolveMathAlphaInline coverage))
          (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage)) doc)
      = mapDoc (mapInlines (resolveMathAlphaInline coverage))
          (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage)) doc := by
  have hfi : (mapInlines (resolveMathAlphaInline coverage))
      ∘ (mapInlines (resolveMathAlphaInline coverage))
      = mapInlines (resolveMathAlphaInline coverage) := funext (mapMathInlines_fixed_point coverage)
  have hfb : (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))
      ∘ (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))
      = mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) := funext (mapMathBlocks_fixed_point coverage)
  rw [mapDoc_comp, hfi, hfb]

/-- The shared IR is unchanged by a second alphabet resolution, including
body, captions and running furniture. Backend entry corollaries project it. -/
public theorem resolveMathAlphas_fixed_point (coverage : Math.MathAlphabetCoverage)
    (family : String) (doc : Doc) :
    (resolveMathAlphas coverage family (resolveMathAlphas coverage family doc).1).1
      = (resolveMathAlphas coverage family doc).1 := by
  simp only [resolveMathAlphas]
  exact mapMathDoc_fixed_point coverage doc

/-- Every request a census holds asks for an alphabet-free formula. -/
private def RequestsFree (out : Array MathRequest) : Prop :=
  ∀ r ∈ out, r.body.alphaFree = true

private theorem requestsFree_push {out : Array MathRequest} {r : MathRequest}
    (h : RequestsFree out) (hr : r.body.alphaFree = true) : RequestsFree (out.push r) := by
  intro q hq
  rcases Array.mem_push.mp hq with hq | hq
  · exact h q hq
  · exact hq ▸ hr

private theorem mathRequestFold_openBlock (scope : MathRequestScope)
    (ctx : Option Span × Bool) (out : Array MathRequest) (b : Block) :
    (mathRequestFold scope).openBlock ctx out b = mathRequestOpen scope ctx out b := rfl

private theorem mathRequestFold_closeBlock (scope : MathRequestScope)
    (ctx : Option Span × Bool) (out : Array MathRequest) (b : Block) :
    (mathRequestFold scope).closeBlock ctx out b = out := rfl

mutual

/-- A walk with the request census's inline events, over a resolved inline,
pushes only resolved formulas — whatever context it is read under. -/
private theorem requestsInline_resolve_covers (coverage : Math.MathAlphabetCoverage)
    (w : CtxFold (Option Span × Bool) (Array MathRequest))
    (ho : ∀ ctx out x, w.openInline ctx out x = mathRequestInlines.openInline ctx out x)
    (hc : ∀ ctx out x, w.closeInline ctx out x = out)
    (ctx : Option Span × Bool) (out : Array MathRequest) (x : Inline) (h : RequestsFree out) :
    RequestsFree (foldCtxInline w ctx out (mapInline (resolveMathAlphaInline coverage) x)) := by
  match x with
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
  | .decorated _ body | .onSteps _ body | .footnote _ body =>
    simp only [mapInline, foldCtxInline, ho, hc, mathRequestInlines, mapInlineList_toList,
      List.nil_append]
    exact requestsInlineList_resolve_covers coverage w ho hc _ out body.toList h
  | .altSteps _ firstPage otherPage =>
    simp only [mapInline, foldCtxInline, ho, hc, mathRequestInlines, mapInlineList_toList,
      List.nil_append]
    exact requestsInlineList_resolve_covers coverage w ho hc _ _ otherPage.toList
      (requestsInlineList_resolve_covers coverage w ho hc _ out firstPage.toList h)
  | .formula _ _ body =>
    simp only [mapInline, resolveMathAlphaInline, foldCtxInline, ho, hc, mathRequestInlines]
    split
    · exact requestsFree_push h (Math.resolveMathAlphas_covers coverage body)
    · exact h
  | .text _ | .math _ _ | .image _ _ _ | .icon _ _ | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount
  | .linebreak _ =>
    simpa only [mapInline, resolveMathAlphaInline, foldCtxInline, ho, hc, mathRequestInlines]
      using h

private theorem requestsInlineList_resolve_covers (coverage : Math.MathAlphabetCoverage)
    (w : CtxFold (Option Span × Bool) (Array MathRequest))
    (ho : ∀ ctx out x, w.openInline ctx out x = mathRequestInlines.openInline ctx out x)
    (hc : ∀ ctx out x, w.closeInline ctx out x = out)
    (ctx : Option Span × Bool) (out : Array MathRequest) :
    ∀ xs : List Inline, RequestsFree out →
      RequestsFree (foldCtxInlineList w ctx out
        (xs.map (mapInline (resolveMathAlphaInline coverage))))
  | [], h => h
  | x :: rest, h => by
    rw [List.map_cons, foldCtxInlineList]
    exact requestsInlineList_resolve_covers coverage w ho hc ctx _ rest
      (requestsInline_resolve_covers coverage w ho hc ctx out x h)

end

/-- The block census's own inline events are the request fold's. -/
private theorem requestsFoldInlines_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool)
    (out : Array MathRequest) (xs : Array Inline) (h : RequestsFree out) :
    RequestsFree (foldCtxInlineList (mathRequestFold scope) ctx out
      (mapInlines (resolveMathAlphaInline coverage) xs).toList) := by
  simp only [mapInlines, mapInlineList_toList, List.nil_append]
  exact requestsInlineList_resolve_covers coverage (mathRequestFold scope) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) ctx out xs.toList h

/-- A run of resolved inline regions, each read by the request fold. -/
private theorem requestsRegions_resolve_covers (coverage : Math.MathAlphabetCoverage)
    (ctx : Option Span × Bool) :
    ∀ (regions : List (Array Inline)) (out : Array MathRequest), RequestsFree out →
      RequestsFree ((regions.map (mapInlines (resolveMathAlphaInline coverage))).foldl
        (fun acc xs => foldCtxInlines mathRequestInlines ctx acc xs) out)
  | [], _, h => h
  | xs :: rest, out, h => by
    rw [List.map_cons, List.foldl_cons]
    apply requestsRegions_resolve_covers coverage ctx rest
    simp only [foldCtxInlines, mapInlines, mapInlineList_toList, List.nil_append]
    exact requestsInlineList_resolve_covers coverage _ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      ctx out xs.toList h

private theorem requestsCells_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool) :
    ∀ (cells : List (Array Inline)) (out : Array MathRequest), RequestsFree out →
      RequestsFree (foldCtxTableCells (mathRequestFold scope) ctx out
        (cells.map (mapInlines (resolveMathAlphaInline coverage))))
  | [], _, h => h
  | cell :: rest, out, h => by
    rw [List.map_cons, foldCtxTableCells]
    exact requestsCells_resolve_covers scope coverage ctx rest _
      (requestsFoldInlines_resolve_covers scope coverage ctx out cell h)

private theorem requestsRows_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool) :
    ∀ (rows : List (Array (Array Inline))) (out : Array MathRequest), RequestsFree out →
      RequestsFree (foldCtxTableRows (mathRequestFold scope) ctx out
        (rows.map fun row => mapTableCells (resolveMathAlphaInline coverage) #[] row.toList))
  | [], _, h => h
  | row :: rest, out, h => by
    rw [List.map_cons, foldCtxTableRows, mapTableCells_toList, List.nil_append]
    exact requestsRows_resolve_covers scope coverage ctx rest _
      (requestsCells_resolve_covers scope coverage ctx row.toList out h)

private theorem requestsAlgLines_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool) :
    ∀ (lines : List AlgLine) (out : Array MathRequest), RequestsFree out →
      RequestsFree (foldCtxAlgLines (mathRequestFold scope) ctx out
        (mapAlgLines (resolveMathAlphaInline coverage) #[] lines).toList)
  | [], _, h => h
  | line :: rest, out, h => by
    have step := requestsAlgLines_resolve_covers scope coverage ctx rest
    simp only [mapAlgLines_toList, List.nil_append] at step ⊢
    rw [List.map_cons, foldCtxAlgLines]
    apply step
    cases hc : line.comment with
    | none =>
      simpa only [Option.map_none] using
        requestsFoldInlines_resolve_covers scope coverage ctx out line.content h
    | some c =>
      simp only [Option.map_some]
      exact requestsFoldInlines_resolve_covers scope coverage ctx _ c
        (requestsFoldInlines_resolve_covers scope coverage ctx out line.content h)

mutual

/-- The request census over a resolved block reads only resolved formulas:
its descent through every region `foldCtxBlock` walks, and the block-owned
regions `mathRequestOpen` reads — captions, references, picture labels. -/
private theorem requestsBlock_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool)
    (out : Array MathRequest) (b : Block) (h : RequestsFree out) :
    RequestsFree (foldCtxBlock (mathRequestFold scope) ctx out
      (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) b)) := by
  match b with
  | .para content | .section _ _ _ content | .framefoot content | .logo content =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock]
    exact requestsFoldInlines_resolve_covers scope coverage ctx out content h
  | .equation number content =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock]
    exact requestsFoldInlines_resolve_covers scope coverage ctx _ number
      (requestsFoldInlines_resolve_covers scope coverage ctx out content h)
  | .list _ items =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockItems_toList, List.nil_append]
    exact requestsItems_resolve_covers scope coverage ctx out items.toList h
  | .columns cols =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockCols_toList, List.nil_append]
    exact requestsCols_resolve_covers scope coverage ctx out cols.toList h
  | .center body | .ragged _ body | .quote body | .abstract body | .role _ body
  | .link _ body | .spaced _ body | .onSteps _ body | .only _ body | .nav _ body =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockList_toList, List.nil_append]
    exact requestsBlockList_resolve_covers scope coverage ctx out body.toList h
  | .note body =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockList_toList, List.nil_append]
    exact requestsBlockList_resolve_covers scope coverage _ out body.toList h
  | .titled _ title body | .frame title _ _ _ body | .float _ _ _ body title =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockList_toList, List.nil_append]
    exact requestsBlockList_resolve_covers scope coverage ctx _ body.toList
      (requestsFoldInlines_resolve_covers scope coverage ctx out title h)
  | .altSteps _ firstPage otherPage =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockList_toList, List.nil_append]
    exact requestsBlockList_resolve_covers scope coverage ctx _ otherPage.toList
      (requestsBlockList_resolve_covers scope coverage ctx out firstPage.toList h)
  | .table _ _ _ rows _ _ =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapTableRows_toList, List.nil_append]
    exact requestsRows_resolve_covers scope coverage ctx rows.toList out h
  | .algorithm _ _ lines =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock]
    exact requestsAlgLines_resolve_covers scope coverage ctx lines.toList out h
  | .verbatim _ _ spec =>
    cases hc : spec.caption with
    | none =>
      simpa only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
        mathRequestFold_closeBlock, hc, Option.map_none, id_eq] using h
    | some caption =>
      simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
        mathRequestFold_closeBlock, hc, Option.map_some, id_eq]
      exact requestsRegions_resolve_covers coverage ctx [caption.2] out h
  | .bibliography _ _ items =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock]
    rw [← Array.foldl_toList, mapBibItems_toList, List.nil_append, List.foldl_map]
    have := requestsRegions_resolve_covers coverage ctx (items.toList.map (·.content)) out h
    simpa only [List.map_map, List.foldl_map, Function.comp_def] using this
  | .picture pic =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, resolveMathAlphaPicture, Pic.Picture.labelContents_mapLabels]
    rw [← Array.foldl_toList, Array.toList_map]
    exact requestsRegions_resolve_covers coverage ctx pic.labelContents.toList out h
  | .setPalette _ | .setTokens _ | .pagebreak | .rule _ _ _ =>
    simpa only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock] using h

private theorem requestsBlockList_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool)
    (out : Array MathRequest) :
    ∀ bs : List Block, RequestsFree out →
      RequestsFree (foldCtxBlockList (mathRequestFold scope) ctx out
        (bs.map (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))))
  | [], h => h
  | b :: rest, h => by
    rw [List.map_cons, foldCtxBlockList]
    exact requestsBlockList_resolve_covers scope coverage ctx _ rest
      (requestsBlock_resolve_covers scope coverage ctx out b h)

private theorem requestsItems_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool)
    (out : Array MathRequest) :
    ∀ items : List (Array Block), RequestsFree out →
      RequestsFree (foldCtxBlockItems (mathRequestFold scope) ctx out
        (items.map fun item => mapBlockList (resolveMathAlphaPicture coverage)
          (resolveMathAlphaInline coverage) #[] item.toList))
  | [], h => h
  | item :: rest, h => by
    rw [List.map_cons, foldCtxBlockItems, mapBlockList_toList, List.nil_append]
    exact requestsItems_resolve_covers scope coverage ctx _ rest
      (requestsBlockList_resolve_covers scope coverage ctx out item.toList h)

private theorem requestsCols_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool)
    (out : Array MathRequest) :
    ∀ cols : List (BoxWidth × Array Block), RequestsFree out →
      RequestsFree (foldCtxBlockCols (mathRequestFold scope) ctx out
        (cols.map fun c => (c.1, mapBlockList (resolveMathAlphaPicture coverage)
          (resolveMathAlphaInline coverage) #[] c.2.toList)))
  | [], h => h
  | (_, body) :: rest, h => by
    rw [List.map_cons, foldCtxBlockCols, mapBlockList_toList, List.nil_append]
    exact requestsCols_resolve_covers scope coverage ctx _ rest
      (requestsBlockList_resolve_covers scope coverage ctx out body.toList h)

end

/-- **Alphabet resolution reaches every formula either census reads**
(`_covers`): after `resolveMathAlphas`, every request of the painted census —
the regions the face is loaded for and both backends set, picture labels
included — and of the alphabet census asks for an alphabet-free formula, for
every document, coverage and family. The painted census reads
`Layout.docMathScalars`' regions (a corpus check, not a theorem, holds the
two to one scalar set), so a region a backend paints and the resolver skips
breaks this statement: picture labels once shipped their
alphabets unresolved, which MathML framed as an error and the page set in the
source glyphs. -/
public theorem mathRequests_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (family : String) (doc : Doc) :
    ∀ r ∈ mathRequests scope (resolveMathAlphas coverage family doc).1,
      r.body.alphaFree = true := by
  have body : RequestsFree (foldCtxBlocks (mathRequestFold scope) (none, true) #[]
      (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage)
        doc.body)) := by
    simp only [foldCtxBlocks, mapBlocksPic, mapBlockList_toList, List.nil_append]
    exact requestsBlockList_resolve_covers scope coverage (none, true) #[] doc.body.toList
      (fun _ h => by simp at h)
  have furniture : ∀ (regions : Array (Array Inline)) (out : Array MathRequest),
      RequestsFree out →
        RequestsFree ((regions.map (mapInlines (resolveMathAlphaInline coverage))).foldl
          (fun acc xs => foldCtxInlines mathRequestInlines (none, true) acc xs) out) := by
    intro regions out h
    rw [← Array.foldl_toList, Array.toList_map]
    exact requestsRegions_resolve_covers coverage (none, true) regions.toList out h
  cases scope with
  | alphabets =>
    simp only [mathRequests, resolveMathAlphas, furnitureInlines_mapDoc]
    exact furniture _ _ body
  | face =>
    simp only [mathRequests, resolveMathAlphas]
    cases hh : doc.headline with
    | none =>
      have := furniture (furnitureInlines.optRegion doc.head ++
        furnitureInlines.optRegion doc.foot ++ #[] ++
        furnitureInlines.optRegion doc.logoLeft ++ furnitureInlines.optRegion doc.logoRight)
        _ body
      simp only [RequestsFree] at this
      simpa [mapDoc, hh, optRegion_map, Array.map_append] using this
    | some hl =>
      have := furniture (furnitureInlines.optRegion doc.head ++
        furnitureInlines.optRegion doc.foot ++ #[hl.title, hl.author, hl.institute] ++
        furnitureInlines.optRegion doc.logoLeft ++ furnitureInlines.optRegion doc.logoRight)
        _ body
      simp only [RequestsFree] at this
      simpa [mapDoc, hh, optRegion_map, Array.map_append] using this

/-- Resolution empties the alphabet census for every document and coverage:
the census reads the alphabet requests, and every one of them is
alphabet-free after resolution (`mathRequests_resolve_covers`). -/
public theorem missingMathAlphas_resolve_exact (coverage : Math.MathAlphabetCoverage)
    (family : String) (doc : Doc) :
    missingMathAlphas coverage (resolveMathAlphas coverage family doc).1 = #[] := by
  have spent : ∀ rs : List MathRequest, (∀ r ∈ rs, r.body.alphaFree = true) →
      rs.foldl (noteRequestAlphas coverage) #[] = #[] := by
    intro rs hrs
    induction rs with
    | nil => rfl
    | cons r rest ih =>
      simp only [List.foldl_cons, noteRequestAlphas,
        Math.missingMathAlphas_alphaFree_exact coverage _ (hrs r (by simp)), Array.foldl_empty]
      exact ih fun q hq => hrs q (by simp [hq])
  rw [missingMathAlphas, missingAlphasOf, ← Array.foldl_toList]
  exact spent _ fun r hr =>
    mathRequests_resolve_covers .alphabets coverage family doc r (by simpa using hr)

/-- Entry normalization can repeat without repeating N0018 diagnostics. -/
public theorem resolveMathAlphas_diags_exact (coverage : Math.MathAlphabetCoverage)
    (family : String) (doc : Doc) :
    (resolveMathAlphas coverage family (resolveMathAlphas coverage family doc).1).2 = #[] := by
  change (missingMathAlphas coverage (resolveMathAlphas coverage family doc).1).map _ = #[]
  rw [missingMathAlphas_resolve_exact, Array.map_empty]

/-- The List companion of `linkBlocks`: one block link owns the whole body,
so an authored wrapper cannot multiply with its inline leaves. -/
private def linkBlockList (url : String) (body : List Block) : List Block :=
  [Block.link url body.toArray]

/-- Wrap a block sequence in one link destination. -/
public def linkBlocks (url : String) (xs : Array Block) : Array Block :=
  (linkBlockList url xs.toList).toArray

/-- A block link's nested body given its kind's affordance: every
text-bearing run — through styling, colour and role wrappers alike — set in
the kind's link ink and underlined, exactly as an inline link's body is,
applied once per leaf. Built only where the body bears no anchor
(`hasBlockAnchor` refuses the nested case first), so no span inside an inner
inline link is reached, and none is afforded twice. An image-only body — no
text-bearing leaf — is returned carrying no decoration (`linkLeafAfford_id`).
Both backends read this one afforded body: `Layout`'s `.decorated`/`.colored`
arms lower it to a PDF underline fill and coloured glyphs, HtmlDoc's to a
`<u>` and an ink span. -/
public def Styles.linkBodyAfford (s : Styles) (kind : String) (xs : Array Block) : Array Block :=
  -- A picture's labels are the diagram's text, not the link's: they keep
  -- their own ink and are never underlined.
  mapBlocks (s.linkLeafAfford kind) xs

mutual

/-- The census face of the map, per node: a leaf function that conserves
each node's own census conserves every node's. `mapInlines_text` and
`mapBlocks_text` are the walk-level schema; a leaf-rewrite states its
census fact as their one-line instance instead of one hand induction per
walk. -/
public theorem mapInlineFinish_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) (x : Inline) :
    plainTextOne (mapInline (finish := finish) f x) = plainTextOne x := by
  match x with
  | .styled st body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .colored c n body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .located n body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .role n body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .link u body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .decorated kind body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .onSteps spec body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .altSteps spec firstPage otherPage =>
    show plainTextList (mapInlineList (finish := finish) f #[] firstPage.toList).toList
        ++ plainTextList (mapInlineList (finish := finish) f #[] otherPage.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish firstPage.toList #[],
      mapInlineListFinish_text f hf finish hfinish otherPage.toList #[]]
    simp [plainTextList, plainTextOne]
  | .footnote n body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ => exact hf _

public theorem mapInlineListFinish_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) (xs : List Inline)
    (out : Array Inline) :
    plainTextList (mapInlineList (finish := finish) f out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simpa [mapInlineList, plainText, plainTextList] using hfinish out
  | x :: rest =>
    rw [mapInlineList, mapInlineListFinish_text f hf finish hfinish rest (out.push (mapInline (finish := finish) f x))]
    rw [Array.toList_push, plainTextList_append]
    simp [plainTextList, mapInlineFinish_text f hf finish hfinish x, String.append_assoc]

end

/-- The `Conserves` schema over the generic map, inline face: whatever the
leaf function, if it conserves each node's census the walk conserves the
content's. -/
public theorem mapInlinesFinish_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) :
    Conserves plainText (mapInlines (finish := finish) f) := fun xs => by
  show plainTextList (mapInlineList (finish := finish) f #[] xs.toList).toList = _
  rw [mapInlineListFinish_text f hf finish hfinish xs.toList #[]]
  simp [plainTextList, plainText]

/-- The default map preserves text when its leaf function does. -/
public theorem mapInline_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (x : Inline) :
    plainTextOne (mapInline f x) = plainTextOne x :=
  mapInlineFinish_text f hf id (fun _ => rfl) x

public theorem mapInlineList_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (xs : List Inline)
    (out : Array Inline) :
    plainTextList (mapInlineList f out xs).toList
      = plainTextList out.toList ++ plainTextList xs :=
  mapInlineListFinish_text f hf id (fun _ => rfl) xs out

public theorem mapInlines_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) :
    Conserves plainText (mapInlines f) :=
  mapInlinesFinish_text f hf id (fun _ => rfl)

private theorem mapAlgLines_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) (ls : List AlgLine)
    (out : Array AlgLine) (acc : String) :
    algLineText acc (mapAlgLines (finish := finish) f out ls).toList
      = algLineText (algLineText acc out.toList) ls := by
  match ls with
  | [] => simp [mapAlgLines, algLineText]
  | l :: rest =>
    rw [mapAlgLines, mapAlgLines_text f hf finish hfinish rest]
    rw [Array.toList_push, algLineText_chain]
    have hm : ∀ xs, plainText (mapInlines (finish := finish) f xs) = plainText xs := mapInlinesFinish_text f hf finish hfinish
    cases hc : l.comment <;> simp [algLineText, hc, hm]


mutual

/-- The Bool fold un-threads: the accumulator rides outside as one `||`,
which is what lets `anyInline p = false` decompose per node below. -/
public theorem foldInline_or (p : Inline → Bool) (b : Bool) (x : Inline) :
    foldInline (fun a y => a || p y) b x
      = (b || foldInline (fun a y => a || p y) false x) := by
  match x with
  | .styled st body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .colored c n body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .located n body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .role n body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .link u body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .decorated kind body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .onSteps spec body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .altSteps spec firstPage otherPage =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or,
      foldInlineList_or p (foldInlineList (fun a y => a || p y)
        (false || p (Inline.altSteps spec firstPage otherPage)) firstPage.toList) otherPage.toList,
      foldInlineList_or p (false || p (Inline.altSteps spec firstPage otherPage)) firstPage.toList]
    simp [Bool.or_assoc]
  | .footnote n body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ => simp [foldInline]

public theorem foldInlineList_or (p : Inline → Bool) (b : Bool) (xs : List Inline) :
    foldInlineList (fun a y => a || p y) b xs
      = (b || foldInlineList (fun a y => a || p y) false xs) := by
  match xs with
  | [] => simp [foldInlineList]
  | x :: rest =>
    rw [foldInlineList, foldInlineList,
      foldInlineList_or p (foldInline (fun a y => a || p y) b x),
      foldInlineList_or p (foldInline (fun a y => a || p y) false x),
      foldInline_or p b x]
    simp [Bool.or_assoc]

end

mutual

/-- Conditional identity, per node: where the trigger census `p` reads
false everywhere and the leaf function fixes every `p`-false node, the map
leaves the node exactly as it stood. -/
public theorem mapInline_id (f : Inline → Inline) (p : Inline → Bool)
    (hf : ∀ x, p x = false → f x = x) (x : Inline)
    (h : foldInline (fun a y => a || p y) false x = false) :
    mapInline f x = x := by
  match x with
  | .styled st body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .colored c n body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .located n body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .role n body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .link u body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .decorated kind body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .onSteps spec body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .altSteps spec firstPage otherPage =>
    rw [foldInline, foldInlineList_or, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨h1, h3⟩
    rcases Bool.or_eq_false_iff.mp h1 with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf firstPage.toList #[] h2,
      mapInlineList_id f p hf otherPage.toList #[] h3]
    simp
  | .footnote n body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ =>
    exact hf _ (by simpa [foldInline] using h)

public theorem mapInlineList_id (f : Inline → Inline) (p : Inline → Bool)
    (hf : ∀ x, p x = false → f x = x) (xs : List Inline) (out : Array Inline)
    (h : foldInlineList (fun a y => a || p y) false xs = false) :
    mapInlineList f out xs = out ++ xs.toArray := by
  match xs with
  | [] => simp [mapInlineList]
  | x :: rest =>
    rw [foldInlineList, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨h1, h2⟩
    rw [mapInlineList, mapInline_id f p hf x h1,
      mapInlineList_id f p hf rest (out.push x) h2]
    simp

end

/-- The conditional-identity schema over the generic map (`_id`): content
carrying no `p`-node survives the pass whole, whenever the leaf function
fixes every `p`-false node. `Layout.substPage_id` is its instance, with
`hasPhysicalPage` (= `anyInline isPhysicalPage`) as the trigger census. -/
public theorem mapInlines_id (f : Inline → Inline) (p : Inline → Bool)
    (hf : ∀ x, p x = false → f x = x) (xs : Array Inline)
    (h : anyInline p xs = false) : mapInlines f xs = xs := by
  rw [mapInlines, mapInlineList_id f p hf xs.toList #[] h]
  simp

private theorem mapTableCells_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) (cells : List (Array Inline))
    (out : Array (Array Inline)) (acc : String) :
    blockTextTableCells acc (mapTableCells (finish := finish) f out cells).toList
      = blockTextTableCells (blockTextTableCells acc out.toList) cells := by
  match cells with
  | [] => simp [mapTableCells, blockTextTableCells]
  | cell :: rest =>
    rw [mapTableCells, mapTableCells_text f hf finish hfinish rest]
    rw [Array.toList_push, blockTextTableCells_chain]
    simp [blockTextTableCells, mapInlinesFinish_text f hf finish hfinish cell]

private theorem mapTableRows_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (rows : List (Array (Array Inline)))
    (out : Array (Array (Array Inline))) (acc : String) :
    blockTextTableRows acc (mapTableRows (finish := finish) f out rows).toList
      = blockTextTableRows (blockTextTableRows acc out.toList) rows := by
  match rows with
  | [] => simp [mapTableRows, blockTextTableRows]
  | row :: rest =>
    rw [mapTableRows, mapTableRows_text f hf finish hfinish rest]
    rw [Array.toList_push, blockTextTableRows_chain]
    simp [blockTextTableRows, blockTextTableCells, mapTableCells_text f hf finish hfinish row.toList #[]]

private theorem mapBibItems_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) (items : List BibItem)
    (out : Array BibItem) (acc : String) :
    blockTextBibItems acc (mapBibItems (finish := finish) f out items).toList
      = blockTextBibItems (blockTextBibItems acc out.toList) items := by
  match items with
  | [] => simp [mapBibItems, blockTextBibItems]
  | i :: rest =>
    rw [mapBibItems, mapBibItems_text f hf finish hfinish rest]
    rw [Array.toList_push, blockTextBibItems_chain]
    simp [blockTextBibItems, mapInlinesFinish_text f hf finish hfinish i.content]

mutual

public theorem mapBlockWith_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText) (acc : String) (b : Block) :
    blockTextOne acc (mapBlock (finish := finish) (listing := listing) gp f b) = blockTextOne acc b := by
  match b with
  | .para content => simp [mapBlock, blockTextOne, mapInlinesFinish_text f hf finish hfinish content]
  | .equation n content =>
    simp [mapBlock, blockTextOne, mapInlinesFinish_text f hf finish hfinish content, mapInlinesFinish_text f hf finish hfinish n]
  | .section l st n title =>
    simp [mapBlock, blockTextOne, mapInlinesFinish_text f hf finish hfinish title]
  | .list o items =>
    show blockTextItems acc (mapBlockItems (finish := finish) (listing := listing) gp f #[] items.toList).toList = _
    rw [mapBlockItemsWith_text gp f hf finish hfinish listing hlisting items.toList #[]]
    rfl
  | .center body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .ragged _ body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .quote body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .abstract body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .titled kind title body =>
    show blockTextList (acc ++ plainText (mapInlines (finish := finish) f title))
      (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapInlinesFinish_text f hf finish hfinish title, mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .role n body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .link target body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .spaced g body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .columns cols =>
    show blockTextColumns acc (mapBlockCols (finish := finish) (listing := listing) gp f #[] cols.toList).toList = _
    rw [mapBlockColsWith_text gp f hf finish hfinish listing hlisting cols.toList #[]]
    rfl
  | .onSteps spec body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .altSteps spec firstPage otherPage =>
    show blockTextList (blockTextList acc
        (mapBlockList (finish := finish) (listing := listing) gp f #[] firstPage.toList).toList)
        (mapBlockList (finish := finish) (listing := listing) gp f #[] otherPage.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting firstPage.toList #[],
      mapBlockListWith_text gp f hf finish hfinish listing hlisting otherPage.toList #[]]
    rfl
  | .only targets body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .nav spec body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .note body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .frame title st v _ body =>
    show blockTextList (acc ++ plainText (mapInlines (finish := finish) f title))
      (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapInlinesFinish_text f hf finish hfinish title, mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .framefoot content =>
    simp [mapBlock, blockTextOne, mapInlinesFinish_text f hf finish hfinish content]
  | .float k num ca body caption =>
    show blockTextList (acc ++ plainText (mapInlines (finish := finish) f caption))
      (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapInlinesFinish_text f hf finish hfinish caption, mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .table c pl pr rows rules spans =>
    show blockTextTableRows acc (mapTableRows (finish := finish) f #[] rows.toList).toList = _
    rw [mapTableRows_text f hf finish hfinish rows.toList #[]]
    rfl
  | .algorithm n sm lines =>
    show algLineText acc (mapAlgLines (finish := finish) f #[] lines.toList).toList = _
    rw [mapAlgLines_text f hf finish hfinish lines.toList #[]]
    rfl
  | .logo content => simp [mapBlock, blockTextOne, mapInlinesFinish_text f hf finish hfinish content]
  | .bibliography src style items =>
    show blockTextBibItems acc (mapBibItems (finish := finish) f #[] items.toList).toList = _
    rw [mapBibItems_text f hf finish hfinish items.toList #[]]
    rfl
  | .verbatim _ _ spec =>
    simp only [mapBlock, blockTextOne, hlisting]
    cases hc : spec.caption with
    | none => simp [ListingSpec.capText, hc]
    | some p =>
      simp [ListingSpec.capText, hc,
        mapInlinesFinish_text f hf finish hfinish p.2]
  | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ => rfl

public theorem mapBlockListWith_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText) (bs : List Block)
    (out : Array Block) (acc : String) :
    blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f out bs).toList
      = blockTextList (blockTextList acc out.toList) bs := by
  match bs with
  | [] => simp [mapBlockList, blockTextList]
  | b :: rest =>
    rw [mapBlockList, mapBlockListWith_text gp f hf finish hfinish listing hlisting rest]
    rw [Array.toList_push, blockTextList_chain]
    simp [blockTextList, mapBlockWith_text gp f hf finish hfinish listing hlisting]

public theorem mapBlockItemsWith_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (mapBlockItems (finish := finish) (listing := listing) gp f out items).toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [mapBlockItems, blockTextItems]
  | item :: rest =>
    rw [mapBlockItems, mapBlockItemsWith_text gp f hf finish hfinish listing hlisting rest]
    rw [Array.toList_push, blockTextItems_chain]
    simp [blockTextItems, blockTextList,
      mapBlockListWith_text gp f hf finish hfinish listing hlisting item.toList #[]]

public theorem mapBlockColsWith_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText)
    (cols : List (BoxWidth × Array Block))
    (out : Array (BoxWidth × Array Block)) (acc : String) :
    blockTextColumns acc (mapBlockCols (finish := finish) (listing := listing) gp f out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [mapBlockCols, blockTextColumns]
  | (w, body) :: rest =>
    rw [mapBlockCols, mapBlockColsWith_text gp f hf finish hfinish listing hlisting rest]
    rw [Array.toList_push, blockTextColumns_chain]
    simp [blockTextColumns, blockTextList,
      mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]

end

/-- The `Conserves` schema over the picture- and inline-parameterised map.
A picture rewrite cannot change text, so only the inline leaf hypothesis is
needed. -/
public theorem mapBlocksPicWith_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText) :
    Conserves blocksText (mapBlocksPic (finish := finish) (listing := listing) gp f) := fun xs => by
  show blockTextList "" (mapBlockList (finish := finish) (listing := listing) gp f #[] xs.toList).toList = _
  rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting xs.toList #[]]
  rfl

public theorem mapBlocksWith_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText) :
    Conserves blocksText (mapBlocks (finish := finish) (listing := listing) f) :=
  mapBlocksPicWith_text id f hf finish hfinish listing hlisting

/-- The default block map is the text-preserving instance of the
region-combining map. Pictures have no entry in `blocksText`. -/
public theorem mapBlock_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (acc : String) (b : Block) :
    blockTextOne acc (mapBlock gp f b) = blockTextOne acc b :=
  mapBlockWith_text gp f hf id (fun _ => rfl) id (fun _ => rfl) acc b

public theorem mapBlockList_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (bs : List Block)
    (out : Array Block) (acc : String) :
    blockTextList acc (mapBlockList gp f out bs).toList
      = blockTextList (blockTextList acc out.toList) bs :=
  mapBlockListWith_text gp f hf id (fun _ => rfl) id (fun _ => rfl) bs out acc

public theorem mapBlockItems_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (mapBlockItems gp f out items).toList
      = blockTextItems (blockTextItems acc out.toList) items :=
  mapBlockItemsWith_text gp f hf id (fun _ => rfl) id (fun _ => rfl) items out acc

public theorem mapBlockCols_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (cols : List (BoxWidth × Array Block))
    (out : Array (BoxWidth × Array Block)) (acc : String) :
    blockTextColumns acc (mapBlockCols gp f out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols :=
  mapBlockColsWith_text gp f hf id (fun _ => rfl) id (fun _ => rfl) cols out acc

public theorem mapBlocksPic_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) :
    Conserves blocksText (mapBlocksPic gp f) :=
  mapBlocksPicWith_text gp f hf id (fun _ => rfl) id (fun _ => rfl)

public theorem mapBlocks_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) :
    Conserves blocksText (mapBlocks f) :=
  mapBlocksPic_text id f hf

/- Source erasure uses the map's completed-region combiner. The reverse
list accumulator joins only neighbouring text leaves; it never crosses a
style, link, overlay, footnote, or other semantic boundary. -/
private def pushLocationText (out : List Inline) (x : Inline) : List Inline :=
  match x with
  | .text s =>
    match out with
    | .text t :: rest => .text (t ++ s) :: rest
    | _ => x :: out
  | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _ | .located _ _
  | .role _ _ | .link _ _ | .label _ | .ref _ _ _ _ | .decorated _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .pageNumber | .pageCount | .linebreak _
  | .strut _ | .italicCorr _ | .onSteps _ _ | .altSteps _ _ _ | .image _ _ _
  | .icon _ _ | .cite _ _ | .footnote _ _ => x :: out

private def joinLocationBody (out : List Inline) : List Inline → List Inline
  | [] => out
  | x :: rest => joinLocationBody (pushLocationText out x) rest

private def spliceLocationOne (out : List Inline) (x : Inline) : List Inline :=
  match x with
  | .located _ body => joinLocationBody out body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _
  | .role _ _ | .link _ _ | .label _ | .ref _ _ _ _ | .decorated _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .pageNumber | .pageCount | .linebreak _
  | .strut _ | .italicCorr _ | .onSteps _ _ | .altSteps _ _ _ | .image _ _ _
  | .icon _ _ | .cite _ _ | .footnote _ _ => pushLocationText out x

private def spliceLocations (out : List Inline) : List Inline → List Inline
  | [] => out
  | x :: rest => spliceLocations (spliceLocationOne out x) rest

private def finishLocations (xs : Array Inline) : Array Inline :=
  (spliceLocations [] xs.toList).reverse.toArray

private theorem pushLocationText_reading (out : List Inline) (x : Inline) :
    plainTextList (pushLocationText out x).reverse =
      plainTextList out.reverse ++ plainTextOne x := by
  cases x <;>
    try simp [pushLocationText, List.reverse_cons, plainTextList_append,
      plainTextList]
  cases out with
  | nil => simp [plainTextList, plainTextOne]
  | cons y rest =>
    cases y <;> simp [List.reverse_cons, plainTextList_append,
      plainTextList, plainTextOne, String.append_assoc]

private theorem joinLocationBody_reading (xs : List Inline) (out : List Inline) :
    plainTextList (joinLocationBody out xs).reverse =
      plainTextList out.reverse ++ plainTextList xs := by
  match xs with
  | [] => simp [joinLocationBody, plainTextList]
  | x :: rest =>
    rw [joinLocationBody, joinLocationBody_reading rest, pushLocationText_reading]
    simp [plainTextList, String.append_assoc]

private theorem spliceLocations_reading (xs : List Inline) (out : List Inline) :
    plainTextList (spliceLocations out xs).reverse =
      plainTextList out.reverse ++ plainTextList xs := by
  match xs with
  | [] => simp [spliceLocations, plainTextList]
  | x :: rest =>
    cases x <;>
      simp [spliceLocations, spliceLocationOne, spliceLocations_reading rest, joinLocationBody_reading,
        pushLocationText_reading, plainTextList, plainTextOne, String.append_assoc]

private theorem finishLocations_text : Conserves plainText finishLocations := by
  intro xs
  simp [finishLocations, plainText, spliceLocations_reading, plainTextList]

/-- Erase diagnostic wrappers and join adjacent text throughout an inline
region. The generic map owns recursion; its combiner sees already-mapped
children, so splicing an annotation cannot leave a nested one behind. -/
public def eraseLocationInlines (xs : Array Inline) : Array Inline :=
  mapInlines id xs finishLocations

public theorem eraseLocationInlines_text : Conserves plainText eraseLocationInlines :=
  mapInlinesFinish_text id (fun _ => rfl) finishLocations finishLocations_text

private theorem joinLocationBody_append (out xs ys : List Inline) :
    joinLocationBody out (xs ++ ys) =
      joinLocationBody (joinLocationBody out xs) ys := by
  induction xs generalizing out with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, joinLocationBody, ih]

private theorem pushLocationText_append (out : List Inline) (s t : String) :
    pushLocationText (pushLocationText out (.text s)) (.text t) =
      pushLocationText out (.text (s ++ t)) := by
  cases out with
  | nil => rfl
  | cons x xs => cases x <;> simp [pushLocationText, String.append_assoc]

private theorem joinLocationBody_push (out acc : List Inline) (x : Inline) :
    joinLocationBody out (pushLocationText acc x).reverse =
      pushLocationText (joinLocationBody out acc.reverse) x := by
  cases x <;>
    try simp only [pushLocationText, List.reverse_cons, joinLocationBody_append, joinLocationBody]
  rename_i s
  cases acc with
  | nil => rfl
  | cons y rest =>
    cases y <;>
      try simp only [pushLocationText, List.reverse_cons, joinLocationBody_append, joinLocationBody]
    rename_i t
    exact (pushLocationText_append (joinLocationBody out rest.reverse) t s).symm

private theorem joinLocationBody_join (out acc xs : List Inline) :
    joinLocationBody out (joinLocationBody acc xs).reverse =
      joinLocationBody (joinLocationBody out acc.reverse) xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [joinLocationBody, ih, joinLocationBody_push]

private theorem joinLocationBody_splice (out acc xs : List Inline) :
    joinLocationBody out (spliceLocations acc xs).reverse =
      spliceLocations (joinLocationBody out acc.reverse) xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp only [spliceLocations, ih, spliceLocationOne,
      joinLocationBody_join, joinLocationBody_push]

private theorem spliceLocations_append (out xs ys : List Inline) :
    spliceLocations out (xs ++ ys) =
      spliceLocations (spliceLocations out xs) ys := by
  induction xs generalizing out with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, spliceLocations, ih]

/-- A diagnostic wrapper anywhere in a region leaves its erased value
unchanged, for arbitrary nested content and sibling regions. -/
public theorem eraseLocationInlines_located_exact (span : Span)
    (before body after : Array Inline) :
    eraseLocationInlines (before ++ #[.located span body] ++ after) =
      eraseLocationInlines (before ++ body ++ after) := by
  simp only [eraseLocationInlines, mapInlines, mapInlineList_finish_exact,
    Array.toList_append, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, mapInline]
  simp only [finishLocations, spliceLocations_append,
    spliceLocations, spliceLocationOne, joinLocationBody_splice, List.reverse_nil, joinLocationBody]

private def eraseLocationPicture (pic : Pic.Picture) : Pic.Picture :=
  pic.mapLabels eraseLocationInlines

private def eraseListingSource (spec : ListingSpec) : ListingSpec :=
  { spec with source := none }

/-- The source-free view of a compiled document. Erase only diagnostic
provenance, including listing starts, in every body and furniture region.
Adjacent text rejoins after annotations disappear, recursively; semantic
wrappers, block ordering, design, and picture geometry remain intact. -/
public def eraseLocations (doc : Doc) : Doc :=
  mapDoc eraseLocationInlines
    (mapBlocksPic eraseLocationPicture id · finishLocations eraseListingSource) doc

/-- Source erasure conserves the body's text census and every furniture
region's text, including style templates and markers. This is the actual
erasure pass, with text coalescing, instantiated through the generic maps. -/
public theorem eraseLocations_text :
    Conserves (fun doc : Doc =>
      (blocksText doc.body, (furnitureInlines doc).map plainText)) eraseLocations := by
  intro doc
  apply Prod.ext
  · exact mapBlocksPicWith_text eraseLocationPicture id (fun _ => rfl)
      finishLocations finishLocations_text eraseListingSource (fun _ => rfl) doc.body
  · simp only [eraseLocations, furnitureInlines_mapDoc, Array.map_map, Function.comp_def]
    congr 1
    funext xs
    exact eraseLocationInlines_text xs

/-- The List wrapper changes navigation, never content. -/
private theorem linkBlockList_text (url : String) (xs : List Block) (acc : String) :
    blockTextList acc (linkBlockList url xs) = blockTextList acc xs := by
  simp [linkBlockList, blockTextList, blockTextOne]

/-- Linking a block-shaped wrapper preserves its complete text census. -/
public theorem linkBlocks_text (url : String) : Conserves blocksText (linkBlocks url) := by
  intro xs
  simp [linkBlocks, blocksText, linkBlockList_text]

/-- A block link's affordance conserves the body's census: it is the generic
map under a leaf rewrite that conserves each leaf (`linkLeafAfford_text`), so
neither underline nor ink adds or hides a character — the one census both
backends read from the afforded body. -/
public theorem Styles.linkBodyAfford_text (s : Styles) (kind : String) :
    Conserves blocksText (s.linkBodyAfford kind) := by
  unfold Styles.linkBodyAfford
  exact mapBlocks_text (s.linkLeafAfford kind) (s.linkLeafAfford_text kind)

/-- A caption fills only what was left undeclared: a described image keeps
its own words, and `artifact` inside a captioned figure stays decoration. -/
private def setAltFill (alt : String) : Alt → Alt
  | .undeclared => Alt.declare alt
  | .decorative => .decorative
  | .described t => .described t

/-- A declared alternative survives any enclosing caption. -/
private theorem setAltFill_fixed_point (alt : String) (a : Alt) (h : a ≠ .undeclared) :
    setAltFill alt a = a := by
  cases a with
  | undeclared => exact absurd rfl h
  | decorative => rfl
  | described _ => rfl

/-- Give every non-text object that has no alternative yet this text:
how a `figure` caption becomes the accessible name of the object it
captions. `mapBlocksPic` is the shared exhaustive leaf rewrite, so the
caption reaches nested images and native pictures without a parallel walk.
An inner caption still wins because `setAltFill` changes only undeclared
values. -/
private def setAltLeaf (alt : String) (x : Inline) : Inline :=
  match x with
  | .image src size old => .image src size (setAltFill alt old)
  | _ => x

private def setAltPic (alt : String) (pic : Pic.Picture) : Pic.Picture :=
  { pic with alt := setAltFill alt pic.alt }

public def setAltBlocks (alt : String) (xs : Array Block) : Array Block :=
  mapBlocksPic (setAltPic alt) (setAltLeaf alt) xs

/-- Caption-to-alt is markup, never content: the census does not read a
non-text object's alternative, so the shared rewrite ships exactly the
text census the body had. -/
public theorem setAltBlocks_text (alt : String) :
    Conserves blocksText (setAltBlocks alt) :=
  mapBlocksPic_text _ _ (fun x => by cases x <;> rfl)

/-- A caption as the alternative of what it captions (`setAltBlocks`): the
words its first page shows (`firstPageText`), the reading a frame's name
takes — an overlay alternation in the caption names the object once, never
by both of its groups as the census would. -/
public def captionAltBlocks (caption : Array Inline) (xs : Array Block) : Array Block :=
  setAltBlocks (firstPageText caption) xs

/-- Naming an object by its caption ships the census the body had. -/
public theorem captionAltBlocks_text (caption : Array Inline) :
    Conserves blocksText (captionAltBlocks caption) :=
  setAltBlocks_text _

/-- A declaration met between blocks: `\footnotesize`, `\bfseries`, or a
bare palette name standing where a block could, with no argument. It
scopes every block after it in its group — the rest-of-group reading
`\centering` already has (ltmiscen.dtx: every declaration form scopes to
the group) — and the elaborator carries the open declarations, outermost
first, to every inline region it builds in that scope (a paragraph, a
table cell), where `wrapDecls` puts them around the region. So a table or
list standing next receives the declaration, no empty styled paragraph is
set in its place, and a later `\normalsize` inside resets because it
stands innermost and sizes are absolute (`Layout.applyStyle`). -/
public inductive Decl where
  | style (s : Style)
  | color (c : Color) (name : Option String)
  deriving Repr, BEq

/-- One declaration around a region: exactly the node its grouped
spelling elaborates to (`{\footnotesize B}` is `.styled (size) B`). -/
public def Decl.wrap : Decl → Array Inline → Array Inline
  | .style s, xs => #[.styled s xs]
  | .color c n, xs => #[.colored c n xs]

/-- The constructor selected by each declaration around a content region. -/
public theorem Decl.wrap_exact (d : Decl) (xs : Array Inline) :
    d.wrap xs = (match d with
      | .style s => #[.styled s xs]
      | .color c name => #[.colored c name xs]) := by
  cases d <;> rfl

/-- The open declarations around a region, outermost first. -/
public def wrapDecls (ds : List Decl) (xs : Array Inline) : Array Inline :=
  match ds with
  | [] => xs
  | d :: rest => d.wrap (wrapDecls rest xs)

/-- The declaration list is applied from its innermost wrapper outwards. -/
public theorem wrapDecls_exact (ds : List Decl) (xs : Array Inline) :
    wrapDecls ds xs = (match ds with
      | [] => xs
      | d :: rest => d.wrap (wrapDecls rest xs)) := by
  cases ds <;> rfl

public theorem Decl.wrap_text (d : Decl) (xs : Array Inline) :
    plainText (d.wrap xs) = plainText xs := by
  cases d <;> simp [Decl.wrap, plainText, plainTextList, plainTextOne]

/-- A declaration is markup, never content: the region ships exactly the
census it had. -/
public theorem wrapDecls_text (ds : List Decl) : Conserves plainText (wrapDecls ds) := fun xs => by
  induction ds with
  | nil => rfl
  | cons d rest ih => simp only [wrapDecls, Decl.wrap_text, ih]

mutual

-- conserves: none — a census, not a rewrite: it reads the tree and returns
-- the text standing under a style the predicate accepts.
/-- The text of inline content that stands under some `.styled st` with
`p st`: what a size or weight declaration is worth on the page. Under an
accepted style everything counts; elsewhere the walk reads through the
wrappers to the styled runs below. The list face threads its
accumulator. -/
public def textUnder (p : Style → Bool) (x : Inline) : String :=
  match x with
  | .styled st body =>
    if p st then plainTextList body.toList else textUnderList p "" body.toList
  | .colored _ _ body => textUnderList p "" body.toList
  | .located _ body => textUnderList p "" body.toList
  | .role _ body => textUnderList p "" body.toList
  | .link _ body => textUnderList p "" body.toList
  | .decorated _ body => textUnderList p "" body.toList
  | .onSteps _ body => textUnderList p "" body.toList
  | .altSteps _ firstPage otherPage =>
    textUnderList p (textUnderList p "" firstPage.toList) otherPage.toList
  | .footnote _ body => textUnderList p "" body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ => ""

public def textUnderList (p : Style → Bool) (acc : String) (xs : List Inline) : String :=
  match xs with
  | [] => acc
  | x :: rest => textUnderList p (acc ++ textUnder p x) rest

end

/-- Whether some open declaration is a style the predicate accepts. -/
public def Decl.anyStyle (p : Style → Bool) : List Decl → Bool
  | [] => false
  | .style s :: rest => p s || Decl.anyStyle p rest
  | .color _ _ :: rest => Decl.anyStyle p rest

/-- A declaration standing between blocks scopes every following block of
its group: once a style the predicate accepts is among the open
declarations, the text standing under it in any region built in that
scope is the region's whole census — no character of the scope escapes
the declaration, and none is added. This is how the `\footnotesize`
before a tabular reaches the cells, where the inline reading left an
empty styled paragraph beside a body-size table. Shape `_covers`. -/
public theorem decl_between_blocks_covers (p : Style → Bool) (ds : List Decl)
    (hd : Decl.anyStyle p ds = true) (xs : Array Inline) :
    textUnderList p "" (wrapDecls ds xs).toList = plainText xs := by
  induction ds with
  | nil => simp [Decl.anyStyle] at hd
  | cons d rest ih =>
    cases d with
    | style s =>
      simp only [Decl.anyStyle, Bool.or_eq_true] at hd
      simp only [wrapDecls, Decl.wrap]
      have hw : plainTextList (wrapDecls rest xs).toList = plainText xs :=
        wrapDecls_text rest xs
      show textUnderList p ("" ++ textUnder p (.styled s _)) [] = _
      rcases hd with h | h
      · simp [textUnderList, textUnder, h, hw]
      · cases hp : p s
        · simp [textUnderList, textUnder, hp, ih h]
        · simp [textUnderList, textUnder, hp, hw]
    | color c n =>
      simp only [Decl.anyStyle] at hd
      simp only [wrapDecls, Decl.wrap]
      show textUnderList p ("" ++ textUnder p (.colored c n _)) [] = _
      simp [textUnderList, textUnder, ih hd]

/-- The two spellings agree: the declaration read between blocks wraps a
region in exactly the node the grouped spelling `{\footnotesize B}`
elaborates to. Shape `_agree`. -/
public theorem decl_spellings_agree (s : Style) (xs : Array Inline) :
    wrapDecls [.style s] xs = #[.styled s xs] := by rfl

/-- One character of a label's anchor: Unicode characters, ASCII word
characters and the punctuation label keys conventionally carry (`fig:flow`,
`eq.1`, `a-b`, `x_y`) survive verbatim. HTML ids permit non-ASCII characters;
folding them would collapse distinct authored targets. Other ASCII
characters — whitespace included — fold to a hyphen. -/
private def labelAnchorChar (c : Char) : Char :=
  if c.toNat ≥ 0x80 || c.isAlpha || c.isDigit || c == ':' || c == '.' ||
      c == '-' || c == '_' then c
  else '-'

/-- The id a `\label` key takes in the HTML page and a resolved reference
targets: the key sanitised character-wise — one resolving site for both
ends, so a link and its anchor cannot disagree. An empty key still yields
an id, HTML §3.2.6's non-emptiness. Two distinct keys can fold to one
anchor only when they differ in folded characters, which the key
conventions above never use. -/
public def labelAnchor (key : String) : String :=
  match key.toList.map labelAnchorChar with
  | [] => "label"
  | l => String.ofList l

/-- Every nonempty key in the supported alphabet keeps its exact spelling
at the one resolving site both an anchor and its link read. In particular,
distinct Unicode keys remain distinct, without relaxing ASCII safety. -/
public theorem labelAnchor_fixed_point (key : String) (hne : key ≠ "")
    (hkeep : ∀ c ∈ key.toList,
      (c.toNat ≥ 0x80 || c.isAlpha || c.isDigit || c == ':' || c == '.' ||
        c == '-' || c == '_') = true) :
    labelAnchor key = key := by
  have hm : key.toList.map labelAnchorChar = key.toList := by
    have h := List.map_congr_left (l := key.toList) (f := labelAnchorChar) (g := id)
      (fun c hc => by simp [labelAnchorChar, hkeep c hc])
    simpa using h
  unfold labelAnchor
  rw [hm]
  split
  · rename_i he
    exact False.elim (hne (String.toList_eq_nil_iff.mp he))
  · exact String.ofList_toList

/-- The sanitiser never lets a character through that the kept set refuses:
whatever the key spelled, the anchor's characters are non-ASCII, word
characters, the kept punctuation, or the fold hyphen — never `bad`. -/
private theorem labelAnchorChar_not (c bad : Char)
    (hbad : (bad.toNat ≥ 0x80 || bad.isAlpha || bad.isDigit || bad == ':' ||
      bad == '.' || bad == '-' || bad == '_') = false) :
    labelAnchorChar c ≠ bad := by
  unfold labelAnchorChar
  split <;> rintro rfl <;> simp_all

/-- The label key is author text entering an `id` attribute and an `href`,
so it owes the same statement `roleClass_single_token` makes for authored
class names: no character of an anchor is ASCII whitespace (HTML §3.2.6's
id contract) or a quote (the attribute-breakout characters `escapeAttr`
kills). Here the statement needs no alphabet hypothesis — the sanitiser is
total over whatever the document spelled. -/
public theorem labelAnchor_single_token (key : String) :
    ((labelAnchor key).toList.all fun c =>
      !(c == ' ' || c == '\t' || c == '\n' || c == '\r' ||
        c == '"' || c == '\'')) = true := by
  unfold labelAnchor
  split
  · decide
  · simp only [String.toList_ofList, List.all_eq_true, List.mem_map]
    rintro c ⟨a, _, rfl⟩
    have h1 := labelAnchorChar_not a ' ' (by decide)
    have h2 := labelAnchorChar_not a '\t' (by decide)
    have h3 := labelAnchorChar_not a '\n' (by decide)
    have h4 := labelAnchorChar_not a '\r' (by decide)
    have h5 := labelAnchorChar_not a '"' (by decide)
    have h6 := labelAnchorChar_not a '\'' (by decide)
    simp [h1, h2, h3, h4, h5, h6]

/-- What a label names: the kind of the numbered thing it bound to, read
by cleveref's name prefixes (`crefNameOf`). The engine's numbered things
are its headings, its display equations, and its captioned floats — a
label under a subfloat takes the parent float's kind, as cleveref's
subfigure names are the figure's. -/
public inductive RefKind where
  | heading | equation | figure | table | algorithm
  deriving Repr, BEq

/-- One label's binding: the number it bound to, with the kind of the
numbered thing when elaboration made one. A binding the engine numbers
without a node of any kind — a bare `\refstepcounter` — carries `none`:
what such a label names has no kind, so a `\cref` to it sets the plain
number, named (W0380). -/
public structure RefBinding where
  kind : Option RefKind
  num : String
  deriving Repr, BEq

/-! ## The keyed index

Every keyed store in this engine is an association array read by
`find? (·.1 == k)`: it holds declaration order, which several stores make
observable (a palette's CSS variables, a style's cascade, a token defined
in terms of an earlier one). Order is therefore not negotiable, so the
fast lookup is an *index beside* the array, never a replacement for it —
`keyIndex_find?` is the one equation that makes the two answers the same,
so a pass may read the index while every theorem keeps stating `find?`.

First-wins insertion is what makes the equation hold: `Array.find?`
answers with the earliest match, so a key already indexed is never
overwritten by a later duplicate. -/

private def indexStep {α : Type} (m : Std.HashMap String (String × α))
    (e : String × α) : Std.HashMap String (String × α) :=
  if m.contains e.1 then m else m.insert e.1 e

/-- The lookup index of a keyed store: each key to its earliest entry. -/
public def keyIndex {α : Type} (xs : Array (String × α)) :
    Std.HashMap String (String × α) :=
  xs.foldl (init := ∅) indexStep

private theorem absent_of_getElem?_none {α : Type}
    (m : Std.HashMap String (String × α)) (k : String) (h : m[k]? = none) :
    m.contains k = false := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, h]
  rfl

private theorem key_ne_of_absent {α : Type} (m : Std.HashMap String (String × α))
    (e : String × α) (k : String) (hc : m.contains e.1 = true) (hk : m[k]? = none) :
    (e.1 == k) = false := by
  cases hEq : (e.1 == k) with
  | true =>
    rw [eq_of_beq hEq, absent_of_getElem?_none m k hk] at hc
    exact absurd hc (by simp)
  | false => rfl

private theorem absent_of_beq {α : Type} (m : Std.HashMap String (String × α))
    (e : String × α) (k : String) (hc : m.contains e.1 = false)
    (hEq : (e.1 == k) = true) : m[k]? = none := by
  rw [eq_of_beq hEq, Std.HashMap.contains_eq_isSome_getElem?] at hc
  simpa using hc

private theorem indexList {α : Type} :
    ∀ (l : List (String × α)) (m : Std.HashMap String (String × α)) (k : String),
      (l.foldl indexStep m)[k]? = m[k]?.or (l.find? (·.1 == k))
  | [], m, k => by cases h : m[k]? <;> simp [h]
  | e :: rest, m, k => by
    rw [List.foldl_cons, indexList rest]
    cases hc : m.contains e.1 with
    | true =>
      cases hk : m[k]? with
      | some v => simp [indexStep, hc, hk]
      | none => simp [indexStep, hc, hk, key_ne_of_absent m e k hc hk]
    | false =>
      cases hEq : (e.1 == k) with
      | true =>
        have hk := absent_of_beq m e k hc hEq
        have hstep : indexStep m e = m.insert e.1 e := by simp [indexStep, hc]
        rw [hstep, Std.HashMap.getElem?_insert, hEq]
        simp [hk, hEq]
      | false => simp [indexStep, hc, hEq, Std.HashMap.getElem?_insert]

/-- **The index answers exactly what the scan answers.** Every keyed store
this engine reads is an `Array (String × α)` scanned by `find?`; the index
is the same question asked in constant time, on the same array, with the
same first-wins tie-break. So a pass may read the index and keep every
`find?`-stated theorem it already had, unweakened: rewriting with this
equation turns the one into the other. -/
public theorem keyIndex_find? {α : Type} (xs : Array (String × α)) (k : String) :
    (keyIndex xs)[k]? = xs.find? (·.1 == k) := by
  unfold keyIndex
  rw [← Array.foldl_toList, indexList, Std.HashMap.getElem?_empty,
    ← Array.find?_toList]
  rfl

/-- The label table resolution spends: each key with the binding its
`\label` took in flow order (`none`: the label stood where nothing
numbers). Elaboration builds it — the first declaration of a key wins,
W0350 names the rest — and `resolveRefs` is the single pass over the IR
that resolves every reference against it, so no backend re-scans for
labels. -/
public abbrev RefTable := Array (String × Option RefBinding)

/-- cleveref's name for a kind: the one resolving site both `refText`
readers use, so `\cref` and `\namecref` cannot disagree on a kind's name.
Every heading level takes the section name, as cleveref's subsection
names are the section's own (its english block). -/
public def crefNameOf (loc : Locale) : RefKind → CrefName
  | .heading => loc.crefSection
  | .equation => loc.crefEquation
  | .figure => loc.crefFigure
  | .table => loc.crefTable
  | .algorithm => loc.crefAlgorithm

/-- Every kind, for the coverage contract: an added constructor fails
`all_complete` until it is listed, and listed is covered
(`crefNameOf_covers`) — the DiagCode registry's shape. -/
public def RefKind.all : List RefKind :=
  [.heading, .equation, .figure, .table, .algorithm]

public theorem RefKind.all_complete (k : RefKind) : RefKind.all.contains k := by
  cases k <;> rfl

/-- Every label kind the engine assigns has its cleveref names, all four
forms, in every shipped locale — with the range conjunction beside them.
Quantified over `Locale.builtin` (adding a locale is entering the
contract) and `RefKind.all` (complete by `RefKind.all_complete`): the
statement behind `\cref` never printing an empty name. -/
public theorem crefNameOf_covers :
    (Locale.builtin.all fun l =>
      (RefKind.all.all fun k =>
        !(crefNameOf l k).one.isEmpty && !(crefNameOf l k).many.isEmpty &&
        !(crefNameOf l k).capOne.isEmpty && !(crefNameOf l k).capMany.isEmpty)
      && !l.crefRangeTo.isEmpty) = true := by decide +kernel

/-- A cref-form number: equation numbers keep their parentheses in every
cleveref form (cleveref.sty `\creflabelformat{equation}{...\textup{(#1)}}`);
every other kind shows the bare number. -/
public def crefNum (b : RefBinding) : String :=
  if b.kind == some .equation then "(" ++ b.num ++ ")" else b.num

/-- The text one resolved reference shows, the one rendering site
(`resolveOneRef` and its theorems read it): `\ref`'s bare number,
`\eqref`'s parentheses, and cleveref's forms over the binding's kind —
name and number joined by the package's own no-break space. A kindless
binding (a bare `\refstepcounter`) sets the plain number under every
cleveref form, and W0349's judge names it (W0380). -/
public def refText (loc : Locale) (form : RefForm) (b : RefBinding) : String :=
  let numText := crefNum b
  match form with
  | .plain => b.num
  | .paren => "(" ++ b.num ++ ")"
  | .labelOnly => numText
  | .cref cap =>
    match b.kind with
    | some k =>
      (if cap then (crefNameOf loc k).capOne else (crefNameOf loc k).one)
        ++ "\u00a0" ++ numText
    | none => b.num
  | .crefRange cap =>
    (match b.kind with
     | some k =>
       (if cap then (crefNameOf loc k).capMany else (crefNameOf loc k).many)
         ++ "\u00a0" ++ numText
     | none => b.num)
      ++ " " ++ loc.crefRangeTo ++ "\u00a0"
  | .name cap =>
    match b.kind with
    | some k => if cap then (crefNameOf loc k).capOne else (crefNameOf loc k).one
    | none => b.num

/-- One reference against a lookup. The table is reached through a function
rather than scanned in place, so the same match serves the scan and the
index beside it — `resolveOneRef` is this at the scan, `resolveRefs` this at
the index, and the two differ by a function equality, never by a case. -/
public def resolveOneRefWith (loc : Locale)
    (look : String → Option (String × Option RefBinding)) (key : String)
    (form : RefForm) : Inline :=
  match look key with
  | some (_, some b) =>
    .ref key form (refText loc form b) (some (labelAnchor key))
  | _ => .ref key form "??" none

/-- One reference against the table. A key bound to a number takes exactly
its form's text over the binding (`refText`) and the label's anchor; a key
the table cannot number keeps LaTeX's own `??` and no target (the
elaborator has already named it, W0349). -/
public def resolveOneRef (loc : Locale) (table : RefTable) (key : String)
    (form : RefForm) : Inline :=
  resolveOneRefWith loc (fun k => table.find? (·.1 == k)) key form

/-- Resolution at the scan, written out: the equation every `resolveOneRef`
theorem is proved through, so factoring the lookup out as a parameter cost
the statements nothing. -/
public theorem resolveOneRef_scan (loc : Locale) (table : RefTable) (key : String)
    (form : RefForm) :
    resolveOneRef loc table key form =
      match table.find? (·.1 == key) with
      | some (_, some b) =>
        .ref key form (refText loc form b) (some (labelAnchor key))
      | _ => .ref key form "??" none := by rfl

/-- Resolution's one rewrite: every `.ref` is rewritten from the lookup
(`resolveOneRef_exact` is its statement), everything else keeps its shape
and is walked by the generic map. -/
private def resolveRefLeaf (loc : Locale)
    (look : String → Option (String × Option RefBinding))
    (x : Inline) : Inline :=
  match x with
  | .ref key form _ _ => resolveOneRefWith loc look key form
  | _ => x

/-- The table read as a lookup: resolution's scan face, the one every
theorem states. -/
public def refScan (table : RefTable) : String → Option (String × Option RefBinding) :=
  fun k => table.find? (·.1 == k)

/-- **The index answers the scan's question.** The lookup a resolution pass
reads is the index beside the table, and this is the one step that makes
that the same lookup the theorems state: the two functions are equal, so
every `resolveOneRef` statement is a statement about the indexed pass too.
Resolution's cost changed; its meaning did not. -/
public theorem refLook_agree (table : RefTable) :
    (fun k => (keyIndex table)[k]?) = refScan table := by
  funext k
  exact keyIndex_find? table k

/-- The pass over an index already built. The index is a *parameter*, not a
`let` inside the leaf: Lean is strict, so an argument is evaluated once
before the call, while a binding used once inside a lambda can be inlined
back into it — which rebuilt the index per reference and cost 12× the scan
it replaced. -/
private def resolveRefsIdx (loc : Locale)
    (idx : Std.HashMap String (String × Option RefBinding))
    (xs : Array Block) : Array Block :=
  -- No label holds a reference: the label reader refuses `\ref` and drops
  -- its key (`Picture.salCtrl`).
  mapBlocks (resolveRefLeaf loc (fun k => idx[k]?)) xs

private def resolveRefInlinesIdx (loc : Locale)
    (idx : Std.HashMap String (String × Option RefBinding))
    (xs : Array Inline) : Array Inline :=
  mapInlines (resolveRefLeaf loc (fun k => idx[k]?)) xs

-- conserves: none — resolution rewrites a ref's placeholder text to its
-- number, which is the pass's whole point; `resolveOneRef_exact` is its
-- statement.
public def resolveRefInline (loc : Locale) (table : RefTable) (x : Inline) : Inline :=
  mapInline (resolveRefLeaf loc (refScan table)) x

-- conserves: none — the block face of resolveRefInline, same reason.
public def resolveRefs (loc : Locale) (table : RefTable) (xs : Array Block) : Array Block :=
  resolveRefsIdx loc (keyIndex table) xs

/-- The indexed block pass applies exactly the table's reference rewrite
through the generic map. Its public equation names `resolveOneRef`; the
lookup adapter and index traversal remain implementation details. -/
public theorem resolveRefs_agree (loc : Locale) (table : RefTable) (xs : Array Block) :
    resolveRefs loc table xs = mapBlocks (fun x => match x with
      | .ref key form _ _ => resolveOneRef loc table key form
      | _ => x) xs := by
  unfold resolveRefs resolveRefsIdx
  rw [refLook_agree]
  congr 1

/-- References resolve to what they name: when the table binds `key` to
binding `b` — elaboration binds a key declared exactly once to the numbered
node in force where its `\label` stood — the resolved reference shows
exactly its form's text over `b` (`refText`) and targets exactly that
label's anchor. The `\ref` and the `\label` cannot disagree, because both
read this one entry. -/
public theorem resolveOneRef_exact (loc : Locale) (table : RefTable) (key : String)
    (form : RefForm)
    (b : RefBinding) (h : ∃ e ∈ table, e.1 = key ∧ e.2 = some b)
    (huniq : ∀ e ∈ table, e.1 = key → e.2 = some b) :
    resolveOneRef loc table key form =
      .ref key form (refText loc form b)
        (some (labelAnchor key)) := by
  rw [resolveOneRef_scan]
  obtain ⟨e, hmem, hkey, hval⟩ := h
  have hfind : ∃ f, table.find? (·.1 == key) = some f := by
    have : (table.find? (·.1 == key)).isSome := by
      rw [Array.find?_isSome]
      exact ⟨e, hmem, by simp [hkey]⟩
    exact Option.isSome_iff_exists.mp this
  obtain ⟨f, hf⟩ := hfind
  have hfmem := Array.mem_of_find?_eq_some hf
  have hfkey : f.1 = key := by
    have := Array.find?_some hf
    simpa using this
  have hfval : f.2 = some b := huniq f hfmem hfkey
  obtain ⟨fk, fv⟩ := f
  simp only at hfval
  subst hfval
  rw [hf]

/-- An unreferencable key resolves to LaTeX's own `??`, never silently to
a number: the reader sees that something stands unresolved, and W0349 has
already named the key. -/
public theorem resolveOneRef_missing (loc : Locale) (table : RefTable) (key : String)
    (form : RefForm) (h : ∀ e ∈ table, e.1 ≠ key) :
    resolveOneRef loc table key form = .ref key form "??" none := by
  rw [resolveOneRef_scan]
  have hfind : table.find? (·.1 == key) = none := by
    rw [Array.find?_eq_none]
    intro e hmem
    simp [h e hmem]
  rw [hfind]

/-- The inline face of `resolveRefs`, for the furniture regions `mapDoc`
hands it: the same leaf, so a `\ref` in a running head resolves as one in
the body does. -/
-- conserves: none — the inline-region face of resolveRefs, same reason.
public def resolveRefInlines (loc : Locale) (table : RefTable) (xs : Array Inline) :
    Array Inline :=
  resolveRefInlinesIdx loc (keyIndex table) xs

/-- The inline-region pass reads the index and means the scan, the twin of
`resolveRefs_agree`: a `\ref` in a running head resolves as one in the body
does, off the same index. -/
private theorem resolveRefInlines_agree (loc : Locale) (table : RefTable) (xs : Array Inline) :
    resolveRefInlines loc table xs = mapInlines (resolveRefLeaf loc (refScan table)) xs := by
  unfold resolveRefInlines resolveRefInlinesIdx
  rw [refLook_agree]

/-! ## The pending census

What the engine could not resolve and a backend would otherwise ship
unnamed: a `\ref` no label numbers, a `\cite` no bibliography answered, an
image no file or tool produced. Each resolver names what it leaves — W0349,
W0351, W0601/W0602/E0382/W0379 — and `pending_named` (Pending.lean) holds
the census to those diagnostics, so "a warning per misunderstood thing" is
a theorem over the pipeline's pure tail, not a convention each resolver
keeps by hand. The silent `\cite` with no bibliography was that convention
failing. -/

/-- One unresolved node the IR itself carries, by the key a diagnostic can
be matched to. -/
public inductive Unresolved where
  | ref (key : String)
  | cite (key : String)
  deriving Repr, BEq, DecidableEq

@[expose] public def Unresolved.isCite : Unresolved → Bool
  | .cite _ => true
  | .ref _ => false

/-- One pending thing a backend would ship unnamed: a node of the IR, or an
image source the store holds no payload for. -/
public inductive Pending where
  | node (u : Unresolved)
  | image (src : String)
  deriving Repr, BEq, DecidableEq

public def Pending.key : Pending → String
  | .node (.ref k) => k
  | .node (.cite k) => k
  | .image s => s

/-- A diagnostic names a pending node when its structured subject is the
node's key: a lookup, never a search of the message text. -/
public def _root_.LeanTex.Core.Diag.mentions (d : Diag) (p : Pending) : Bool :=
  d.subject == some p.key

/-- One node's contribution: a `.ref` still carrying no target is
unresolved (`resolveOneRef` sets a target for every key it numbers); a
`.cite` is unresolved by existence — `Bib.apply` replaces every one. Nodes
are listed, not deduplicated: the census counts occurrences, the judges
name keys. -/
@[expose] public def pendingLeaf : Inline → Array Unresolved
  | .ref key _ _ none => #[.ref key]
  | .cite _ keys => keys.map .cite
  | _ => #[]

/-- The fold step of the census: each node's leaf appended. -/
@[expose] public def pendingStep (acc : Array Unresolved) (x : Inline) : Array Unresolved :=
  let leaf := pendingLeaf x
  acc ++ leaf

/-- Every unresolved reference and citation the document's regions carry,
in document order — a `foldDoc` leaf, so the descent is the fold's. -/
@[expose] public def pendingNodes (doc : Doc) : Array Unresolved :=
  foldDoc pendingStep #[] doc

/-- Every image source the document names that the store holds no payload
for — the placeholder boxes every consumer places. -/
public def pendingImages (doc : Doc) (store : Image.Store) : Array Pending :=
  ((imageRequests doc).filter fun req => (store.infoRequest? req).isNone).map
    (fun req => .image req.src)

/-- The census: everything a backend would ship as `??`, `?`, or a
placeholder box, over the document and the store the backends read. -/
public def pending (doc : Doc) (store : Image.Store) : Array Pending :=
  let images := pendingImages doc store
  (pendingNodes doc).map .node ++ images

/-- The distinct keys of the unresolved references, first occurrence
first: what W0349 names, once per key. -/
public def pendingRefKeys (doc : Doc) : Array String :=
  (pendingNodes doc).foldl (init := #[]) fun out p =>
    match p with
    | .ref k => if out.contains k then out else out.push k
    | .cite _ => out

/-- W0349's judge, read off the resolved IR: every distinct key a `\ref`
still shows `??` for, named at its first site (`spanOf`) with the cause
the table knows — a `\label` that stood where nothing numbers, or no
`\label` at all. It reads the census the gate quantifies over, so a
reference cannot escape it without escaping the fold whose arms are all
explicit (`refDiags_named`). -/
private def refDiagLeaf (look : String → Option (String × Option RefBinding))
    (spanOf : String → Option Span) (key : String) : Diag :=
  match look key with
  | some (_, none) =>
    Diag.of .W0349 s!"'{key}' is \\label'ed where nothing is numbered; set as '??'"
      (spanOf key)
      (help := "move the \\label after a numbered heading, a captioned float, or into an equation")
      (subject := some key)
  | _ =>
    Diag.of .W0349 s!"no \\label\{{key}} in the document; set as '??'" (spanOf key)
      (help := s!"declare \\label\{{key}} after the numbered thing it names")
      (subject := some key)

private def refDiagsIdx (idx : Std.HashMap String (String × Option RefBinding))
    (spanOf : String → Option Span) (keys : Array String) : Array Diag :=
  keys.map (refDiagLeaf (fun k => idx[k]?) spanOf)

public def refDiags (table : RefTable) (spanOf : String → Option Span) (doc : Doc) :
    Array Diag :=
  refDiagsIdx (keyIndex table) spanOf (pendingRefKeys doc)

/-- The judge reads the index and means the scan: `refLook_agree` under the
leaf, so W0349's census is the one the table states. -/
private theorem refDiags_agree (table : RefTable) (spanOf : String → Option Span) (doc : Doc) :
    refDiags table spanOf doc
      = (pendingRefKeys doc).map (refDiagLeaf (refScan table) spanOf) := by
  unfold refDiags refDiagsIdx
  rw [refLook_agree]

/-- The key fold only grows its accumulator. -/
private theorem pendingRefKeys_grow (l : List Unresolved) :
    ∀ (out : Array String) (k : String), k ∈ out →
      k ∈ l.foldl (init := out) fun out p => match p with
        | .ref k => if out.contains k then out else out.push k
        | .cite _ => out := by
  induction l with
  | nil => intro out k hk; simpa using hk
  | cons p rest ih =>
    intro out k hk
    simp only [List.foldl_cons]
    apply ih
    cases p with
    | ref k' =>
      show k ∈ (if out.contains k' = true then out else out.push k')
      split <;> simp [hk]
    | cite _ => exact hk

private theorem pendingRefKeys_mem (doc : Doc) (key : String)
    (h : Unresolved.ref key ∈ pendingNodes doc) : key ∈ pendingRefKeys doc := by
  unfold pendingRefKeys
  rw [← Array.foldl_toList]
  rw [Array.mem_def] at h
  generalize (pendingNodes doc).toList = l at h ⊢
  generalize (#[] : Array String) = out
  induction l generalizing out with
  | nil => simp at h
  | cons p rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hrest
    · apply pendingRefKeys_grow
      show key ∈ (if out.contains key = true then out else out.push key)
      split
      · rename_i hc; exact Array.contains_iff_mem.mp hc
      · simp
    · exact ih hrest _

/-- **Every unresolved reference is named**: a `.ref` the census lists has
a W0349 in the judge's output whose subject is its key. -/
public theorem refDiags_named (table : RefTable) (spanOf : String → Option Span) (doc : Doc)
    (key : String) (h : Unresolved.ref key ∈ pendingNodes doc) :
    ∃ d ∈ refDiags table spanOf doc, d.mentions (.node (.ref key)) = true := by
  have hk := pendingRefKeys_mem doc key h
  rw [refDiags_agree]
  unfold refDiagLeaf refScan
  refine ⟨_, Array.mem_map_of_mem hk, ?_⟩
  cases hf : table.find? (·.1 == key) with
  | none => simp [Diag.mentions, Diag.of_subject, Pending.key]
  | some e =>
    obtain ⟨_, b⟩ := e
    cases b <;> simp [Diag.mentions, Diag.of_subject, Pending.key]

-- Float label rows. Elaboration cannot know a float's number — `numberFloats`
-- assigns it once the whole body exists — so the table's float rows are read
-- off the numbered IR by this collect, and no second numbering exists to
-- disagree with (`refs_agree_with_numbering` is the statement a predictor
-- could only hope for).

/-- One label leaf into the rows, bound to the float binding in force. -/
private def floatLabelPush (float : Option RefBinding)
    (out : Array (String × Option RefBinding)) : Inline → Array (String × Option RefBinding)
  | .label k => out.push (k, float)
  | _ => out

/-- The float binding in force at every `.label` of the numbered IR, in
document order. `float` is the enclosing captioned float's rendering —
`none` outside every captioned float — and every label is reported, bound
or not, so a key's first row is its first declaration and a later
duplicate inside a float can never override it (`withFloatRows` reads only
the first). A captioned float binds its number over its own extent, the
caption included; a captionless one leaves the enclosing binding in
force; a captioned subfloat binds its parent's number plus its letter
(subcaption manual §"Referencing subfigures": `\ref` shows `1a`, the
figure number then `\alph`); an equation's content and a section's title
bind to numbers elaboration already recorded, so their labels report
unbound here. The IR keeps a float body's labels but not their side of
the caption, so a label anywhere under a captioned float binds to it —
LaTeX documents `\label` before `\caption` as a user error (clsguide §"The
label commands"); here it resolves to the number the author captioned.

The binding is the walk's context, so this is the open event and nothing
else: `foldCtxBlock` owns the descent, and the arms below say only what
each block does to the binding its content is read under. The explicit
arms are the obligation table's, kept here because a new constructor must
declare which binding it passes down. -/
public def floatLabelEnter (float : Option RefBinding) (out : Array (String × Option RefBinding))
    (b : Block) : Array (String × Option RefBinding) × Option RefBinding :=
  match b with
  -- an equation's content and a section's title number at elaboration
  | .equation _ _ | .section _ _ _ _ => (out, none)
  | .float kind num _ _ _ =>
    (out, match num with
      | none => float
      | some m =>
        match kind with
        -- A subfloat letters under its parent: the binding keeps the
        -- parent's kind, as cleveref's subfigure names are the figure's.
        | .sub => some { kind := float.bind (·.kind)
                         num := ((float.map (·.num)).getD "") ++ subLetter m }
        | .figure => some { kind := some .figure, num := toString m }
        | .table => some { kind := some .table, num := toString m }
        | .algorithm => some { kind := some .algorithm, num := toString m })
  | .para _ | .list _ _ | .center _ | .ragged _ _ | .quote _ | .abstract _
  | .titled _ _ _ | .role _ _ | .link _ _ | .spaced _ _ | .columns _ | .onSteps _ _
  | .altSteps _ _ _ | .only _ _ | .nav _ _ | .note _ | .frame _ _ _ _ _
  | .framefoot _ | .table _ _ _ _ _ _ | .algorithm _ _ _ | .logo _
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .bibliography _ _ _ => (out, float)

/-- The label walk: `floatLabelEnter` binds, `floatLabelPush` collects, the
shared context fold descends. -/
public def floatLabelWalk : CtxFold (Option RefBinding) (Array (String × Option RefBinding)) where
  openBlock := floatLabelEnter
  closeBlock := fun _ out _ => out
  openInline := fun float out x => (floatLabelPush float out x, float)
  closeInline := fun _ out _ => out

/-- The float rows of the numbered body: every label with the float binding
in force where it stands, the table's float half. -/
public def floatLabelRows (xs : Array Block) : RefTable :=
  foldCtxBlocks floatLabelWalk none #[] xs

/-- The label table with its float rows filled from the numbered IR: an
entry whose key's first `.label` stands under a captioned float takes that
float's number; every other entry keeps elaboration's binding (headings
and equations number at elaboration; a key bound nowhere keeps `none` and
W0349 names it). `rows` is `floatLabelRows` over the numbered body. -/
private def floatRowLeaf (look : String → Option (String × Option RefBinding))
    (e : String × Option RefBinding) : String × Option RefBinding :=
  match look e.1 with
  | some (_, some n) => (e.1, some n)
  | _ => e

/-- The merge over an index already built. The index is a *parameter*, not
a `let` inside the mapped function: Lean is strict, so an argument is
evaluated once before the call, while a binding used once inside a lambda
can be inlined back into it — which rebuilt the whole index per label and
cost 32× the scan it replaced. -/
private def withFloatRowsIdx (labels : RefTable)
    (idx : Std.HashMap String (String × Option RefBinding)) : RefTable :=
  labels.map (floatRowLeaf (fun k => idx[k]?))

public def withFloatRows (labels rows : RefTable) : RefTable :=
  withFloatRowsIdx labels (keyIndex rows)

/-- The merge reads the index and means the scan: `refLook_agree` under the
leaf, the equation `withFloatRows_finds` is proved through. -/
private theorem withFloatRows_agree (labels rows : RefTable) :
    withFloatRows labels rows
      = labels.map (floatRowLeaf (refScan rows)) := by
  unfold withFloatRows withFloatRowsIdx
  rw [refLook_agree]

/-- The merge keeps keys and takes exactly the collect's binding: when the
collect's first row for `key` carries a number and elaboration recorded
the key at all, the merged table's answer for `key` is that number. -/
public theorem withFloatRows_finds (labels rows : RefTable) (key : String) (b : RefBinding)
    (hrow : rows.find? (·.1 == key) = some (key, some b))
    (hkey : (labels.find? (·.1 == key)).isSome) :
    (withFloatRows labels rows).find? (·.1 == key) = some (key, some b) := by
  rw [withFloatRows_agree]
  unfold refScan
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hkey
  have hekey : e.1 = key := by simpa using Array.find?_some he
  rw [Array.find?_map]
  have hp : ((fun x : String × Option RefBinding => x.1 == key) ∘
      floatRowLeaf (fun k => rows.find? (·.1 == k)))
      = fun e : String × Option RefBinding => e.1 == key := by
    funext x
    cases hx : rows.find? (·.1 == x.1) with
    | none => simp [Function.comp, floatRowLeaf, hx]
    | some p =>
      obtain ⟨pk, pv⟩ := p
      cases pv <;> simp [Function.comp, floatRowLeaf, hx]
  rw [hp, he, Option.map_some]
  unfold floatRowLeaf
  rw [hekey]
  simp [hrow]

/-- Floats are numbered once, from the proved walk. `numberFloats` assigns
every captioned float's number (`numberFloats_exact`: gapless, 1-based,
document order), `floatLabelRows` reads those numbers off the numbered
nodes where each `\label` stands, `withFloatRows` carries them into the
table, and resolution shows precisely that entry: a resolved reference to
a float shows exactly the number the float node carries, and targets the
label's anchor. Before this pipeline, elaboration *predicted* the number
and nothing related predictor to assigner; now there is no predictor, and
the agreement is this theorem, stated over the engine's own functions. -/
public theorem refs_agree_with_numbering (loc : Locale) (labels : RefTable) (xs : Array Block)
    (key : String) (b : RefBinding) (form : RefForm) (t : String) (a : Option String)
    (hrow : (floatLabelRows (numberFloats xs)).find? (·.1 == key)
      = some (key, some b))
    (hkey : (labels.find? (·.1 == key)).isSome) :
    resolveRefInline loc (withFloatRows labels (floatLabelRows (numberFloats xs)))
        (.ref key form t a)
      = .ref key form (refText loc form b)
        (some (labelAnchor key)) := by
  have h := withFloatRows_finds labels _ key b hrow hkey
  show resolveOneRef _ _ key form = _
  rw [resolveOneRef_scan]
  rw [h]

private def dumpDiag (d : Diag) : String :=
  let where' := match d.span with
    | some sp => s!"{sp.pos.line}:{sp.pos.col}"
    | none => "-"
  let help := match d.help with
    | some h => s!" | help: {h}"
    | none => ""
  s!"{d.severity.label}[{d.code}] {where'} {d.message}{help}\n"

public def dump (doc : Doc) (diags : Array Diag) : String :=
  let opts := if doc.classOptions == "" then "" else s!" [{doc.classOptions}]"
  let head := s!"class {doc.docClass.name}{opts}\n"
  let page :=
    s!"page {doc.page.width.toPtString}x{doc.page.height.toPtString} " ++
    s!"vmargin {doc.page.vmargin.toPtString} hmargin {doc.page.hmargin.toPtString}" ++
    (if doc.page.fontSize != baseFontSize
      then s!" fontsize {doc.page.fontSize.toPtString}" else "") ++
    (match doc.page.sizes with
      | some sc => String.join ((sc.filter fun p =>
          sizeScale.lookup p.1 != some p.2).map fun p => s!" size {p.1} {p.2}")
      | none => "") ++
    (match doc.page.parskip with
      | some g => s!" parskip {dumpGlue g}"
      | none => "") ++
    (if doc.page.bleed != 0 then s!" bleed {doc.page.bleed.toPtString}" else "") ++
    String.join (doc.page.drawn.toList.map fun r =>
      s!" drawn {r.x.toPtString} {r.y.toPtString} {r.w.toPtString} {r.h.toPtString} {r.color}") ++
    (if doc.page.marks then " marks cut" else "") ++
    (if doc.page.markGap != cutMarkGap
      then s!" mark-gap {doc.page.markGap.toPtString}" else "") ++
    (if doc.page.markThickness != cutMarkThickness
      then s!" mark-thickness {doc.page.markThickness.toPtString}" else "") ++
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
    String.join (doc.fonts.faces.toList.map fun ((slot, weight, italic), f) =>
      let slotName := match slot with | 0 => "body" | 1 => "sans" | _ => "mono"
      let variant := match weight, italic with
        | 400, false => "upright" | 700, false => "bold"
        | 400, true => "italic" | 700, true => "bolditalic"
        | w, i => (Weight.ofCss w).series ++ (if i then ".italic" else "")
      fontLine s!"{slotName}.{variant}" (some f))
  let paletteLines := String.join (doc.palette.entries.toList.map fun (n, c) =>
    let mark := if doc.palette.decorative.contains n then " decorative" else ""
    s!"palette {n} #{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}{mark}\n") ++
    (match doc.palette.coveredFraction with
     | some f => s!"palette covered {f}%\n"
     | none => "")
  let tokenLines := String.join (doc.tokens.entries.toList.map fun (n, g) =>
    s!"token {n} {dumpGlue g}\n") ++
    String.join (doc.captionPos.toList.map fun (scope, p) =>
      let pos := match p with
        | .top => "top"
        | .bottom => "bottom"
        | .auto => "auto"
      s!"caption-position {if scope.isEmpty then "*" else scope} {pos}\n")
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
     | none => "") ++
    (match doc.headline with
     | some hl =>
       "headline\n  title\n" ++ dumpInlines "    " hl.title ++
       (if hl.author.isEmpty then "" else "  author\n" ++ dumpInlines "    " hl.author) ++
       (if hl.institute.isEmpty then "" else
         "  institute\n" ++ dumpInlines "    " hl.institute)
     | none => "") ++
    (match doc.logoLeft with
     | some xs => "logoleft\n" ++ dumpInlines "  " xs
     | none => "") ++
    (match doc.logoRight with
     | some xs => "logoright\n" ++ dumpInlines "  " xs
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
