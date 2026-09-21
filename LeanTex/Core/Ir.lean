import LeanTex.Core.Diag
import LeanTex.Core.Dim
import LeanTex.Core.Image
import LeanTex.Core.Math
import LeanTex.Core.LocaleContract

namespace LeanTex.Core.Ir

open LeanTex.Core LeanTex.Core.Dim

/-- The base font size every relative measure hangs off. It lives in the IR
because both backends read it: layout sets body text at this size, and HTML
derives its content measure from the page's text width in these units. -/
def baseFontSize : Sp := Dim.pt 10

/-- The leading ratio, per-mille: baselines sit at 6⁄5 of the size — the
routine text setting, 10/12 of Bringhurst's "settings such as 9/11, 10/12,
11/13 and 12/15 are routine" (Elements §2.2.1). It lives in the IR because
both backends read it: `leadingFor` applies it to every baseline distance
the PDF sets (the math grid included), and the HTML stylesheet emits it as
the heading line-height. -/
def leadingMilli : Nat := 1200

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
def leadingFor (size : Sp) (factor : Nat := 1000) : Sp :=
  size * (leadingMilli : Int) / 1000 * factor / 1000

/-- The rhythm's working quantum: the half-unit. Bringhurst §2.2.2 permits
half-lines in the measured intervals; every declared default vertical gap
is an integer number of these, which `default_rhythm_multiples` and
`caption_gaps_rhythm` state over the shipped defaults. -/
def rhythmQuantum (size : Sp) (factor : Nat := 1000) : Sp :=
  leadingFor size factor / 2

/-- The default gap between peer paragraphs: one rhythm quantum of the
governing size, half its leading (6pt at the 10pt base, 6.6pt at the
slides 11pt). Derivation-closed in the base size by construction —
`parskip_is_quantum` is `rfl` at every base — which is what makes a
uniform `\page{ fontsize }` scale the whole design (`\linespread` moves
the lines it declares, not the default gaps: the gap quantizes on the
base rhythm). A document declares its own through
`\page{ parskip = ... }`. -/
def parskipDefault (size : Sp) : SymGlue :=
  { width := Dim.Length.ofSp (rhythmQuantum size) }

/-- The rhythm quantum is positive at any body size of at least 1pt: the
one key fact every default-gap theorem consumes, proved once over the
arithmetic (`omega` over bare `Int`, the `slides_lines_survive_bands`
pattern) instead of once per consumer. -/
theorem rhythmQuantum_pos (size : Int) (h : Dim.pt 1 ≤ size) :
    0 < rhythmQuantum size := by
  have hx : (65536 : Int) ≤ size := h
  show 0 < size * 1200 / 1000 * 1000 / 1000 / 2
  omega

/-- The comparison twin: the half-unit is strictly under the full unit, so
`≤` and `<` orderings between quantum multiples both read off this pair. -/
theorem rhythmQuantum_lt_double (size : Int) (h : Dim.pt 1 ≤ size) :
    rhythmQuantum size < 2 * rhythmQuantum size := by
  have hx : (65536 : Int) ≤ size := h
  show size * 1200 / 1000 * 1000 / 1000 / 2
    < 2 * (size * 1200 / 1000 * 1000 / 1000 / 2)
  omega

/-- The default clearance between a cut mark's inward end and the trim
line it stops short of: 0.075 in. The industry guillotine tolerance is
1/32–1/16 in (PrintNinja's pre-press guide and Smartpress's cutting
tolerance both publish the 1/16 in outer bound), so 0.075 in beats a
spec-limit drift with 0.0125 in to spare — the mirror of the 1/8 in safe
zone type keeps inside the trim. `\page{ mark-gap = ... }` overrides. -/
def cutMarkGap : Sp := inch 3 / 40

/-- The default cut-mark thickness: 0.5 bp, a print shop's floor for a
hairline that prints legibly on digital stock and twice the 0.25 bp
offset floor, so the mark survives either process. This engine reads
`bp` as `pt` (`Decl.unitScaleBase`), so the value is 0.5 pt in sp.
`\page{ mark-thickness = ... }` overrides. -/
def cutMarkThickness : Sp := pt 1 / 2

/-- Page geometry, as declared by `\page`. -/
structure PageSpec where
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
  tests/compat-index/lineno.txt carries it too). -/
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
  /-- LaTeX's `\footskip`, as declared: baseline to baseline. Read through
  the same correction as `headsep` — the symmetric reading — so equal
  declared values mean equal visual gaps; a surviving difference is
  N0021. -/
  footskip : Option Sp := none
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
engine's own — beamer spends that band on headline and footline templates
the engine does not render — and, being the engine's own, it is derived,
not chosen: two lines of the slides context's own rhythm (its earlier
spelling, 9 mm, missed that by 0.888 pt — a free scalar for no reason).
The lines-per-slide theorem in Layout is what holds these numbers
together. -/
def slidesStage43 : Sp × Sp := (Dim.mm 128, Dim.mm 96)
def slidesStage169 : Sp × Sp := (Dim.mm 160, Dim.mm 90)

/-- The slides stages, beamer's `aspectratio` table entire (beamer user
guide §8.1, the `aspectratio=` class option; the millimetre pairs are
`beamer.cls`'s own: 1610 → 160×100, 169 → 160×90, 149 → 140×90,
141 → 148.5×105, 54 → 125×100, 32 → 135×90, 43 → 128×96). Each row is
named by its ratio as `\page{ size = ... }` spells it — `√2:1` by beamer's
own digits `141` — and `slidesStageNamed` matches with the colon elided,
so `aspectratio=169` and the native `16:9` select one row. The lines-fit
contract (`Layout.slides_lines_in_band`) quantifies over every row:
adding a stage is entering that contract. -/
def slidesStages : Array (String × Sp × Sp) :=
  #[("4:3", slidesStage43),
    ("16:9", slidesStage169),
    ("16:10", Dim.mm 160, Dim.mm 100),
    ("14:9", Dim.mm 140, Dim.mm 90),
    ("141", Dim.mm100 14850, Dim.mm 105),
    ("5:4", Dim.mm 125, Dim.mm 100),
    ("3:2", Dim.mm 135, Dim.mm 90)]

/-- The stage a ratio name selects, colon elided on both sides: `16:9`,
`169`, and beamer's option digits agree on one row. -/
def slidesStageNamed (name : String) : Option (Sp × Sp) :=
  let strip := fun (s : String) => String.ofList (s.toList.filter (· != ':'))
  (slidesStages.find? fun r => strip r.1 == strip name).map (·.2)

def slidesHMargin : Sp := Dim.mm 10
def slidesFontSize : Sp := Dim.pt 11
def slidesVMargin : Sp := 2 * leadingFor slidesFontSize

/-- The article page's vertical inch, restated as rhythm: the letter-paper
office convention (`PageSpec.vmargin`'s docstring) happens to be exactly
six units of the base context's leading — 72 pt over 12 pt — so the
default page's vertical frame is on the grid it did not know it was on.
Held here so neither side drifts: an edit to the base leading or the
margin that breaks the coincidence must say which convention it is
keeping. -/
theorem vmargin_on_rhythm :
    ({} : PageSpec).vmargin = 6 * leadingFor baseFontSize := by decide

/-- The card class's legibility floor: an angular x-height of 0.2° at the
40 cm hand-held distance is 1.4 mm, the bound of the fluent-reading range
in Legge & Bigelow 2011. The class implies `text.xheight >=` this;
`card_floor_within_scale` ties it to the size scale. -/
def cardXHeightFloor : Sp := Dim.mm100 140
/-- The poster class's body size: beamerposter's scale-1 normalsize,
24.88 pt — the size10.clo ladder magnified for its A0 calibration
(beamerposter.sty v1.13, the fontscale table's base row). `scale=` and
the named sizes multiply it through `\page{ fontsize }`. -/
def posterFontSize : Sp := Dim.pt 2488 / 100

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
def posterXHeightFloor : Sp := Dim.mm100 350

/-- An sRGB colour — and, when the document declared it in CMYK, the
declared components ride along so the PDF can honour the declared model.
`r g b` are always populated: they are the one screen-facing reading
(HTML, contrast judgement, dimming), computed for a CMYK declaration by
`ofCmyk`'s stated conversion. -/
structure Color where
  r : UInt8
  g : UInt8
  b : UInt8
  /-- Declared-model components in thousandths (0–1000 each) when the
  colour was declared in CMYK; `none` for a colour declared in RGB. The
  PDF backend emits these as `DeviceCMYK` verbatim (`cmyk_components_kept`)
  — converting a print colour to RGB would silently change what a press
  prints. -/
  cmyk : Option (Nat × Nat × Nat × Nat) := none
  deriving Repr, BEq, Inhabited

def Color.black : Color := { r := 0, g := 0, b := 0 }

/-- One byte as two hex digits; `upper` picks the alphabet's case. The dump
printers and diagnostics quote colours uppercase; CSS serializes lowercase
(`HtmlDoc.cssColor`). One printer for every reader, so a byte cannot render
two ways. -/
def Color.hexByte (v : UInt8) (upper : Bool := true) : String :=
  let d := (if upper then "0123456789ABCDEF" else "0123456789abcdef").toList
  String.ofList [d.getD (v.toNat / 16) '0', d.getD (v.toNat % 16) '0']

/-- The sRGB preview of a CMYK declaration, for the screen-facing readers
only (HTML output, contrast checks): CSS Color 4's `device-cmyk` naive
conversion, `red = 1 − min(1, cyan·(1−black) + black)` and its siblings —
explicitly an un-colour-managed approximation, not a lossless mapping;
the CSS spec itself calls naive conversion "a poor substitute" for a
colour profile. The declared components stay in `cmyk`; only they reach
the PDF. -/
def Color.ofCmyk (c m y k : Nat) : Color :=
  let ch (v : Nat) : UInt8 :=
    UInt8.ofNat (255 * (1000 - min 1000 (v * (1000 - min 1000 k) / 1000 + k)) / 1000)
  { r := ch c, g := ch m, b := ch y, cmyk := some (c, m, y, k) }

/-- Thousandths as a PDF decimal: 830 ↦ "0.83". -/
def Color.pdfMilli (v : Nat) : String :=
  let v := min v 1000
  if v == 0 then "0" else if v == 1000 then "1"
  else
    let frac := toString v
    let frac := ("".pushn '0' (3 - frac.length)) ++ frac
    "0." ++ (frac.dropEndWhile (· == '0')).toString

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

/-- The fill-colour operation for this colour: a CMYK declaration paints in
`DeviceCMYK` with its own components (`k` sets fill colour in DeviceCMYK,
ISO 32000-2 §8.6.8, Table 73; DeviceCMYK is §8.6.4.4), an RGB one in
`DeviceRGB` (`rg`). One emission site per backend, so the declared model
cannot be quietly re-interpreted anywhere else. -/
def Color.pdfFill (c : Color) : String :=
  match c.cmyk with
  | some (cy, m, y, k) =>
    s!"{pdfMilli cy} {pdfMilli m} {pdfMilli y} {pdfMilli k} k"
  | none => s!"{c.pdfComponents} rg"

/-- The stroke-colour twin of `pdfFill`: the same declared components
through the stroking operators (`K`/`RG`, ISO 32000-2 §8.6.8, Table 74). -/
def Color.pdfStroke (c : Color) : String :=
  match c.cmyk with
  | some (cy, m, y, k) =>
    s!"{pdfMilli cy} {pdfMilli m} {pdfMilli y} {pdfMilli k} K"
  | none => s!"{c.pdfComponents} RG"

/-- A colour declared in a model round-trips to that model in a backend
that supports it: the components the document declared are the components
the PDF paints with, exactly — never an RGB re-interpretation. -/
theorem Color.cmyk_components_kept (c m y k : Nat) :
    (Color.ofCmyk c m y k).cmyk = some (c, m, y, k) ∧
    (Color.ofCmyk c m y k).pdfFill
      = s!"{pdfMilli c} {pdfMilli m} {pdfMilli y} {pdfMilli k} k" := by
  exact ⟨rfl, rfl⟩

/-- The colour printer's marks paint in. ISO 32000-2 §8.6.6.4 names the
special colorant `All` — "useful for purposes such as painting
registration targets", ink on every separation — and DeviceCMYK 1,1,1,1
is its device spelling when the document declares print colours: the
marks then render on all four plates, as ISO 12647-conforming proofs
expect of registration marks. A document that declares no CMYK colour
has no separations to register, so its honest mark colour is plain
black. -/
def Color.registration (printModel : Bool) : Color :=
  if printModel then Color.ofCmyk 1000 1000 1000 1000 else Color.black

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

/-- The two halves of keyed last-wins, over the one keyed store both
`Tokens.declare` and `Palette.declare` are built on: the declared value is
the one read back, and a redeclaration collapses — declaring a key twice is
declaring the later value once. Public: `Theme`'s install fold runs the
same store step, so its lemmas consume these rather than re-proving them. -/
theorem declare_find_eq {α : Type} (xs : Array (String × α)) (k : String) (v : α) :
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
theorem declare_keeps {α : Type} (xs : Array (String × α)) (k k' : String) (v : α)
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
theorem Tokens.declare_last_wins (t : Tokens) (k : String) (g : SymGlue) :
    (t.declare k g).find? k = some g := by
  unfold declare find?
  rw [declare_find_eq]
  rfl

/-- Keyed last-wins, write side (T2): redeclaring a key overwrites — the
earlier value leaves no residue, so same-key order is the only order two
`\tokens` blocks carry. -/
theorem Tokens.declare_overwrite (t : Tokens) (k : String) (g g' : SymGlue) :
    (t.declare k g).declare k g' = t.declare k g' := by
  unfold declare
  rw [declare_collapse]

/-- An override changes exactly what it names (T2's locality half, the
`Tokens` twin of `Palette.declare_keeps_others`): every other token
resolves as it did before. -/
theorem Tokens.declare_keeps_others (t : Tokens) (k k' : String) (g : SymGlue)
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
-- is part of the rule, never left to the author. Em/ex-relative, resolved
-- at the table's own size like every token; each is overridable through
-- `\tokens{ <latex name> = ... }` under its LaTeX name.

/-- `\toprule`/`\bottomrule` weight: booktabs `\heavyrulewidth` (.08em). -/
def heavyRuleWidth : Dim.Length := { em := 80 }
/-- `\midrule` weight: booktabs `\lightrulewidth` (.05em). -/
def lightRuleWidth : Dim.Length := { em := 50 }
/-- `\cmidrule` weight: booktabs `\cmidrulewidth` (.03em). -/
def cmidRuleWidth : Dim.Length := { em := 30 }
/-- Space under a rule, above the content it heads: booktabs
`\belowrulesep` (.65ex). -/
def belowRuleSep : Dim.Length := { ex := 650 }
/-- Space over a rule, under the content above it: booktabs `\aboverulesep`
(.4ex). -/
def aboveRuleSep : Dim.Length := { ex := 400 }
/-- Space over a `\toprule`: zero — "which seems sensible for a rule
designed to go at the top" (booktabs.dtx); the float's own caption gap
owns that space here. -/
def aboveTopSep : Dim.Length := {}
/-- Space under a `\bottomrule`: zero, as booktabs' `\belowbottomsep`. -/
def belowBottomSep : Dim.Length := {}
/-- Default end-trim of a trimmed `\cmidrule`: booktabs `\cmidrulekern`
(.5em). -/
def cmidRuleKern : Dim.Length := { em := 500 }
/-- `\addlinespace` default: booktabs `\defaultaddspace` (.5em). -/
def defaultAddSpace : Dim.Length := { em := 500 }
/-- Half the gap between two table columns: LaTeX's `\tabcolsep` — "the
columns in a tabular environment are separated by 2\tabcolsep", 6pt
(classes.dtx §Array and tabular). An `@{}` in the column spec deletes the
outer pad, as in LaTeX. -/
def tabColSep : Dim.Length := { sp := Dim.pt 6 }
/-- Two stacked full rules separate by LaTeX's `\doublerulesep`, 2pt
(classes.dtx §Array and tabular) — drawn, but warned: "never use double
rules" (booktabs.dtx §The layout of formal tables). -/
def doubleRuleSep : Dim.Length := { sp := Dim.pt 2 }

/-- The three rule weights are a hierarchy, not three loose numbers: "the
top and bottom rules are heavier than the middle rule, which is in turn
heavier than the subrule" (booktabs.dtx §Introduction, of its own first
example). A weight edit that flattens the hierarchy fails the build. -/
theorem rule_weights_ordered :
    0 < cmidRuleWidth.em ∧ cmidRuleWidth.em < lightRuleWidth.em ∧
    lightRuleWidth.em < heavyRuleWidth.em := by decide

/-- A rule clears more below than above: booktabs' `\belowrulesep` (.65ex)
against `\aboverulesep` (.4ex) — a rule binds to the content it closes and
clears the content it heads, which is exactly the "space above and below
rules" the package exists to add. -/
theorem rule_seps_ordered : 0 < aboveRuleSep.ex ∧ aboveRuleSep.ex < belowRuleSep.ex := by
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
def captionSepDefault (size : Sp) : SymGlue :=
  { width := { sp := rhythmQuantum size } }
/-- Gap between a float and the text around it: one full rhythm unit of
the governing size. Overridable as `\tokens{ floatsep = ... }`. -/
def floatSepDefault (size : Sp) : SymGlue :=
  { width := { sp := 2 * rhythmQuantum size } }

/-- Gap between the last body line and the footnote region: `\skip\footins`
(classes.dtx, the 10pt option: 9pt plus 4pt minus 2pt), quantized to the
rhythm — two quanta, one full leading. The quantized value lies inside the
source glue's own range (7..13pt at the 10pt base, `footins_within_glue`),
so it is a length LaTeX's own glue could set. Overridable as
`\tokens{ footins = ... }`. -/
def footinsDefault (size : Sp) : SymGlue :=
  { width := { sp := 2 * rhythmQuantum size } }

/-- The quantized `\skip\footins` is on the rhythm and inside the source
glue's own rubber range at the base it was sourced at: 9−2 ≤ 12 ≤ 9+4 pt.
An edit that moves the default off the grid or outside what the LaTeX glue
could legally set fails the build here. -/
theorem footins_within_glue :
    (footinsDefault baseFontSize).width.sp = 2 * rhythmQuantum baseFontSize ∧
    Dim.pt 7 ≤ (footinsDefault baseFontSize).width.sp ∧
    (footinsDefault baseFontSize).width.sp ≤ Dim.pt 13 := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- The heading's default spaces, their own tokens rather than the
parskip's doubles: article.cls pairs a zero `\parskip` with 3.5ex above /
2.3ex below a `\section` (classes.dtx `\@startsection`), so a class that
zeroes the peer gap must not silently zero the heading's. The
rhythm-aligned stand-ins are one full unit above and the half-unit below
(the heading and peer rows of `rhythmGapQuanta`), the same ordering. A
document with a larger declared parskip keeps the walk's 2-quanta growth
(the walk takes the larger); a declared `\style{section}{ before/after }`
overrides entirely. -/
def headingBeforeDefault (size : Sp) : SymGlue :=
  { width := { sp := 2 * rhythmQuantum size } }
/-- The heading's default space below: the half-unit. See
`headingBeforeDefault`. -/
def headingAfterDefault (size : Sp) : SymGlue :=
  { width := { sp := rhythmQuantum size } }

/-- A heading binds to the text it introduces: its default space above is
at least its space below (Hochuli, Detail in Typography, on section
openings: more space above the heading than below it; article.cls's
3.5ex/2.3ex is the same ordering at 1.52), both on the rhythm, and neither
zero. That the space above is exactly twice the quantum is
`rhythm_table_exact`'s heading row, stated once there. W0202 is the
declared-values half of the same rule; this is the defaults' half, and an
edit that inverts them fails the build here. -/
theorem heading_space_above_ge_below (size : Int) (h : Dim.pt 1 ≤ size) :
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
theorem default_rhythm_multiples (size : Int) (h : Dim.pt 1 ≤ size) :
    (parskipDefault size).width.sp = rhythmQuantum size ∧
    0 < (parskipDefault size).width.sp :=
  ⟨rfl, rhythmQuantum_pos size h⟩

/-- The anchor, `rfl` by derivation at every base: the peer gap IS the
rhythm quantum, because it is defined as it — no absolute constant
survives in the default, which is the soundness of mapping a poster's
`scale=` onto `\page{ fontsize }`. -/
theorem parskip_is_quantum (size : Sp) :
    (parskipDefault size).width.sp = rhythmQuantum size := rfl

/-- At the shipped article base the leading is even, so the half-unit
halves it exactly. The slides 11pt leading is odd in sp (865075), so its
quantum rounds down half an sp — invisible ink, stated rather than
implied; the exactness is per-base, the derivation universal
(`parskip_is_quantum`). -/
theorem parskip_halves_leading_at_bases :
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
theorem caption_gaps_rhythm (size : Int) (h : Dim.pt 1 ≤ size) :
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
def titleAuthorStrut : SymGlue := { width := { em := 2 * leadingMilli } }

/-- The gap after the whole title block, before the abstract or the text:
two rhythm units, shrinkable by the half-unit — a little rubber, as the
lineage's `\vskip 0.3in \@minus 0.1in` has. The venue's 21.7pt (shrunk
floor 14.5pt) becomes the engine's 24pt (floor 18pt) at the 10pt body:
the grid lands 2.3pt over what the venue eyeballed. -/
def titleBlockAfter : SymGlue :=
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
def titleBarGap : SymGlue := { width := { em := 3 * leadingMilli / 2 } }

/-- The skip outside a title bar — above the top one, below the bottom
one: one rhythm quantum. -/
def titleBarSkip : SymGlue := { width := { em := leadingMilli / 2 } }

/-- The author block joins the rhythm (`default_rhythm_multiples`' family):
the strut and the post-block gap are half-unit multiples of the body
leading — four quanta each, the gap's shrink one — so the title block
stays the engine's typography while the venue chooses only that the
furniture exists (and the author's weight). Per-base `decide`, and it must
stay so: em-resolution floors, so this equality is false at general sizes
(65538 sp is a counterexample; `titleAuthorStrut`'s caveat). -/
theorem title_author_rhythm :
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
theorem title_bar_rhythm :
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
is declared once; each backend realizes it in its own context's unit. -/
def rhythmGapQuanta : List (String × Nat) :=
  [("peer", 1), ("heading", 2), ("caption", 1), ("float", 2)]

/-- The table and the tokens agree: each declared default gap is its row's
multiple of the quantum, and the heading row is twice the peer row — the
walk's `parskip.add parskip` spelled as a multiple. An edit that moves a
token off its declared multiple, or drops a row a backend reads, fails the
build here. -/
theorem rhythm_table_exact (size : Sp) :
    ((rhythmGapQuanta.lookup "peer").getD 0 : Int) * rhythmQuantum size
      = (parskipDefault size).width.sp ∧
    ((rhythmGapQuanta.lookup "caption").getD 0 : Int) * rhythmQuantum size
      = (captionSepDefault size).width.sp ∧
    ((rhythmGapQuanta.lookup "float").getD 0 : Int) * rhythmQuantum size
      = (floatSepDefault size).width.sp ∧
    ((rhythmGapQuanta.lookup "heading").getD 0 : Int) * rhythmQuantum size
      = (headingBeforeDefault size).width.sp ∧
    (rhythmGapQuanta.lookup "heading").getD 0
      = 2 * (rhythmGapQuanta.lookup "peer").getD 0 := by
  refine ⟨?_, ?_, ?_, ?_, by decide⟩ <;>
    simp [rhythmGapQuanta, parskipDefault, captionSepDefault, floatSepDefault,
      headingBeforeDefault, Dim.Length.ofSp, List.lookup]

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
    decorative := if decorative then
        if p.decorative.contains key then p.decorative
        else p.decorative.push key
      else p.decorative.filter (· != key) }

/-- Keyed last-wins for colours (T2), the same statement `\tokens` carries:
the declared colour is the one resolved. -/
theorem Palette.declare_last_wins (p : Palette) (k : String) (c : Color) :
    (p.declare k c).find? k = some c := by
  unfold declare find?
  rw [declare_find_eq]
  rfl

/-- Redeclaring a colour overwrites without residue (T2) — the door theme
bundles and documents share, so "override the theme's entry" is exact, not
approximate. -/
theorem Palette.declare_overwrite (p : Palette) (k : String) (c c' : Color) :
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
theorem Palette.declare_keeps_others (p : Palette) (k k' : String) (c : Color) (d : Bool)
    (h : k' ≠ k) : (p.declare k c d).find? k' = p.find? k' := by
  unfold declare find?
  rw [declare_keeps _ _ _ _ h]

/-- A colour override never touches the covered fraction. -/
theorem Palette.declare_keeps_covered (p : Palette) (k : String) (c : Color) (d : Bool) :
    (p.declare k c d).coveredFraction = p.coveredFraction := rfl

/-- The decorative exemption rides with the declaration: a plain
redeclaration removes its key from the exempt set, so re-declaring a
colour without the opt-out restores the contrast check. The exemption is
WCAG 2.2 SC 1.4.3's decoration exemption, and it excuses the declared
value — a property of one declaration, never of the key forever: before
this statement a stale exemption outlived the value it excused, and a
redeclared colour shipped illegible in silence. -/
theorem declare_decorative_rides (p : Palette) (k : String) (c : Color) :
    (p.declare k c false).decorative.contains k = false := by
  simp [Palette.declare]

/-- The other direction: declaring decorative exempts the key. -/
theorem declare_decorative_names (p : Palette) (k : String) (c : Color) :
    (p.declare k c true).decorative.contains k = true := by
  simp only [Palette.declare, ite_true]
  by_cases h : k ∈ p.decorative <;> simp [h]

def Color.white : Color := { r := 255, g := 255, b := 255 }

/-- One step of xcolor's `!` mix: `pct`% of `a` over the rest of `b`,
per sRGB channel, rounded. -/
def Color.mix (a : Color) (pct : Nat) (b : Color) : Color :=
  let ch (x y : UInt8) : UInt8 :=
    UInt8.ofNat ((x.toNat * pct + y.toNat * (100 - pct) + 50) / 100)
  { r := ch a.r b.r, g := ch a.g b.g, b := ch a.b b.b }

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
def xcolorBase (s : String) : Option Color :=
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
def Palette.resolve (p : Palette) (expr : String) : Option Color :=
  let atom (s : String) : Option Color :=
    (p.find? s).orElse fun _ => xcolorBase s
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
  match bangParts [] expr.toList with
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
def FontSpec.declareFace (s : FontSpec) (variant : Nat × Nat × Bool)
    (face : String) : FontSpec :=
  { s with faces := (s.faces.filter (·.1 != variant)).push (variant, face) }

/-- The face the document declared for one slot variant, if any. -/
def FontSpec.faceFor (s : FontSpec) (slot weight : Nat) (italic : Bool) : Option String :=
  (s.faces.find? (·.1 == (slot, weight, italic))).map (·.2)

/-- The last-declared face is the one resolved (the fontspec rule above,
mirroring `declare_overwrite` for tokens): redeclaring a variant is an
override, never a silently first-wins accident. -/
theorem FontSpec.faceFor_last_declared (s : FontSpec) (v : Nat × Nat × Bool)
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
def OutputSpec.addFormat (o : OutputSpec) (f : String) : OutputSpec :=
  { o with formats := if o.formats.contains f then o.formats else o.formats.push f }

/-- A format list never grows a duplicate (T4): `formats = pdf, pdf` and a
second `\output` block naming `pdf` again are one entry — the list-append
half of the surface stays a set. -/
theorem OutputSpec.addFormat_nodup (o : OutputSpec) (f : String)
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
  /-- The document's main language, a BCP 47 tag: babel's package options
  declare it (last option = main, babel's rule), `\pdfmeta{ language = .. }`
  spells it natively. Both artifacts declare it — `<html lang>` and the
  PDF catalog `/Lang` — and every language-reading site (captions,
  hyphenation patterns, quotes) resolves through it. -/
  language : Option String := none
  deriving Repr, BEq, Inhabited

/-- The document's resolved main locale: the declared language when a
record ships for it, English otherwise (the site that declared the tag
named the miss, W0368). One resolving site, read by both backends. -/
def Meta.locale (m : Meta) : Locale :=
  (m.language.bind Locale.forTag).getD Locale.en

/-- The OpenType features both backends apply, one record: the PDF path
applies them to the glyphs it sets, the HTML path requests them of the
browser (`font-kerning`), so the artifacts cannot disagree —
`features_agree` holds by construction, the two emissions being two
projections of one value. `kern` defaults on, HarfBuzz's own default
set; a `\tokens` knob arrives with the features it gates, and until
then the record is the engine's one constant. -/
structure Features where
  kern : Bool := true
  deriving Repr, BEq, Inhabited

/-- The features in force: the one resolving site. -/
def features : Features := {}

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
  /-- The document conforms to the engine's judged WCAG 2.2 AA rows: no
  accessibility fact the judges name (a failing contrast pair, an image
  with no text alternative, a broken heading outline) and a declared
  language. Facts the engine cannot judge (a PDF's tagged reading order,
  browser rendering) are outside the assertion and stay named in PLAN,
  never implied passes. -/
  | accessibilityAA
  deriving Repr, BEq, Inhabited

def AssertKind.source : AssertKind → String
  | .pages op n => s!"pages {op.label} {n}"
  | .fontsAllEmbedded => "fonts.all_embedded"
  | .textInArea => "text.in_area"
  | .minXHeight m => s!"text.xheight >= {m.toPtString}pt"
  | .accessibilityAA => "accessibility = AA"

structure Assertion where
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
inductive Weight where
  | ul | el | l | sl | m | sb | b | eb | ub
  deriving Repr, BEq, DecidableEq

instance : Inhabited Weight := ⟨.m⟩

/-- The CSS/OpenType numeric value of each series (CSS Fonts 4 §2.2 /
OpenType OS/2 `usWeightClass`, the same registry: 100 Thin, 200
Extra-light, 300 Light, 400 Normal, 600 Semi-bold, 700 Bold, 800
Extra-bold, 900 Black). `m` is NFSS's *default* series — the regular
weight, 400, not the registry's 500 "Medium" — and `sl` (semi-light) has
no slot in the nine-step table; 350 is DirectWrite's `SemI_LIGHT`, the
one registry that names it. No single authority numbers all nine, so
those two placements are this table's decision; the round-trip theorem
below is what makes the assignment a bijection onto its image. -/
def Weight.css : Weight → Nat
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
def Weight.all : List Weight := [.ul, .el, .l, .sl, .m, .sb, .b, .eb, .ub]

/-- The series nearest a numeric weight (a face's `usWeightClass`), ties
to the lighter: the inverse direction of the bijection, total over every
input. -/
def Weight.ofCss (n : Nat) : Weight :=
  (Weight.all.foldl (init := Weight.ul) fun best w =>
    let d := fun v : Weight => max v.css n - min v.css n
    if d w < d best then w else best)

/-- The NFSS spelling of each series, `\fontseries`'s vocabulary. -/
def Weight.series : Weight → String
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
def seriesWidthCodes : List String :=
  ["uc", "ec", "sc", "c", "sx", "ex", "ux", "x"]

/-- Parse an NFSS series value into its weight and width halves
(fntguide §2.2: a series combines a weight code and a width code, each
dropped when medium — `bx` is bold extended, `c` is medium condensed,
`m` is both). Longest weight code first, so `sb` is semi-bold, never
`s`+garbage. `none` when the string is no series value at all. -/
def Weight.parseSeries (s : String) : Option (Weight × String) :=
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
def Weight.isBold (w : Weight) : Bool := 700 ≤ w.css

/-- The two directions of the series↔number map compose to the identity:
each series is the nearest series to its own number, which is what makes
`css` a bijection onto its image and `ofCss` its inverse there. The parse
half — `parseSeries w.series = some (w, "")` — is String-typed, which the
kernel cannot reduce, so it is pinned by an executable check in
Tests/FontMath rather than stated here. -/
theorem Weight.ofCss_css_id : ∀ w : Weight, ofCss w.css = w := by
  intro w; cases w <;> rfl

inductive Style where
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
def sizeScale : List (String × Nat) :=
  [("tiny", 500), ("scriptsize", 700), ("footnotesize", 800), ("small", 900),
   ("normalsize", 1000), ("large", 1200), ("Large", 1440), ("LARGE", 1728),
   ("huge", 2074), ("Huge", 2488)]

/-- A named step of the scale applied to a base size — the one resolving
site for `base * step / 1000`, so the backends and the layout cannot
drift on what a named size means. A name off the scale is the base
itself: the identity factor, `normalsize`'s. -/
def scaleStep (base : Sp) (name : String) : Sp :=
  base * ((sizeScale.lookup name).getD 1000) / 1000

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

/-- The poster's mirror of `card_floor_within_scale`: at the same
half-nominal fallback ratio, every scale step from `footnotesize` up on
beamerposter's scale-1 body (`posterFontSize`) clears the 1 m fluent-
reading floor — the class never states an assertion the calibration it is
derived from violates, and what fails (`scriptsize`, `tiny`, or a body
pasted in unscaled from an article) is what the assertion exists to catch. -/
theorem poster_floor_within_scale :
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
def stepsOrdered (scale : List (String × Nat)) : Bool :=
  ((scale.map (·.2)).zip (scale.map (·.2)).tail).all fun p => p.1 ≤ p.2

theorem sizeScale_stepsOrdered : stepsOrdered sizeScale = true := by decide

/-- Replace one named step of a ladder — the door a venue's refused
`\@setfontsize` size commands are read through, per-mille of the body.
`none` when the name is off the ladder or the replaced ladder would no
longer be ordered: LaTeX's own scale is ordered by design (size10.clo's
values), and the engine's size comparisons assume it, so a venue step
that breaks the order keeps the built-in instead, named. -/
def setStep (scale : List (String × Nat)) (name : String) (f : Nat) :
    Option (List (String × Nat)) :=
  if (scale.lookup name).isNone then none
  else
    let s' := scale.map fun p => if p.1 == name then (p.1, f) else p
    if stepsOrdered s' then some s' else none

/-- Every ladder `setStep` accepts is ordered in the named order: the
read-out cannot admit a venue that sets `\small` larger than
`\normalsize` — that step keeps the built-in (W0361 names it). -/
theorem size_ladder_monotone (scale : List (String × Nat)) (name : String)
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
def setStepsAll (scale : List (String × Nat)) (steps : List (String × Nat)) :
    Option (List (String × Nat)) :=
  let s' := scale.map fun q => match steps.lookup q.1 with
    | some f => (q.1, f)
    | none => q
  if stepsOrdered s' then some s' else none

/-- The batch door's half of `size_ladder_monotone`: a venue ladder
accepted whole is ordered whole. -/
theorem size_ladder_monotone_all (scale steps : List (String × Nat))
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
def PageSpec.scale (p : PageSpec) : List (String × Nat) :=
  p.sizes.getD sizeScale

/-- `scaleStep` over a document's ladder: the same integer arithmetic, the
scale a parameter. A name off the ladder is the base itself. -/
def scaleStepIn (scale : List (String × Nat)) (base : Sp) (name : String) : Sp :=
  base * ((scale.lookup name).getD 1000) / 1000

theorem scaleStepIn_default (base : Sp) (name : String) :
    scaleStepIn sizeScale base name = scaleStep base name := rfl

def Style.label : Style → String
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
  | .lang tag => s!"lang:{tag}"


/-- What a resolved cross-reference renders (`refText`): LaTeX's bare
number (`\ref`) and parenthesised equation number (`\eqref`), and
cleveref's forms (cleveref manual v0.21.4 §2) — the kind's locale name
before the number (`\cref`/`\Cref` — `cap` picks the capitalised name,
which English also unabbreviates), the first key of a `\crefrange` pair
(plural name, number, the range conjunction), the label format alone
(`\labelcref`, also the range pair's second key), and the name alone
(`\namecref`/`\nameCref`). -/
inductive RefForm where
  | plain
  | paren
  | cref (cap : Bool)
  | crefRange (cap : Bool)
  | labelOnly
  | name (cap : Bool)
  deriving Repr, BEq

/-- The weight a style selects, when it touches the axis: the one map
`.bold`, `.medium`, `.series`, and `.normal`'s reset project through.
Layout's `applyStyle` follows it exactly (`weight_agree` in Layout.lean),
and the HTML emission reads the same `w` its `.series` arm carries — so
the face a run selects is one function of the style in both backends. -/
def Style.weight? : Style → Option Weight
  | .bold => some .b
  | .medium => some .m
  | .series w => some w
  | .normal => some .m
  | _ => none

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
  /-- A strut, LaTeX's `\rule{\z@}{h}`: a zero-width prop that makes its
  line's box at least `h` tall above the baseline. It ships no ink and no
  text — layout raises the line, the other backends keep an empty carrier —
  so it owes no census fact. The author line of a styled title block
  carries one (`ElementStyle.authorStrut`). -/
  | strut (height : SymGlue)
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
  /-- A citation (`\cite`, natbib's `\citep`/`\citet`): the keys of one
  citation group, as written. Elaboration emits it unresolved — the `.bib`
  file is the driver's effect — and resolution (`Bib.apply`) *replaces* the
  node with the bibliography style's own inlines: marks linked to their
  entries, brackets or parentheses per the style, so no backend ever reads
  a citation form. A node a backend still sees is one no bibliography
  resolved; it renders `citeMark` per key, LaTeX's own spelling for an
  undefined citation, and W0351 or the missing-file diagnostic has already
  said why. `textual` marks `\citet`'s in-sentence form. -/
  | cite (textual : Bool) (keys : Array String)
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

/-- The anchor a reference-list entry carries in HTML and its citations
link to (`#` prefixed): one naming site, read by the resolver's link
construction and the backend's id emission, so the two cannot drift. -/
def bibAnchor (key : String) : String := "ref-" ++ key

/-- What an unresolved citation shows for each key: LaTeX's rendering for
an undefined citation. The one definition site backends and census read. -/
def citeMark : String := "?"

/-- The text an unresolved citation is worth: one mark per key, comma
separated — `\cite{a,b}` with no bibliography shows `?, ?`, one visible
gap per promised entry. -/
def citeMarks (keys : Array String) : String :=
  String.intercalate ", " (keys.toList.map fun _ => citeMark)

/-- How far a footnote mark's baseline stands above its line's, per mille
of the surrounding size, the mark itself set at the `scriptsize` step of
`sizeScale`. The authority this constant stands in for is the face's own
OS/2 `ySuperscriptYOffset` (OpenType spec, OS/2 table): `Font` does not
parse it yet — it reads sCapHeight and sxHeight only — so one named value,
a third of an em, holds the raise until it does (PLAN § Owed obligations
records the parse). -/
def markRaise : Nat := 333

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

/-- The shares of a page's leftover vertical space above and below its
content, per declared alignment: the ratio form of beamer's `\vfil`-glue
model — top-flush 0:1 (all leftover below), centring 1:1 (beamer user
guide §8.1: `c` is the default), bottom-flush 1:0, and the title page's
golden 2618:1000 (beamerinnerthememoloch.dtx, the "golden ratio spacing"
of its `title page` template). The one table both artifacts must honour:
`Layout.VDist.of` projects it onto the PDF page, `HtmlDoc.vdistShares`
onto the deck's flex spacers, and `vdist_shares_agree` in Tests states
the agreement. -/
def VAlign.shares : VAlign → Nat × Nat
  | .top => (0, 1)
  | .center => (1, 1)
  | .bottom => (1, 0)
  | .golden => (2618, 1000)

namespace Pic

/-- The two line widths the subset strokes: pgf manual §15.3.1 — `thin`,
0.4 pt, is every path's default, `thick` is 0.8 pt. Widths are graphic
state, not geometry: `scale=` never touches them, as in pgf. -/
def thinWidth : Sp := Dim.pt 2 / 5
def thickWidth : Sp := Dim.pt 4 / 5

/-- A dash pattern by name; the backends emit the sourced rhythms — pgf
manual §15.3.2: `dashed` is on 3 pt off 3 pt, `dotted` on the line width
off 1 pt (the `densely dotted` rhythm; the subset keeps one dotted form). -/
inductive Dash where
  | solid
  | dashed
  | dotted
  deriving Repr, BEq, Inhabited

/-- How a border or an edge strokes: colour, width, dash. -/
structure Stroke where
  color : Color := Color.black
  width : Sp := thinWidth
  dash : Dash := .solid
  deriving Repr, BEq, Inhabited

/-- One segment of a stroked edge, endpoints spelled explicitly (no
current-point state): a straight line, or a cubic Bézier with its two
control points. -/
inductive PathSeg where
  | line (x1 y1 x2 y2 : Sp)
  | cubic (x1 y1 c1x c1y c2x c2y x2 y2 : Sp)
  deriving Repr, BEq, Inhabited

/-- The declared box of a segment. A cubic lies in the convex hull of its
four control points (de Casteljau), so the join of their boxes bounds
the drawn curve. -/
def PathSeg.box : PathSeg → (Sp × Sp) × (Sp × Sp)
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
structure Tip where
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
inductive LabelAlign where
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
def paintDump (st : Option Stroke) (fl : Option Color) : String :=
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
inductive Shape where
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
def Shape.recolor (f : Color → Color) : Shape → Shape
  | .rect x y w h c => .rect x y w h (f c)
  | .label x y t c sc al => .label x y t (f c) sc al
  | .circle x y r st fl =>
    .circle x y r (st.map fun s => { s with color := f s.color }) (fl.map f)
  | .frame x y w h st fl =>
    .frame x y w h (st.map fun s => { s with color := f s.color }) (fl.map f)
  | .edge segs st tip => .edge segs { st with color := f st.color } tip

/-- A box in picture coordinates: min corner, then max corner. -/
abbrev Box := (Sp × Sp) × (Sp × Sp)

/-- The join of two boxes: the smallest box holding both. -/
def Box.join (a b : Box) : Box :=
  ((min a.1.1 b.1.1, min a.1.2 b.1.2), (max a.2.1 b.2.1, max a.2.2 b.2.2))

/-- The declared box of a shape, corners sorted. A label's box is its
anchor point — its text extent is a font question layout answers — so a
picture's box bounds every fill entirely and every label at its anchor
(`box_in_bbox`); the ink of a label can stand a little proud of it. -/
def Shape.box : Shape → Box
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

structure Picture where
  shapes : Array Shape := #[]
  deriving Repr, BEq, Inhabited

def Picture.recolor (p : Picture) (f : Color → Color) : Picture :=
  { shapes := p.shapes.map (·.recolor f) }

/-- The inline content each label sets, for the font-scalar walk: every
glyph — text or math — a picture can ask a face for is here. -/
def Picture.labelContents (p : Picture) : Array (Array Inline) :=
  p.shapes.filterMap fun s => match s with
    | .label _ _ content _ _ _ => some content
    | .rect _ _ _ _ _ => none
    | .circle _ _ _ _ _ => none
    | .frame _ _ _ _ _ _ => none
    | .edge _ _ _ => none

/-- `a` is inside `b`, componentwise. -/
def Box.le (a b : Box) : Prop :=
  b.1.1 ≤ a.1.1 ∧ b.1.2 ≤ a.1.2 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2

-- The Box and Place proofs state their arithmetic over bare `Int` binders
-- because `omega` does not see through the `Sp` abbreviation (the same
-- workaround `furnitureBand`'s proof records in Layout).

theorem Box.le_refl (a : Box) : Box.le a a := by
  have h : ∀ x : Int, x ≤ x := fun _ => Int.le_refl _
  exact ⟨h _, h _, h _, h _⟩

theorem Box.le_join_left (a b : Box) : Box.le a (Box.join a b) := by
  have hmin : ∀ x y : Int, min x y ≤ x := by intro x y; omega
  have hmax : ∀ x y : Int, x ≤ max x y := by intro x y; omega
  exact ⟨hmin _ _, hmin _ _, hmax _ _, hmax _ _⟩

theorem Box.le_join_right (a b : Box) : Box.le b (Box.join a b) := by
  have hmin : ∀ x y : Int, min x y ≤ y := by intro x y; omega
  have hmax : ∀ x y : Int, y ≤ max x y := by intro x y; omega
  exact ⟨hmin _ _, hmin _ _, hmax _ _, hmax _ _⟩

theorem Box.le_trans {a b c : Box} (h1 : Box.le a b) (h2 : Box.le b c) : Box.le a c := by
  have h : ∀ x y z : Int, x ≤ y → y ≤ z → x ≤ z := fun _ _ _ => Int.le_trans
  exact ⟨h _ _ _ h2.1 h1.1, h _ _ _ h2.2.1 h1.2.1,
         h _ _ _ h1.2.2.1 h2.2.2.1, h _ _ _ h1.2.2.2 h2.2.2.2⟩

/-- The bounding-box fold, `List` companion first as every walk here. -/
def bboxList (acc : Box) : List Shape → Box
  | [] => acc
  | s :: rest => bboxList (Box.join acc s.box) rest

/-- The picture's bounding box: the join of its shapes' boxes. An empty
picture is the empty box at the origin. -/
def Picture.bbox (p : Picture) : Box :=
  match p.shapes.toList with
  | [] => ((0, 0), (0, 0))
  | s :: rest => bboxList s.box rest

theorem bboxList_le (acc : Box) (xs : List Shape) : Box.le acc (bboxList acc xs) := by
  induction xs generalizing acc with
  | nil => exact Box.le_refl acc
  | cons s rest ih =>
    exact Box.le_trans (Box.le_join_left acc s.box) (ih (Box.join acc s.box))

theorem bboxList_mem (acc : Box) (xs : List Shape) (s : Shape) (h : s ∈ xs) :
    Box.le s.box (bboxList acc xs) := by
  induction xs generalizing acc with
  | nil => cases h
  | cons t rest ih =>
    cases h with
    | head =>
      exact Box.le_trans (Box.le_join_right acc s.box) (bboxList_le _ rest)
    | tail _ hmem => exact ih (Box.join acc t.box) hmem

/-- The picture stays in its box: the bounding box contains the declared
box of every shape it emits, so nothing the picture draws stands outside
what layout measures for it (labels bound at their anchors, see
`Shape.box`). -/
theorem Picture.box_in_bbox (p : Picture) (s : Shape) (h : s ∈ p.shapes) :
    Box.le s.box p.bbox := by
  have h' : s ∈ p.shapes.toList := by simpa using h
  unfold Picture.bbox
  split
  · next heq => rw [heq] at h'; cases h'
  · next t rest heq =>
    rw [heq] at h'
    cases h' with
    | head => exact bboxList_le _ rest
    | tail _ hmem => exact bboxList_mem _ rest s hmem

/-- Where a picture lands on a page: the map from picture coordinates
(y up) to layout coordinates (y down). The elaborator has already applied
`scale=`, so what is left is a translation and the y reflection — affine
with unit determinant, hence exactly invertible over sp
(`ofPage_toPage`/`toPage_ofPage`), monotone in x and antitone in y
(`toPage_box`): a shape's placed box is the transform of its declared box,
corner for corner, so a diagram cannot silently drift off its slot. -/
structure Place where
  /-- Page x where the picture's `xmin` lands (its left edge). -/
  x0 : Sp
  /-- Page y where the picture's `ymax` lands (its top edge). -/
  yTop : Sp
  xmin : Sp
  ymax : Sp
  deriving Repr, BEq, Inhabited

def Place.toPage (t : Place) (u : Sp × Sp) : Sp × Sp :=
  (t.x0 + (u.1 - t.xmin), t.yTop + (t.ymax - u.2))

def Place.ofPage (t : Place) (q : Sp × Sp) : Sp × Sp :=
  (t.xmin + (q.1 - t.x0), t.ymax - (q.2 - t.yTop))

/-- The placement transform loses nothing: every page point recovers its
picture point exactly. -/
theorem Place.ofPage_toPage (t : Place) (u : Sp × Sp) : t.ofPage (t.toPage u) = u := by
  obtain ⟨ux, uy⟩ := u
  have hx : ∀ a b c : Int, b + (a + (c - b) - a) = c := by intro a b c; omega
  have hy : ∀ m yT q : Int, m - (yT + (m - q) - yT) = q := by intro m yT q; omega
  simp only [toPage, ofPage, Prod.mk.injEq]
  exact ⟨hx _ _ _, hy _ _ _⟩

theorem Place.toPage_ofPage (t : Place) (q : Sp × Sp) : t.toPage (t.ofPage q) = q := by
  obtain ⟨qx, qy⟩ := q
  have hx : ∀ a b c : Int, b + (a + (c - b) - a) = c := by intro a b c; omega
  have hy : ∀ yT m q : Int, yT + (m - (m - (q - yT))) = q := by intro yT m q; omega
  simp only [toPage, ofPage, Prod.mk.injEq]
  exact ⟨hx _ _ _, hy _ _ _⟩

/-- The transform preserves containment: a picture point inside a declared
box lands inside that box's transform — x keeps its order, y reverses, so
the placed box's top-left corner is the declared box's `(xmin, ymax)`. With
`box_in_bbox` this is why no shape escapes the placed picture. -/
theorem Place.toPage_box (t : Place) (b : Box) (u : Sp × Sp)
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

/-- Horizontal alignment of a table column's cells: `l`, `c`, `r`. -/
inductive HAlign where
  | left
  | center
  | right
  deriving Repr, BEq, Inhabited

/-- A table column's declared width. `p{0.31\linewidth}` is a fraction of
the measure, `p{54pt}` an absolute length; `l`/`c`/`r` size to the widest
cell (`natural`), as LaTeX's own column types do. -/
inductive ColWidth where
  | natural
  | frac (permille : Nat)
  | abs (w : Sp)
  deriving Repr, BEq, Inhabited

/-- One column of a table, from the `tabular` column spec. A `p` column
wraps its cells at the declared width; `l`/`c`/`r` set each cell as one
unbreakable line. -/
structure ColSpec where
  width : ColWidth
  align : HAlign
  deriving Repr, BEq, Inhabited

/-- A horizontal rule (or declared row gap) inside a table, booktabs'
vocabulary: `top` and `bottom` draw at `heavyRuleWidth`, `mid` at
`lightRuleWidth`, and each carries its documented padding
(`aboveTopSep`/`aboveRuleSep` over it, `belowRuleSep`/`belowBottomSep`
under). `cmid` is `\cmidrule`: `cmidRuleWidth` across columns `a`–`b`
(1-based, inclusive), each end trimmed by `cmidRuleKern` when its flag is
set. `gap` is `\addlinespace` (and `\\[len]`): no ink, declared space. -/
inductive TableRule where
  | top
  | mid
  | bottom
  | cmid (a : Nat) (b : Nat) (trimL : Bool) (trimR : Bool)
  | gap (space : SymGlue)
  deriving Repr, BEq, Inhabited

/-- What a float wraps: `{figure}` or `{table}`, or a `{subfigure}`/
`{subtable}` box inside one (`sub`). The kinds differ in name and in which
counter numbers them (`numberFloats`); the caption and separation
machinery is one. -/
inductive FloatKind where
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
inductive AlgIo where
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
inductive AlgOpen where
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
inductive AlgKind where
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
structure AlgLine where
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
structure AlgWords where
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
def algWords (tag : String) : AlgWords :=
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
def AlgWords.all (w : AlgWords) : List String :=
  [w.forKw, w.foreachKw, w.whileKw, w.doKw, w.ifKw, w.thenKw, w.elseIfKw,
   w.elseKw, w.repeatKw, w.untilKw, w.endKw, w.returnKw, w.inputKw,
   w.outputKw, w.dataKw, w.resultKw, w.functionKw, w.procedureKw]

/-- The opener's keyword pair: the word before the condition and the word
after it (`for … do`, `if … then`; `else` and `repeat` stand alone). -/
def AlgOpen.words (w : AlgWords) : AlgOpen → String × Option String
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
def AlgIo.word (w : AlgWords) : AlgIo → String
  | .input => w.inputKw
  | .output => w.outputKw
  | .data => w.dataKw
  | .result => w.resultKw
  | .named label => label

/-- The opener's dump spelling, for goldens. -/
def AlgOpen.name : AlgOpen → String
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
def AlgIo.name : AlgIo → String
  | .input => "input"
  | .output => "output"
  | .data => "data"
  | .result => "result"
  | .named label => s!"named {label.quote}"

/-- The line kind's dump spelling, for goldens. -/
def AlgKind.name : AlgKind → String
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
def mutedOf (pal : Palette) : Color :=
  (pal.find? "muted").getD ((pal.find? "fg").getD Color.black)

/-- One algorithm line as display inlines — the one site both backends
read, so the page and the HTML list item spell a line identically
(`algorithm_lines_agree` is the statement). Keywords set bold
(algorithm2e's `\KwSty` default `\textbf`); the comment sets in the muted
role between algorithm2e's own `/* … */` fences (`\tcc`'s default
comment style); `semis` closes statement, io and return lines with the
`;` algorithm2e prints for `\;` unless `\DontPrintSemicolon`. -/
def AlgLine.rendered (w : AlgWords) (semis : Bool) (muted : Color)
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
def padTableRows (rows : Array (Array (Array Inline))) (n : Nat) :
    Array (Array (Array Inline)) :=
  rows.map fun r => r ++ Array.replicate (n - r.size) #[]

/-- Padding conserves content exactly: each padded row is the original's
cells followed by empties — nothing dropped, nothing reordered. -/
theorem padTableRows_cells (rows : Array (Array (Array Inline))) (n i : Nat)
    (h : i < rows.size) :
    (padTableRows rows n)[i]'(by simpa [padTableRows] using h)
      = rows[i] ++ Array.replicate (n - rows[i].size) #[] := by
  simp [padTableRows]

/-- A padded grid is rectangular: every row of `padTableRows rows n` has
exactly `n` cells when none had more — the invariant every walk over
`.table` trusts (`cols.size` is every row's size), sourced from the same
need as the alignment grid's: a column's alignment point is one x for
every row. -/
theorem padTableRows_rectangular (rows : Array (Array (Array Inline))) (n : Nat)
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
structure Pin where
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
structure NavSpec where
  label : Option String := none
  pin : Option Pin := none
  deriving Repr, BEq, Inhabited

/-- One reference-list entry, resolved: its key (the HTML anchor and what
`\cite` spells), the marker the style shows beside it (the position for a
numeric style, nothing for author-year lists, which mark no entries), and
its content formatted per the style. `Bib.apply` builds these; a backend
only structures them. -/
structure BibItem where
  key : String
  marker : Option String
  content : Array Inline
  deriving Repr, BEq, Inhabited

/-- The titled block's kind, closed: beamer's three block environments
(`{block}`, `{alertblock}`, `{exampleblock}` — beamer user guide §12.3,
"Highlighting"). The kind selects the role pair the title resolves
through (`titledLook`); nothing else about the node differs per kind —
a poster and a deck set the same node at different base sizes. -/
inductive TitledKind where
  | block
  | alert
  | example
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The kind's one spelling: the HTML class suffix and the role-key stem
(`alerttitlefg`), one naming site for both backends. -/
def TitledKind.name : TitledKind → String
  | .block => "block"
  | .alert => "alert"
  | .example => "example"

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
are. A bare `{verbatim}` is the default value everywhere. -/
structure ListingSpec where
  caption : Option (Nat × Array Inline) := none
  numbers : Bool := false
  deriving Repr, BEq, Inhabited

inductive Block where
  | para (content : Array Inline)
  /-- A heading. `number` is the section's resolved number ("2", "2.1",
  "A.2" after `\appendix`), assigned at elaboration in flow order — article
  numbers unstarred levels 1–3 (classes.dtx §Sectioning, secnumdepth 3);
  slides and card documents, and every starred form, carry `none`. The
  number rides beside the title, never inside it, so a backend renders it
  as its own structural piece (classes.dtx's `\@seccntformat`: number then
  `\quad`) and the HTML anchor still derives from the title text alone —
  numbering a section must not move its anchor. -/
  | section (level : Nat) (starred : Bool) (number : Option String) (title : Array Inline)
  | list (ordered : Bool) (items : Array (Array Block))
  | center (body : Array Block)
  /-- Left-aligned unjustified setting for a scope — `\flushleft` and
  `\raggedright`'s meaning (ltmiscen.dtx: `{flushleft}` is a trivlist under
  `\raggedright`). The lines break ragged and keep the engine's left
  origin; the one alignment beside `center` a page can declare per block.
  Right-ragged setting (`\flushright`/`\raggedleft`) stays a named loss:
  line placement knows no right origin yet. -/
  | ragged (body : Array Block)
  /-- `\block[before = <len>]{...}`: content with declared space above. -/
  | spaced (before : SymGlue) (body : Array Block)
  /-- The block half of `Inline.role`: a document-defined command whose
  expansion is block content (`\entry{...}` producing whole paragraphs)
  keeps its authored name the same way — `<div class="u-name">` in HTML,
  a transparent group everywhere else. -/
  | role (name : String) (body : Array Block)
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
  elaboration; `content` is the formula — or its source-text degradation —
  preceded by the `\label` anchors the environment carried. The number is
  structural in both backends: right-aligned beside the centred formula on
  the page, its own element in HTML, never text glued into the formula.
  The unnumbered forms keep the plain centred-paragraph shape. -/
  | equation (number : String) (content : Array Inline)
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
  vertical distribution (`[t]`/`[c]`/`[b]`; `center` unless declared). -/
  | frame (title : Array Inline) (standout : Bool) (valign : VAlign) (body : Array Block)
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
  the thickness is symbolic so a token may state it in em. -/
  | rule (color : Color) (name : Option String) (thickness : SymGlue)
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
  `tabColSep` pads, deleted by `@{}` as in LaTeX. -/
  | table (cols : Array ColSpec) (padLeft : Bool) (padRight : Bool)
      (rows : Array (Array (Array Inline))) (rules : Array (Nat × TableRule))
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

/-- One footnote mark's number against the counter: an override
(`\footnote[n]{...}`) is itself and steps nothing — LaTeX's own semantics,
where the optional argument sets the mark without `\stepcounter` (source2e,
ltmiscen.dtx `\@xfootnote`) — and an ordinary mark takes the next value.
The elaborator's per-mark step; `footnoteMarksFrom` is its fold and
`footnote_numbers_gapless` its contract. -/
def footnoteMark (k : Nat) (override : Option Nat) : Nat × Nat :=
  match override with
  | some n => (n, k)
  | none => (k + 1, k + 1)

/-- The footnote numbering fold: `footnoteMark` over the marks' overrides
in flow order — what running the elaborator's step over a whole document
assigns. -/
def footnoteMarksFrom (k : Nat) : List (Option Nat) → List Nat
  | [] => []
  | o :: rest => (footnoteMark k o).1 :: footnoteMarksFrom (footnoteMark k o).2 rest

/-- Footnote marks in flow order are gapless: over any override pattern,
the unoverridden marks number `k+1, k+2, …` exactly — `numbers_gapless`
instantiated at the footnote counter's step. An override never steps, so
`\footnote{a}\footnote[7]{b}\footnote{c}` numbers 1, 7, 2. -/
theorem footnote_numbers_gapless (k : Nat) (os : List (Option Nat)) :
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

-- Float numbering. LaTeX steps a float's counter inside `\caption`
-- (classes.dtx: `\caption` is `\refstepcounter` then `\@makecaption`), so
-- a captionless float bears no number; and this engine's floats never
-- float, so document order IS first-appearance order. `numberFloats` is
-- the one assignment site: elaboration writes `none`, this pass fills the
-- numbers, and both backends only replay what the node carries.

/-- The counters `numberFloats` threads: captioned figures, captioned
tables, and — reset at every float body, restored after it — captioned
subfloats, so a letter is an index within its own parent. -/
structure FloatCtr where
  fig : Nat := 0
  tab : Nat := 0
  sub : Nat := 0
  alg : Nat := 0
  deriving Repr, BEq

def FloatCtr.get : FloatCtr → FloatKind → Nat
  | c, .figure => c.fig
  | c, .table => c.tab
  | c, .sub => c.sub
  | c, .algorithm => c.alg

def FloatCtr.bump : FloatCtr → FloatKind → FloatCtr
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
def numberFloatList (c : FloatCtr) (out : Array Block) :
    List Block → FloatCtr × Array Block
  | [] => (c, out)
  | b :: rest =>
    let (c2, b2) := numberFloatOne c b
    numberFloatList c2 (out.push b2) rest

def numberFloatOne (c : FloatCtr) : Block → FloatCtr × Block
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
  | .ragged body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .ragged body2)
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
  | .spaced g body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .spaced g body2)
  | .columns cols =>
    let (c2, cols2) := numberFloatCols c #[] cols.toList
    (c2, .columns cols2)
  | .step n l body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .step n l body2)
  | .only targets body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .only targets body2)
  | .nav spec body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .nav spec body2)
  | .frame t s v body =>
    let (c2, body2) := numberFloatList c #[] body.toList
    (c2, .frame t s v body2)
  | .note body => (c, .note body)
  | .verbatim k s sp => (c, .verbatim k s sp)
  | .logo content => (c, .logo content)
  | .framefoot content => (c, .framefoot content)
  | .setPalette p => (c, .setPalette p)
  | .setTokens tk => (c, .setTokens tk)
  | .pagebreak => (c, .pagebreak)
  | .rule col nm th => (c, .rule col nm th)
  | .picture p => (c, .picture p)
  | .table cols pl pr rows rules => (c, .table cols pl pr rows rules)
  -- Lines hold inlines: no float can nest in an algorithm.
  | .algorithm n sm lines => (c, .algorithm n sm lines)
  -- A reference list is not a float: it consumes no number and holds none.
  | .bibliography src style items => (c, .bibliography src style items)
  | .float kind _ capAbove body caption =>
    let cAfter := if caption.isEmpty then c else c.bump kind
    let num := if caption.isEmpty then none else some (c.get kind + 1)
    let (cBody, body2) := numberFloatList { cAfter with sub := 0 } #[] body.toList
    (⟨cBody.fig, cBody.tab, cAfter.sub, cBody.alg⟩, .float kind num capAbove body2 caption)

def numberFloatItems (c : FloatCtr) (out : Array (Array Block)) :
    List (Array Block) → FloatCtr × Array (Array Block)
  | [] => (c, out)
  | item :: rest =>
    let (c2, item2) := numberFloatList c #[] item.toList
    numberFloatItems c2 (out.push item2) rest

def numberFloatCols (c : FloatCtr) (out : Array (Option Nat × Array Block)) :
    List (Option Nat × Array Block) → FloatCtr × Array (Option Nat × Array Block)
  | [] => (c, out)
  | (w, body) :: rest =>
    let (c2, body2) := numberFloatList c #[] body.toList
    numberFloatCols c2 (out.push (w, body2)) rest

end

/-- Assign every float its number: the pass elaboration hands the finished
body to, once, before any backend reads it. -/
def numberFloats (xs : Array Block) : Array Block :=
  (numberFloatList {} #[] xs.toList).2

mutual

/-- The numbers the walk assigned to captioned floats of kind `k`, in
document order — the collector `numberFloats_exact` judges the walk by.
For `.sub` it reads a body's own letters: it does not descend into a
nested float's body, whose letters belong to that float. For `.figure`
and `.table` it descends everywhere the walk threads its counters. -/
def floatNumsList (k : FloatKind) (out : List Nat) : List Block → List Nat
  | [] => out
  | b :: rest => floatNumsList k (floatNumsOne k out b) rest

def floatNumsOne (k : FloatKind) (out : List Nat) : Block → List Nat
  | .para _ => out
  | .equation _ _ => out
  | .section _ _ _ _ => out
  | .list _ items => floatNumsItems k out items.toList
  | .center body => floatNumsList k out body.toList
  | .ragged body => floatNumsList k out body.toList
  | .quote body => floatNumsList k out body.toList
  | .abstract body => floatNumsList k out body.toList
  | .titled _ _ body => floatNumsList k out body.toList
  | .role _ body => floatNumsList k out body.toList
  | .spaced _ body => floatNumsList k out body.toList
  | .columns cols => floatNumsCols k out cols.toList
  | .step _ _ body => floatNumsList k out body.toList
  | .only _ body => floatNumsList k out body.toList
  | .nav _ body => floatNumsList k out body.toList
  | .frame _ _ _ body => floatNumsList k out body.toList
  | .note _ => out
  | .verbatim _ _ _ => out
  | .logo _ => out
  | .framefoot _ => out
  | .setPalette _ => out
  | .setTokens _ => out
  | .pagebreak => out
  | .rule _ _ _ => out
  | .picture _ => out
  | .table _ _ _ _ _ => out
  | .algorithm _ _ _ => out
  | .bibliography _ _ _ => out
  | .float kind num _ body _ =>
    let out := match num with
      | some n => if kind = k then out ++ [n] else out
      | none => out
    if k = .sub then out else floatNumsList k out body.toList

def floatNumsItems (k : FloatKind) (out : List Nat) :
    List (Array Block) → List Nat
  | [] => out
  | item :: rest => floatNumsItems k (floatNumsList k out item.toList) rest

def floatNumsCols (k : FloatKind) (out : List Nat) :
    List (Option Nat × Array Block) → List Nat
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
theorem numberFloatList_exact (k : FloatKind) (c : FloatCtr) (acc : Array Block)
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

theorem numberFloatOne_exact (k : FloatKind) (c : FloatCtr) (out : List Nat)
    (b : Block) :
    ∃ n, ((numberFloatOne c b).1).get k = c.get k + n ∧
      floatNumsOne k out (numberFloatOne c b).2
        = out ++ List.range' (c.get k + 1) n := by
  match b with
  | .para _ | .equation _ _ | .section _ _ _ _ | .note _ | .verbatim _ _ _ | .logo _
  | .algorithm _ _ _
  | .bibliography _ _ _
  | .framefoot _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .table _ _ _ _ _ =>
    exact ⟨0, by simp [numberFloatOne], by simp [numberFloatOne, floatNumsOne]⟩
  | .list o items =>
    obtain ⟨n, hc, hn⟩ := numberFloatItems_exact k c #[] out items.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsItems] using hn⟩
  | .center body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .ragged body =>
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
  | .spaced _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .columns cols =>
    obtain ⟨n, hc, hn⟩ := numberFloatCols_exact k c #[] out cols.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsCols] using hn⟩
  | .step _ _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .only _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .nav _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .frame _ _ _ body =>
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

theorem numberFloatItems_exact (k : FloatKind) (c : FloatCtr)
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

theorem numberFloatCols_exact (k : FloatKind) (c : FloatCtr)
    (acc : Array (Option Nat × Array Block)) (out : List Nat)
    (cols : List (Option Nat × Array Block)) :
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
      have happ : ∀ (l1 : List (Option Nat × Array Block)) (o : List Nat)
          (x : Option Nat × Array Block),
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
theorem numberFloats_exact (k : FloatKind) (xs : Array Block) :
    floatNumsList k [] (numberFloats xs).toList
      = List.range' 1 (((numberFloatList {} #[] xs.toList).1).get k) := by
  obtain ⟨n, hc, hn⟩ := numberFloatList_exact k {} #[] [] xs.toList
  have h0 : (({} : FloatCtr)).get k = 0 := by cases k <;> rfl
  rw [h0] at hc hn
  simpa [numberFloats, floatNumsList, hc] using hn

/-- A subfloat's letter is its index within its own parent: every float
body enters the walk with the sub counter reset to zero (the `.float` arm
of `numberFloatOne`), so the letters assigned inside it — read shallowly,
a nested float's letters belonging to that float — are exactly `1, 2, …`
(subcaption: `\thesubfigure` is `(\alph{subfigure})`, an index within the
parent figure). -/
theorem numberFloats_sub_letters (c : FloatCtr) (body : Array Block) :
    floatNumsList .sub []
        ((numberFloatList { c with sub := 0 } #[] body.toList).2).toList
      = List.range' 1
        (((numberFloatList { c with sub := 0 } #[] body.toList).1).get .sub) := by
  obtain ⟨n, hc, hn⟩ :=
    numberFloatList_exact .sub { c with sub := 0 } #[] [] body.toList
  have h0 : (({ c with sub := 0 } : FloatCtr)).get .sub = 0 := rfl
  rw [h0] at hc hn
  simpa [floatNumsList, hc] using hn

/-- A subfloat's letter: `\alph` (1 → a, …, 26 → z). LaTeX's `\alph`
errors past 26; past it this engine sets the number itself — degraded,
never silent, and a 27-subfigure float has larger problems. -/
def subLetter (n : Nat) : String :=
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
def captionPrefix (loc : Locale) (kind : FloatKind) (num : Option Nat) : Option String :=
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
def numberedCaption (loc : Locale) (kind : FloatKind) (num : Option Nat)
    (caption : Array Inline) : Array Inline :=
  match captionPrefix loc kind num with
  | some p => (Inline.text p :: caption.toList).toArray
  | none => caption

/-- A listing caption with its number prefix set in front: the
figure-caption shape (`captionPrefix`'s own spelling, classes.dtx
§\@makecaption) with the locale's listing word — "Listing 1: text" —
the one site both backends spell a listing's number from, so the PDF and
the HTML cannot drift. The prefix is furniture the backend adds, exactly
as `numberedCaption`'s is: the IR keeps the declared text alone. -/
-- conserves: none — the prefix is furniture the backend adds at emission,
-- never a rewrite of the stored document: the IR's caption census stays
-- the declared text alone, exactly as `numberedCaption`'s does.
def listingCaption (loc : Locale) (n : Nat) (caption : Array Inline) : Array Inline :=
  (Inline.text s!"{loc.listing} {n}: " :: caption.toList).toArray

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
`separator`; the other keys have no meaning there yet); `logo` reads
`align` only — where the logo stands in the furniture band (`logoAlign`,
both backends). Beyond this list, a
`\define`d name is styleable too (the elaborator admits it once the
`\define` stands): the role's rhythm rides `before`/`after` on the page,
and the whole style addresses the `u-<name>` class hook in HTML. -/
def styleableElements : List String :=
  ["section", "subsection", "subsubsection", "abstract", "itemize", "enumerate",
   "itemize2", "itemize3", "itemize4", "enumerate2", "enumerate3", "enumerate4",
   "frametitle", "sectionpage", "standout", "titlepage", "nav", "logo"]

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

/-- The abstract heading's style is the section heading's, centred: a
reference, not a copy, so a venue or theme that restyles sections carries
the abstract heading with it — the class's own relation (the NeurIPS
lineage sets both headings `\large\bf`, differing only in alignment:
section `\raggedright`, Abstract centred; article.cls sets both in the
bold face). An explicit `\style{abstract}` key wins per key;
`abstract_heading_follows_section` is the equation. Undeclared on both
sides, `font` is `none` and each backend keeps its class-sourced default. -/
def abstractHeadingStyle (styles : Styles) : ElementStyle :=
  let sec := (styles.find? "section").getD {}
  let own := (styles.find? "abstract").getD {}
  { own with
    font := own.font <|> sec.font
    align := own.align <|> some "center" }

/-- With no explicit `\style{abstract}`, the abstract heading's font equals
the section heading's, and it centres — by construction of the derivation,
which is what keeps the two headings from drifting when a venue or theme
restyles sections. -/
theorem abstract_heading_follows_section (styles : Styles)
    (h : styles.find? "abstract" = none) :
    (abstractHeadingStyle styles).font =
      ((styles.find? "section").getD {}).font ∧
    (abstractHeadingStyle styles).align = some "center" := by
  simp [abstractHeadingStyle, h]

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
merges per slot, and a theme's chrome installs through the same per-slot
merge (`Theme.apply`) — a theme fills the slots the document left empty,
and naming one slot never clears its sibling. -/
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
  | .role n body =>
    .role n (if body.isEmpty then content else (fillList content body.toList).toArray)
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
  | .icon s l => .icon s l
  | .label k => .label k
  | .ref k p t tg => .ref k p t tg
  | .fill => .fill
  | .strut h => .strut h
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak e => .linebreak e
  -- a citation carries no inline body: it cannot hold the template's hole
  | .cite t ks => .cite t ks
  -- a footnote's body is the note's own text, never a template hole
  | .footnote n body => .footnote n body

def fillList (content : Array Inline) : List Inline → List Inline
  | [] => []
  | x :: rest => fillOne content x :: fillList content rest

end

/-- Fill a font template's hole with content. The hole is the innermost empty
body; a template with no hole (plain content) is returned unchanged, which
is what a marker is. -/
-- conserves: none — a splice, not a walk of one tree: the output census is
-- the template's plus the content's, conservation of neither alone; the
-- styled-heading and marker tests pin the behaviour.
def fillTemplate (template content : Array Inline) : Array Inline :=
  if template.isEmpty then content else (fillList content template.toList).toArray

/-- The kernel's page models: how content maps onto the surfaces the paged
backends draw. Three today; `report`'s chapter-opens-a-page is the one
candidate fourth. HTML is continuous scroll whatever the model —
scroll-vs-page is per medium, the model per document. -/
inductive PageModel where
  /-- Content flows into a sequence of pages (`article`'s model). -/
  | flow
  /-- A frame is a page boundary; overlays produce steps (`slides`). -/
  | frame
  /-- Fixed faces, no flow: trim sizes and a print safe zone (`card`). -/
  | face
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The page-count bound a class implies, when it implies one: a literal
(`resume`: fits one page) or the document's own declared faces (`card`). -/
inductive PagesBound where
  | lit (op : CmpOp) (n : Int)
  | faces
  deriving Repr, BEq

/-- A document class is a record over one of the kernel's page models:
defaults, furniture flags, implied assertions, build intent — values only,
no code. A class that needs layout code rather than fields here is asking
for a new page model and that is a kernel discussion, not a class. -/
structure ClassRecord where
  model : PageModel
  /-- The class's body-size default, when it declares one (`slides`:
  beamer's documented 11 pt, user guide §18.2.1). -/
  fontSize : Option Sp := none
  /-- The class's paragraph-separation default, when it declares one.
  `resume` declares zero: the LaTeX résumé lineage (moderncv.cls keeps the
  standard classes' zero `\parskip`) spaces entries by declared rhythm,
  not by paragraph skips — the same value compat injects when a foreign
  résumé class is rewritten, so the native spelling and the rewritten one
  agree. -/
  parskip : Option Dim.SymGlue := none
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
inductive DocClass where
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
def DocClass.name : DocClass → String
  | .article => "article"
  | .slides => "slides"
  | .card => "card"
  | .resume => "resume"
  | .webpage => "webpage"
  | .poster => "poster"

/-- The class a `\documentclass` argument names, if any: the inverse of
`name`, and the one door a class enters the IR through. -/
def DocClass.ofString? : String → Option DocClass
  | "article" => some .article
  | "slides" => some .slides
  | "card" => some .card
  | "resume" => some .resume
  | "webpage" => some .webpage
  | "poster" => some .poster
  | _ => none

theorem DocClass.ofString?_name (c : DocClass) : ofString? c.name = some c := by
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
def DocClass.record : DocClass → ClassRecord
  | .article =>
    { model := .flow
      numberHeadings := true
      measureBand := true
      pageNumbers := true }
  | .slides =>
    { model := .frame
      fontSize := some slidesFontSize
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
      formats := #["html", "md"]
      mdName := some "llms.txt" }
  | .poster =>
    { model := .face
      fontSize := some posterFontSize
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
theorem poster_model_face : (DocClass.poster).record.model = .face := rfl

structure Doc where
  docClass : DocClass := .article
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
  /-- The boundary tool in force: the external TeX the driver runs for
  pictures outside the rendered subset — the document's pin
  (`\pictures{ tool = lualatex }`, or the `\tikzexternalize` spelling) or
  the engine default, the boundary being open by default. `none` is the
  declared refusal (`tool = none`): nothing routes, so no request rides. -/
  pictureTool : Option String := some "lualatex"
  /-- The boundary requests this document states: content hash of each
  wrapped standalone source, with the source itself — the `bibRefs` shape.
  The driver fulfils each by running the declared tool (cached under the
  hash), and the result embeds through the image path as a measured form
  XObject. The trust label: the engine claims the *box*, never the
  contents. -/
  pictureSrcs : Array (String × String) := #[]
  body : Array Block := #[]
  deriving Repr, BEq, Inhabited

/-- The document's one frame numbering (T2–T4 hold over it). -/
def Doc.frameNumbers (doc : Doc) : Array (Option Nat) :=
  Ir.frameNumbers doc.body

/-- The numbering's denominator for the document. -/
def Doc.frameCount (doc : Doc) : Nat :=
  Ir.frameCount doc.body

/-- Whether this document's pages carry the plain page number: the
document's own `\page{ numbers = ... }` wins; an undeclared document takes
its class record's default (`ClassRecord.pageNumbers`). One resolving site,
read by layout's furniture pass and the driver's glyph precompute alike. -/
def Doc.pageNumbersOn (doc : Doc) : Bool :=
  doc.page.numbers.getD doc.docClass.record.pageNumbers

/-- Whether counted body lines carry margin line numbers: the document's
own declaration and nothing else — no class default turns line numbers
on (the page key is a declared flag, never a default). One resolving
site, read by layout's furniture pass and the driver's glyph precompute
alike. -/
def Doc.lineNumbersOn (doc : Doc) : Bool :=
  doc.page.linenumbers.getD false

/-- The line-number modulus in force: 1 — every counted line — unless
declared. Floored at 1 so the printing test `count % modulus == 0` is
meaningful for every declaration that reached the spec. -/
def Doc.lineModulo (doc : Doc) : Nat :=
  max 1 (doc.page.lineModulo.getD 1)

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
  | .role _ body => plainTextList body.toList
  | .link _ body => plainTextList body.toList
  | .underline body => plainTextList body.toList
  | .step _ _ body => plainTextList body.toList
  | .fill | .strut _ | .pageNumber | .pageCount => ""
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

/-- A role is a name around content, never content: the census reads
straight through it, so no annotation can add or hide a character. -/
theorem role_plaintext (n : String) (body : Array Inline) :
    plainTextOne (.role n body) = plainTextList body.toList := rfl

mutual

/-- One leaf-parameterised fold hosts every collect walk over the tree:
`fi` reads each inline node — applied to the node itself, never to
children, so the recursion below stays explicit and the checker sees it.
Document order, a node before its content. -/
def foldInline (fi : α → Inline → α) (acc : α) (x : Inline) : α :=
  match x with
  | .styled _ body => foldInlineList fi (fi acc x) body.toList
  | .colored _ _ body => foldInlineList fi (fi acc x) body.toList
  | .role _ body => foldInlineList fi (fi acc x) body.toList
  | .link _ body => foldInlineList fi (fi acc x) body.toList
  | .underline body => foldInlineList fi (fi acc x) body.toList
  | .step _ _ body => foldInlineList fi (fi acc x) body.toList
  | .footnote _ body => foldInlineList fi (fi acc x) body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _ => fi acc x

def foldInlineList (fi : α → Inline → α) (acc : α) : List Inline → α
  | [] => acc
  | x :: rest => foldInlineList fi (foldInline fi acc x) rest

end

/-- `foldInline` over an inline tree, the collectors' entry. -/
def foldInlines (fi : α → Inline → α) (acc : α) (xs : Array Inline) : α :=
  foldInlineList fi acc xs.toList

def foldTableCells (fi : α → Inline → α) (acc : α) : List (Array Inline) → α
  | [] => acc
  | cell :: rest => foldTableCells fi (foldInlineList fi acc cell.toList) rest

/-- `foldInline` over algorithm lines: each line's content, then its
comment, in reading order — one spelling for every collector, so no two
can disagree on what an algorithm declares. -/
def foldAlgLines (fi : α → Inline → α) (acc : α) : List AlgLine → α
  | [] => acc
  | l :: rest =>
    foldAlgLines fi (match l.comment with
      | some c => foldInlineList fi (foldInlineList fi acc l.content.toList) c.toList
      | none => foldInlineList fi acc l.content.toList) rest

def foldTableRows (fi : α → Inline → α) (acc : α) :
    List (Array (Array Inline)) → α
  | [] => acc
  | row :: rest => foldTableRows fi (foldTableCells fi acc row.toList) rest

mutual

/-- The block face of the fold: `fb` reads each block, `fi` each inline —
the node first, a frame's title and a float's caption before their bodies,
as the collectors this fold hosts always read them. A `.bibliography`'s
items are formatted renderings, not authored content, so the fold reads
the marker itself and does not descend into them. -/
def foldBlock (fb : α → Block → α) (fi : α → Inline → α) (acc : α) (b : Block) : α :=
  match b with
  | .para content => foldInlineList fi (fb acc b) content.toList
  | .equation _ content => foldInlineList fi (fb acc b) content.toList
  | .section _ _ _ title => foldInlineList fi (fb acc b) title.toList
  | .list _ items => foldBlockItems fb fi (fb acc b) items.toList
  | .center body => foldBlockList fb fi (fb acc b) body.toList
  | .ragged body => foldBlockList fb fi (fb acc b) body.toList
  | .quote body => foldBlockList fb fi (fb acc b) body.toList
  | .abstract body => foldBlockList fb fi (fb acc b) body.toList
  | .titled _ title body =>
    foldBlockList fb fi (foldInlineList fi (fb acc b) title.toList) body.toList
  | .role _ body => foldBlockList fb fi (fb acc b) body.toList
  | .spaced _ body => foldBlockList fb fi (fb acc b) body.toList
  | .columns cols => foldBlockCols fb fi (fb acc b) cols.toList
  | .step _ _ body => foldBlockList fb fi (fb acc b) body.toList
  | .only _ body => foldBlockList fb fi (fb acc b) body.toList
  | .nav _ body => foldBlockList fb fi (fb acc b) body.toList
  | .note body => foldBlockList fb fi (fb acc b) body.toList
  | .frame title _ _ body =>
    foldBlockList fb fi (foldInlineList fi (fb acc b) title.toList) body.toList
  | .framefoot content => foldInlineList fi (fb acc b) content.toList
  | .float _ _ _ body caption =>
    foldBlockList fb fi (foldInlineList fi (fb acc b) caption.toList) body.toList
  | .table _ _ _ rows _ => foldTableRows fi (fb acc b) rows.toList
  | .algorithm _ _ lines => foldAlgLines fi (fb acc b) lines.toList
  | .logo content => foldInlineList fi (fb acc b) content.toList
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .bibliography _ _ _ => fb acc b

def foldBlockList (fb : α → Block → α) (fi : α → Inline → α) (acc : α) :
    List Block → α
  | [] => acc
  | b :: rest => foldBlockList fb fi (foldBlock fb fi acc b) rest

def foldBlockItems (fb : α → Block → α) (fi : α → Inline → α) (acc : α) :
    List (Array Block) → α
  | [] => acc
  | item :: rest => foldBlockItems fb fi (foldBlockList fb fi acc item.toList) rest

def foldBlockCols (fb : α → Block → α) (fi : α → Inline → α) (acc : α) :
    List (Option Nat × Array Block) → α
  | [] => acc
  | (_, body) :: rest => foldBlockCols fb fi (foldBlockList fb fi acc body.toList) rest

end

/-- `foldBlock` over a block tree: `bibRefs`, `bibStyleName`, and
`BibStyle.citedKeys` are leaf projections of this one traversal. -/
def foldBlocks (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (xs : Array Block) : α :=
  foldBlockList fb fi acc xs.toList

/-- Does any node of the inline content satisfy `p`? The Bool face of the
fold — the trigger census the conditional-identity schema
(`mapInlines_id`) and `hasPhysicalPage` read. -/
def anyInline (p : Inline → Bool) (xs : Array Inline) : Bool :=
  foldInlines (fun b x => b || p x) false xs


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
  String.ofList (slugGo #[] false (plainText title).toList).toList

theorem slugCharKeep_not_whitespace (k k' : Char) (h : slugCharKeep k = some k') :
    isWhiteSpaceUni k' = false := by
  unfold slugCharKeep at h
  (repeat' split at h) <;> simp_all

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

-- Navigation links: what a paged surface renders an unpinned nav as — the
-- document outline. Structural recursion through `List`, as the walks above.

mutual

/-- Every link of a navigation landmark's body, in document order, as
(text, target). -/
-- conserves: none — a projection of the links alone: a nav is furniture on
-- the paged surface, and only its links are navigation; what its body must
-- NOT ship there is pinned by the webnav census and the nav layout tests.
def navLinkList (out : Array (String × String)) : List Block → Array (String × String)
  | [] => out
  | b :: rest => navLinkList (navLinkOne out b) rest

def navLinkOne (out : Array (String × String)) : Block → Array (String × String)
  | .para content => navLinkInlineList out content.toList
  | .equation _ content => navLinkInlineList out content.toList
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
  | .ragged body => navLinkList out body.toList
  | .quote body => navLinkList out body.toList
  | .abstract body => navLinkList out body.toList
  | .titled _ title body => navLinkList (navLinkInlineList out title.toList) body.toList
  | .role _ body => navLinkList out body.toList
  | .spaced _ body => navLinkList out body.toList
  | .columns cols => navLinkColumns out cols.toList
  | .step _ _ body => navLinkList out body.toList
  -- a speaker note is a side channel in every backend; never navigation
  | .note _ => out
  | .only _ body => navLinkList out body.toList
  | .nav _ body => navLinkList out body.toList
  | .frame title _ _ body => navLinkList (navLinkInlineList out title.toList) body.toList
  | .table _ _ _ rows _ => navLinkRows out rows.toList
  | .float _ _ _ body caption => navLinkInlineList (navLinkList out body.toList) caption.toList
  | .algorithm _ _ lines => navLinkAlgLines out lines.toList
  -- a resolved entry's content carries its URL and anchor links
  | .bibliography _ _ items => navLinkBibItems out items.toList

def navLinkBibItems (out : Array (String × String)) :
    List BibItem → Array (String × String)
  | [] => out
  | item :: rest => navLinkBibItems (navLinkInlineList out item.content.toList) rest

def navLinkRows (out : Array (String × String)) :
    List (Array (Array Inline)) → Array (String × String)
  | [] => out
  | row :: rest => navLinkRows (navLinkCells out row.toList) rest

def navLinkCells (out : Array (String × String)) :
    List (Array Inline) → Array (String × String)
  | [] => out
  | cell :: rest => navLinkCells (navLinkInlineList out cell.toList) rest

def navLinkItems (out : Array (String × String)) :
    List (Array Block) → Array (String × String)
  | [] => out
  | item :: rest => navLinkItems (navLinkList out item.toList) rest

def navLinkColumns (out : Array (String × String)) :
    List (Option Nat × Array Block) → Array (String × String)
  | [] => out
  | (_, body) :: rest => navLinkColumns (navLinkList out body.toList) rest

def navLinkAlgLines (out : Array (String × String)) :
    List AlgLine → Array (String × String)
  | [] => out
  | l :: rest =>
    navLinkAlgLines (match l.comment with
      | some c => navLinkInlineList (navLinkInlineList out l.content.toList) c.toList
      | none => navLinkInlineList out l.content.toList) rest

def navLinkInlineList (out : Array (String × String)) :
    List Inline → Array (String × String)
  | [] => out
  | x :: rest => navLinkInlineList (navLinkInline out x) rest

def navLinkInline (out : Array (String × String)) : Inline → Array (String × String)
  -- the link whole: its text is the entry's title (a link cannot nest)
  | .link url body => out.push (plainTextList body.toList, url)
  | .styled _ body => navLinkInlineList out body.toList
  | .colored _ _ body => navLinkInlineList out body.toList
  | .role _ body => navLinkInlineList out body.toList
  | .underline body => navLinkInlineList out body.toList
  | .step _ _ body => navLinkInlineList out body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  -- a footnote's links are the note's own, never navigation entries
  | .footnote _ _
  | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _ => out

end

def navLinks (body : Array Block) : Array (String × String) :=
  navLinkList #[] body.toList

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
  | .accent mark stretch body =>
    -- The combining mark by scalar value: pushed bare it would combine
    -- with the golden's own text.
    let tag := if stretch then "acc*" else "acc"
    (dumpMathList (acc ++ s!"{tag}:{mark.toNat}\{") body).push '}'
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
      | some n => s!"{n} #{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}"
      | none => s!"#{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}"
    s!"{ind}color {tag}\n" ++ dumpInlines (ind ++ "  ") body
  | .role n body =>
    s!"{ind}role {n}\n" ++ dumpInlines (ind ++ "  ") body
  | .link url body =>
    s!"{ind}link {url.quote}\n" ++ dumpInlines (ind ++ "  ") body
  | .underline body =>
    s!"{ind}underline\n" ++ dumpInlines (ind ++ "  ") body
  | .step n last body =>
    s!"{ind}{dumpStepRange n last}\n" ++ dumpInlines (ind ++ "  ") body
  | .fill => s!"{ind}fill\n"
  | .strut _ => s!"{ind}strut\n"
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
  | .icon c label =>
    s!"{ind}icon {(String.ofList [c]).quote} label {label.quote}\n"
  | .cite textual keys =>
    let form := if textual then "citet" else "cite"
    s!"{ind}{form} {String.intercalate " " (keys.toList.map (·.quote))}\n"
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
width. `l:310/1000` is a left `p{.31\linewidth}`; a bare letter is a
natural column. -/
def dumpColSpec (c : ColSpec) : String :=
  let al := match c.align with
    | .left => "l"
    | .center => "c"
    | .right => "r"
  match c.width with
  | .natural => al
  | .frac f => s!"{al}:{f}/1000"
  | .abs w => s!"{al}:{w.toPtString}pt"

def dumpTableRule (r : TableRule) : String :=
  match r with
  | .top => "top"
  | .mid => "mid"
  | .bottom => "bottom"
  | .cmid a b tl tr =>
    let trim := (if tl then "l" else "") ++ (if tr then "r" else "")
    s!"cmid {a}-{b}{if trim.isEmpty then "" else s!"({trim})"}"
  | .gap g => s!"gap {dumpGlue g}"

def dumpTableCells (ind : String) (acc : String) : List (Array Inline) -> String
  | [] => acc
  | cell :: rest =>
    let inner := dumpInlines (ind ++ "  ") cell
    dumpTableCells ind (acc ++ s!"{ind}cell\n" ++ inner) rest

def dumpTableRows (ind : String) (acc : String) : List (Array (Array Inline)) -> String
  | [] => acc
  | row :: rest =>
    dumpTableRows ind (dumpTableCells (ind ++ "  ") (acc ++ s!"{ind}row\n") row.toList) rest

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
  | .equation number content =>
    s!"{ind}equation {number.quote}\n" ++ dumpInlines (ind ++ "  ") content
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
  | .ragged body => s!"{ind}ragged\n" ++ dumpBlocks (ind ++ "  ") body
  | .quote body => s!"{ind}quote\n" ++ dumpBlocks (ind ++ "  ") body
  | .abstract body => s!"{ind}abstract\n" ++ dumpBlocks (ind ++ "  ") body
  | .titled kind title body =>
    s!"{ind}titled {kind.name}\n" ++
    (if title.isEmpty then ""
     else s!"{ind}  title\n" ++ dumpInlines (ind ++ "    ") title) ++
    dumpBlocks (ind ++ "  ") body
  | .role n body => s!"{ind}role {n}\n" ++ dumpBlocks (ind ++ "  ") body
  | .columns cols => s!"{ind}columns\n" ++ dumpColumns (ind ++ "  ") cols.toList
  | .step n last body =>
    s!"{ind}{dumpStepRange n last}\n" ++ dumpBlocks (ind ++ "  ") body
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
    s!"{ind}block before {dumpGlue before}\n" ++ dumpBlocks (ind ++ "  ") body
  | .verbatim covered s spec =>
    s!"{ind}verbatim{if covered.isSome then " covered" else ""}\
{if spec.numbers then " numbers" else ""}" ++
    (match spec.caption with
      | some (n, _) => s!" listing {n}"
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
    s!"{ind}rule{nm} {dumpGlue thickness}\n"
  | .picture pic =>
    -- Every evaluated shape, so a golden witnesses the whole elaboration:
    -- unrolled loops, reduced expressions, resolved colours.
    s!"{ind}picture {pic.shapes.size} shapes\n" ++
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
  | .table cols padL padR rows rules =>
    let spec := String.intercalate "," (cols.toList.map dumpColSpec)
    let pads := (if padL then "" else "@{}") ++ spec ++ (if padR then "" else "@{}")
    let ruleLines := String.join (rules.toList.map fun (i, r) =>
      s!"{ind}  rule {i} {dumpTableRule r}\n")
    dumpTableRows (ind ++ "  ") (s!"{ind}table {pads}\n" ++ ruleLines) rows.toList
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
def coveredFractionDefault : Nat := 38

/-- One foreground/background pairing a themed element ships. -/
structure ColorPair where
  fg : Color
  bg : Color
  deriving Repr, BEq

/-- A titled block's resolved look: the title's ink, and the bar behind it
when the palette declares one — no bar key, no bar, exactly the
frame-title rule. -/
structure TitledLook where
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
def titledLook (pal : Palette) : TitledKind → TitledLook
  | .block =>
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
  /-- The titled block's title look, one per kind (`titledLook`, the one
  resolving site). Total: an undeclared palette pairs the kind's content
  colour with no bar. -/
  blockTitle : TitledLook
  alertTitle : TitledLook
  exampleTitle : TitledLook
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
    blockTitle := titledLook pal .block
    alertTitle := titledLook pal .alert
    exampleTitle := titledLook pal .example
    progress := (pal.find? "progressfg").map fun barFg =>
      { fg := barFg
        bg := (pal.find? "progressbg").getD bg }
    standout := { fg := (pal.find? "standoutfg").getD bg
                  bg := (pal.find? "standoutbg").getD fg }
    separator := (pal.find? "separator").getD fg
    -- The fallback is moloch's own default, `progressbar linewidth=1pt`
    -- (beamerouterthememoloch.dtx, \moloch@outer@setdefaults); the layout
    -- fallback and the bundles' token entries are the same value.
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
   "blocktitlefg", "blocktitlebg",    -- Layout.collectBlock titled arm,
   "alerttitlefg", "alerttitlebg",    --   HtmlDoc.themeCss (titledLook is
   "exampletitlefg", "exampletitlebg",--   the one resolving site)
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
  | .equation _ content => maxStepInlines content
  | .list _ items => maxStepItems items.toList
  | .center body => maxStepBlockList body.toList
  | .ragged body => maxStepBlockList body.toList
  | .quote body => maxStepBlockList body.toList
  | .abstract body => maxStepBlockList body.toList
  -- The title is furniture and does not multiply pages, as a frame
  -- title does not; the body's own steps take theirs.
  | .titled _ _ body => maxStepBlockList body.toList
  | .role _ body => maxStepBlockList body.toList
  | .spaced _ body => maxStepBlockList body.toList
  | .columns cols => maxStepColumns cols.toList
  | .step n last body => max (max n (last.getD n)) (maxStepBlockList body.toList)
  -- Conditional content steps like any other content: a backend that keeps
  -- it must give its overlays their pages. A nav's links may step too.
  | .only _ body => maxStepBlockList body.toList
  | .nav _ body => maxStepBlockList body.toList
  | .section _ _ _ _ => 1
  | .verbatim _ _ _ => 1
  | .algorithm _ _ lines => maxStepAlgLines lines.toList
  | .note _ => 1
  | .frame _ _ _ _ => 1
  | .framefoot _ => 1
  | .setPalette _ => 1
  | .setTokens _ => 1
  | .pagebreak => 1
  | .logo _ => 1
  | .rule _ _ _ => 1
  -- A picture is concrete ink with no overlay structure inside it.
  | .picture _ => 1
  -- A cell's content may step (an overlay reveal per row); the caption is
  -- furniture and does not multiply pages, as a frame title does not.
  | .table _ _ _ rows _ => maxStepTableRows rows.toList
  | .float _ _ _ body _ => maxStepBlockList body.toList
  -- A reference list is furniture like a section title: no overlay inside.
  | .bibliography _ _ _ => 1

def maxStepTableRows : List (Array (Array Inline)) → Nat
  | [] => 1
  | row :: rest => max (maxStepTableCells row.toList) (maxStepTableRows rest)

def maxStepTableCells : List (Array Inline) → Nat
  | [] => 1
  | cell :: rest => max (maxStepInlines cell) (maxStepTableCells rest)

def maxStepItems : List (Array Block) → Nat
  | [] => 1
  | item :: rest => max (maxStepBlockList item.toList) (maxStepItems rest)

def maxStepColumns : List (Option Nat × Array Block) → Nat
  | [] => 1
  | (_, body) :: rest => max (maxStepBlockList body.toList) (maxStepColumns rest)

def maxStepAlgLines : List AlgLine → Nat
  | [] => 1
  | l :: rest =>
    max (max (maxStepInlineList l.content.toList)
      (match l.comment with
       | some c => maxStepInlineList c.toList
       | none => 1))
      (maxStepAlgLines rest)

def maxStepInlines (xs : Array Inline) : Nat := maxStepInlineList xs.toList

def maxStepInlineList : List Inline → Nat
  | [] => 1
  | x :: rest => max (maxStepInline x) (maxStepInlineList rest)

def maxStepInline : Inline → Nat
  | .styled _ body => maxStepInlineList body.toList
  | .colored _ _ body => maxStepInlineList body.toList
  | .role _ body => maxStepInlineList body.toList
  | .link _ body => maxStepInlineList body.toList
  | .underline body => maxStepInlineList body.toList
  | .footnote _ body => maxStepInlineList body.toList
  | .step n last body => max (max n (last.getD n)) (maxStepInlineList body.toList)
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _
  | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _ | .cite _ _ => 1

end

/-- The handout pages one top-level block owes: one per overlay step of a
frame, none for anything else. A frame projection, not a measure walk —
only a frame opens handout duplicates, whatever block kinds arrive later —
and the `frames_sections` census (deckStepChecks) holds it to the shipped
page count. The page-count obligation (`pages_count_frame_steps`,
Obligations.lean) states its theorem over this def. -/
def frameSteps (b : Block) : Nat :=
  if let .frame _ _ _ body := b then max 1 (maxStepBlocks body) else 0

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
grey. Runs with no colour of their own take `cover.plain`; verbatim dims
through its own `covered` field; section blocks carry no colour and stay
(recorded in PLAN). Only colours change in either mode, so no step can
reflow the slide — the cover-not-hide invariant, by construction. -/
def dimBlockList (cover : Cover) (k : Nat) (pending : Bool) (out : Array Block) :
    List Block → Array Block
  | [] => out
  | b :: rest =>
    dimBlockList cover k pending (out.push (dimBlock cover k pending b)) rest

def dimBlock (cover : Cover) (k : Nat) (pending : Bool) : Block → Block
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
  | .ragged body => .ragged (dimBlockList cover k pending #[] body.toList)
  | .quote body => .quote (dimBlockList cover k pending #[] body.toList)
  | .abstract body => .abstract (dimBlockList cover k pending #[] body.toList)
  | .titled kind title body =>
    .titled kind
      (if pending then
        if title.isEmpty then title
        else #[.colored cover.plain none (dimInlineList cover k true #[] title.toList)]
       else dimInlineList cover k false #[] title.toList)
      (dimBlockList cover k pending #[] body.toList)
  | .role n body => .role n (dimBlockList cover k pending #[] body.toList)
  | .spaced g body => .spaced g (dimBlockList cover k pending #[] body.toList)
  | .columns cols => .columns (dimColumns cover k pending #[] cols.toList)
  -- The mode flip: a pending step's body covers, and inside a cover a
  -- nested step stays covered — `\uncover<2>` covers on 1 and again from 3,
  -- exactly as beamer's transparent covering does.
  | .step n last body =>
    .step n last (dimBlockList cover k (pending || stepPending n last k) #[] body.toList)
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
  | .frame t st v body => .frame t st v body
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
  | .table cols pl pr rows rules =>
    .table cols pl pr (dimTableRows cover k pending #[] rows.toList) rules
  | .float fk num ca body caption =>
    .float fk num ca (dimBlockList cover k pending #[] body.toList)
      (if pending then
        if caption.isEmpty then caption
        else #[.colored cover.plain none (dimInlineList cover k true #[] caption.toList)]
       else dimInlineList cover k false #[] caption.toList)
  -- A reference list is furniture, like a section title: the dim walk
  -- keeps it whole (the `.section` decision, recorded in PLAN).
  | .bibliography src style items => .bibliography src style items

def dimTableRows (cover : Cover) (k : Nat) (pending : Bool)
    (out : Array (Array (Array Inline))) :
    List (Array (Array Inline)) → Array (Array (Array Inline))
  | [] => out
  | row :: rest =>
    dimTableRows cover k pending (out.push (dimTableCells cover k pending #[] row.toList)) rest

def dimTableCells (cover : Cover) (k : Nat) (pending : Bool)
    (out : Array (Array Inline)) :
    List (Array Inline) → Array (Array Inline)
  | [] => out
  | cell :: rest =>
    dimTableCells cover k pending (out.push
      (if pending then
        if cell.isEmpty then cell
        else #[.colored cover.plain none (dimInlineList cover k true #[] cell.toList)]
       else dimInlineList cover k false #[] cell.toList)) rest

def dimItems (cover : Cover) (k : Nat) (pending : Bool) (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest =>
    dimItems cover k pending (out.push (dimBlockList cover k pending #[] item.toList)) rest

def dimColumns (cover : Cover) (k : Nat) (pending : Bool)
    (out : Array (Option Nat × Array Block)) :
    List (Option Nat × Array Block) → Array (Option Nat × Array Block)
  | [] => out
  | (w, body) :: rest =>
    dimColumns cover k pending (out.push (w, dimBlockList cover k pending #[] body.toList)) rest

def dimAlgLines (cover : Cover) (k : Nat) (pending : Bool) (out : Array AlgLine) :
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

def dimInlineList (cover : Cover) (k : Nat) (pending : Bool) (out : Array Inline) :
    List Inline → Array Inline
  | [] => out
  | x :: rest =>
    dimInlineList cover k pending (out.push (dimInline cover k pending x)) rest

def dimInline (cover : Cover) (k : Nat) (pending : Bool) : Inline → Inline
  | .styled st body => .styled st (dimInlineList cover k pending #[] body.toList)
  | .colored c nm body =>
    if pending then .colored (cover.of c) none (dimInlineList cover k true #[] body.toList)
    else .colored c nm (dimInlineList cover k false #[] body.toList)
  -- a role is a name, not ink: the cover dims what is inside it
  | .role n body => .role n (dimInlineList cover k pending #[] body.toList)
  | .link u body => .link u (dimInlineList cover k pending #[] body.toList)
  | .underline body => .underline (dimInlineList cover k pending #[] body.toList)
  -- The inline flip wraps: a covered paragraph's plain cover comes from its
  -- block wrapper, but a pending inline step must bring its own.
  | .step n last body =>
    if !pending && stepPending n last k then
      .step n last #[.colored cover.plain none (dimInlineList cover k true #[] body.toList)]
    else .step n last (dimInlineList cover k pending #[] body.toList)
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
  | .strut h => .strut h
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
def dimBlocks (cover : Cover) (k : Nat) (xs : Array Block) : Array Block :=
  dimBlockList cover k false #[] xs.toList

/-- The item flatten itself: a leading `.step` wrapper opens into its item,
the body standing where the wrapper stood. Named so its text conservation
is one lemma, not a case buried inside the walk. -/
def flattenLeadStep (item : Array Block) : Array Block :=
  match item[0]? with
  | some (Block.step _ _ body) => body ++ item.extract 1 item.size
  | _ => item

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
  | .ragged body => .ragged (unwrapItemStepList #[] body.toList)
  | .quote body => .quote (unwrapItemStepList #[] body.toList)
  | .abstract body => .abstract (unwrapItemStepList #[] body.toList)
  | .titled kind title body => .titled kind title (unwrapItemStepList #[] body.toList)
  | .role n body => .role n (unwrapItemStepList #[] body.toList)
  | .spaced g body => .spaced g (unwrapItemStepList #[] body.toList)
  | .columns cols => .columns (unwrapItemStepCols #[] cols.toList)
  | .step n l body => .step n l (unwrapItemStepList #[] body.toList)
  | .only targets body => .only targets (unwrapItemStepList #[] body.toList)
  | .nav spec body => .nav spec (unwrapItemStepList #[] body.toList)
  | .frame t s v body => .frame t s v (unwrapItemStepList #[] body.toList)
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
  | .table cols pl pr rows rules => .table cols pl pr rows rules
  | .float k n ca body caption => .float k n ca (unwrapItemStepList #[] body.toList) caption
  -- A reference list holds entries, never item paragraphs.
  | .bibliography src style items => .bibliography src style items

def unwrapItemStepItems (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest =>
    unwrapItemStepItems
      (out.push (flattenLeadStep (unwrapItemStepList #[] item.toList))) rest

def unwrapItemStepCols (out : Array (Option Nat × Array Block)) :
    List (Option Nat × Array Block) → Array (Option Nat × Array Block)
  | [] => out
  | (w, body) :: rest =>
    unwrapItemStepCols (out.push (w, unwrapItemStepList #[] body.toList)) rest

end

/-- The conservation shape, named once: `f` leaves the census fixed. Every
public IR-to-IR walk states its conservation as an instance of this — one
shape, many instances — so an instance is grep-recognisable and the
pre-commit hook can ask a new walk for one (or for the one-line refusal
naming why none holds). -/
def Conserves (census : α → β) (f : α → α) : Prop :=
  ∀ x, census (f x) = census x

/-- Body-transparent wraps, once: a constructor whose own census is exactly
its body's conserves the census when wrapped around any content.
`langWrap_text`, `footnoteWrap_text`, and `underline_text` are its
one-line instances (`rfl` per constructor), and the next wrapper's costs
the same line. -/
theorem wrap_text (w : Array Inline → Inline)
    (hw : ∀ xs, plainTextOne (w xs) = plainText xs) :
    Conserves plainText (fun xs => #[w xs]) := fun xs => by
  simp [plainText, plainTextList, hw]

/-- Wrap inline content in a language switch: what `\foreignlanguage`,
`\selectlanguage`, and `otherlanguage` become. -/
def langWrap (tag : String) (xs : Array Inline) : Array Inline :=
  #[.styled (.lang tag) xs]

/-- The language attribute is pure markup: tagging content ships exactly
the text census the content already had — `language_attribute_text_free`,
an instance of `wrap_text` because the census ignores style wrappers. -/
theorem langWrap_text (tag : String) :
    Conserves plainText (langWrap tag) :=
  wrap_text (.styled (.lang tag)) fun _ => rfl

/-- Wrap inline content as a footnote's body: what `\footnote` becomes. -/
def footnoteWrap (num : Option Nat) (xs : Array Inline) : Array Inline :=
  #[.footnote num xs]

/-- The note body is document text: marking content as a footnote ships
exactly the text census the content already had. The mark digit is
generated ink, excluded as `citeMark` is. -/
theorem footnoteWrap_text (num : Option Nat) :
    Conserves plainText (footnoteWrap num) :=
  wrap_text (.footnote num) fun _ => rfl

-- Nothing vanishes: dimming recolours, never removes. The text of a frame's
-- body is identical on every handout page, so the union of what the steps
-- show is the whole content — each page already shows all of it, dimmed or
-- not. Stated over the walks above and proved by the same structural
-- recursion; a step function that dropped or reordered content would fail
-- these equalities.

/-- A listing caption's census text: the declared characters, `""` when
none is declared. The number prefix is backend furniture, excluded as a
float's `captionPrefix` is. -/
def ListingSpec.capText (spec : ListingSpec) : String :=
  match spec.caption with
  | some (_, cap) => plainText cap
  | none => ""

/-- The algorithm lines' census: each line's declared content, then its
comment — the keywords a kind implies are generated by the backends
(`AlgLine.rendered`) and never counted, exactly as caption prefixes are
not (`algorithm_text` is the statement). -/
def algLineText (acc : String) : List AlgLine → String
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
def blocksText (xs : Array Block) : String := blockTextList "" xs.toList

def blockTextList (acc : String) : List Block → String
  | [] => acc
  | b :: rest => blockTextList (blockTextOne acc b) rest

def blockTextOne (acc : String) : Block → String
  | .para content =>
    let t := plainText content
    acc ++ t
  -- an equation's number ships beside its formula in every backend
  | .equation number content =>
    let t := plainText content
    acc ++ t ++ number
  | .section _ _ _ title =>
    let t := plainText title
    acc ++ t
  | .list _ items => blockTextItems acc items.toList
  | .center body => blockTextList acc body.toList
  | .ragged body => blockTextList acc body.toList
  -- A quotation's text is real census content, exactly as a paragraph's.
  | .quote body => blockTextList acc body.toList
  | .abstract body => blockTextList acc body.toList
  -- The title counts with its block, before the body, as a frame's does;
  -- the bar and background are decorative ink and ship no characters.
  | .titled _ title body => blockTextList (acc ++ plainText title) body.toList
  | .role _ body => blockTextList acc body.toList
  | .spaced _ body => blockTextList acc body.toList
  | .columns cols => blockTextColumns acc cols.toList
  | .step _ _ body => blockTextList acc body.toList
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
  | .frame title _ _ body => blockTextList (acc ++ plainText title) body.toList
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
  | .table _ _ _ rows _ => blockTextTableRows acc rows.toList
  | .float _ _ _ body caption => blockTextList (acc ++ plainText caption) body.toList
  -- Every entry's text is census content, in list order.
  | .bibliography _ _ items => blockTextBibItems acc items.toList

def blockTextBibItems (acc : String) : List BibItem → String
  | [] => acc
  | item :: rest => blockTextBibItems (acc ++ plainText item.content) rest

def blockTextTableRows (acc : String) : List (Array (Array Inline)) → String
  | [] => acc
  | row :: rest => blockTextTableRows (blockTextTableCells acc row.toList) rest

def blockTextTableCells (acc : String) : List (Array Inline) → String
  | [] => acc
  | cell :: rest => blockTextTableCells (acc ++ plainText cell) rest

def blockTextItems (acc : String) : List (Array Block) → String
  | [] => acc
  | item :: rest => blockTextItems (blockTextList acc item.toList) rest

def blockTextColumns (acc : String) : List (Option Nat × Array Block) → String
  | [] => acc
  | (_, body) :: rest => blockTextColumns (blockTextList acc body.toList) rest

end

theorem blockTextList_append (a b : List Block) (acc : String) :
    blockTextList acc (a ++ b) = blockTextList (blockTextList acc a) b := by
  induction a generalizing acc with
  | nil => simp [blockTextList]
  | cons x xs ih => simp [blockTextList, ih]

/-- Blocks are content-free furniture: a titled block's census is its
title's text then its body's, onto whatever came before — the bar and the
background ship no characters. Definitional (`rfl`), the frame arm's own
shape, so an edit that made the furniture ship text fails this build. -/
theorem titled_text (acc : String) (kind : TitledKind) (title : Array Inline)
    (body : Array Block) :
    blockTextOne acc (.titled kind title body)
      = blockTextList (acc ++ plainText title) body.toList := rfl

/-- A declared vertical skip standing on its own, as `\vskip` does: glue
the next placed line pays, no content. -/
private def gapBlock (g : Dim.SymGlue) : Block := .spaced g #[]

/-- A declared bar with the skips beside it; no declared weight, no ink. -/
private def barSide (ink : Color × Option String)
    (before after : Dim.SymGlue) : Option Dim.SymGlue → Array Block
  | some w => #[gapBlock before, .rule ink.1 ink.2 w, gapBlock after]
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
def titleBarsList (st : ElementStyle) (ink : Color × Option String)
    (out : Array Block) (done : Bool) : List Block → Array Block
  | [] => out
  | b :: rest =>
    match b, done with
    | .section 0 starred num title, false =>
      titleBarsList st ink (titleStep st ink out starred num title) true rest
    | b, _ => titleBarsList st ink (out.push b) done rest

def titleBars (st : ElementStyle) (ink : Color × Option String)
    (blocks : Array Block) : Array Block :=
  if st.ruleAbove.isNone && st.ruleBelow.isNone then blocks
  else titleBarsList st ink #[] false blocks.toList

private theorem blocksText_push (out : Array Block) (b : Block) :
    blocksText (out.push b) = blockTextOne (blocksText out) b := by
  simp [blocksText, Array.toList_push, blockTextList_append, blockTextList]

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
theorem titleBars_text (st : ElementStyle) (ink : Color × Option String) :
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
def headingLevels (xs : Array Block) : Array Nat := headingLevelList #[] xs.toList

def headingLevelList (out : Array Nat) : List Block → Array Nat
  | [] => out
  | b :: rest => headingLevelList (headingLevelOne out b) rest

def headingLevelOne (out : Array Nat) : Block → Array Nat
  | .section level _ _ _ => out.push level
  | .para _ => out
  | .equation _ _ => out
  | .list _ items => headingLevelItems out items.toList
  | .center body => headingLevelList out body.toList
  | .ragged body => headingLevelList out body.toList
  | .quote body => headingLevelList out body.toList
  | .abstract body => headingLevelList out body.toList
  | .titled _ _ body => headingLevelList out body.toList
  | .role _ body => headingLevelList out body.toList
  | .spaced _ body => headingLevelList out body.toList
  | .columns cols => headingLevelColumns out cols.toList
  | .step _ _ body => headingLevelList out body.toList
  | .only _ body => headingLevelList out body.toList
  | .nav _ body => headingLevelList out body.toList
  | .frame _ _ _ body => headingLevelList out body.toList
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
  | .table _ _ _ _ _ => out
  | .float _ _ _ body _ => headingLevelList out body.toList
  -- The References heading is its own .section block; the list holds none.
  | .bibliography _ _ _ => out

def headingLevelItems (out : Array Nat) : List (Array Block) → Array Nat
  | [] => out
  | item :: rest => headingLevelItems (headingLevelList out item.toList) rest

def headingLevelColumns (out : Array Nat) : List (Option Nat × Array Block) → Array Nat
  | [] => out
  | (_, body) :: rest => headingLevelColumns (headingLevelList out body.toList) rest

end

mutual

/-- Every footnote in document order, with its resolved mark number: the
one flow the backends' endnote sections read (the HTML `doc-endnotes`
section, the markdown `[^k]` definitions). The accumulator threads
through, as every walk here does. -/
-- conserves: none — a projection of the notes alone: nothing is rewritten,
-- and the census the notes owe is `footnoteWrap_text` at the wrap site.
def footnotesOf (xs : Array Block) : Array (Option Nat × Array Inline) :=
  footnoteBlockList #[] xs.toList

def footnoteBlockList (out : Array (Option Nat × Array Inline)) :
    List Block → Array (Option Nat × Array Inline)
  | [] => out
  | b :: rest => footnoteBlockList (footnoteBlockOne out b) rest

def footnoteBlockOne (out : Array (Option Nat × Array Inline)) :
    Block → Array (Option Nat × Array Inline)
  | .para content => footnoteInlineList out content.toList
  | .equation _ content => footnoteInlineList out content.toList
  | .section _ _ _ title => footnoteInlineList out title.toList
  | .list _ items => footnoteItems out items.toList
  | .center body => footnoteBlockList out body.toList
  | .ragged body => footnoteBlockList out body.toList
  | .quote body => footnoteBlockList out body.toList
  | .abstract body => footnoteBlockList out body.toList
  | .titled _ title body =>
    footnoteBlockList (footnoteInlineList out title.toList) body.toList
  | .role _ body => footnoteBlockList out body.toList
  | .spaced _ body => footnoteBlockList out body.toList
  | .columns cols => footnoteColumns out cols.toList
  | .step _ _ body => footnoteBlockList out body.toList
  | .only _ body => footnoteBlockList out body.toList
  | .nav _ body => footnoteBlockList out body.toList
  | .frame title _ _ body =>
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
  | .table _ _ _ rows _ => footnoteTableRows out rows.toList
  | .algorithm _ _ lines => footnoteAlgLines out lines.toList
  -- the caption counts with its float, before the body, as its text does
  | .float _ _ _ body caption =>
    footnoteBlockList (footnoteInlineList out caption.toList) body.toList
  | .bibliography _ _ _ => out

def footnoteTableRows (out : Array (Option Nat × Array Inline)) :
    List (Array (Array Inline)) → Array (Option Nat × Array Inline)
  | [] => out
  | row :: rest => footnoteTableRows (footnoteTableCells out row.toList) rest

def footnoteTableCells (out : Array (Option Nat × Array Inline)) :
    List (Array Inline) → Array (Option Nat × Array Inline)
  | [] => out
  | cell :: rest => footnoteTableCells (footnoteInlineList out cell.toList) rest

def footnoteItems (out : Array (Option Nat × Array Inline)) :
    List (Array Block) → Array (Option Nat × Array Inline)
  | [] => out
  | item :: rest => footnoteItems (footnoteBlockList out item.toList) rest

def footnoteColumns (out : Array (Option Nat × Array Inline)) :
    List (Option Nat × Array Block) → Array (Option Nat × Array Inline)
  | [] => out
  | (_, body) :: rest => footnoteColumns (footnoteBlockList out body.toList) rest

def footnoteAlgLines (out : Array (Option Nat × Array Inline)) :
    List AlgLine → Array (Option Nat × Array Inline)
  | [] => out
  | l :: rest =>
    footnoteAlgLines (match l.comment with
      | some c => footnoteInlineList (footnoteInlineList out l.content.toList) c.toList
      | none => footnoteInlineList out l.content.toList) rest

def footnoteInlineList (out : Array (Option Nat × Array Inline)) :
    List Inline → Array (Option Nat × Array Inline)
  | [] => out
  | x :: rest => footnoteInlineList (footnoteInlineOne out x) rest

def footnoteInlineOne (out : Array (Option Nat × Array Inline)) :
    Inline → Array (Option Nat × Array Inline)
  | .footnote num body =>
    -- flow order: a note nested in another note's body follows its host
    footnoteInlineList (out.push (num, body)) body.toList
  | .styled _ body => footnoteInlineList out body.toList
  | .colored _ _ body => footnoteInlineList out body.toList
  | .role _ body => footnoteInlineList out body.toList
  | .link _ body => footnoteInlineList out body.toList
  | .underline body => footnoteInlineList out body.toList
  | .step _ _ body => footnoteInlineList out body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _ => out

end

/-- A heading level in the author's own vocabulary. -/
private def levelName : Nat → String
  | 0 => "the title"
  | 1 => "'\\section'"
  | 2 => "'\\subsection'"
  | _ => "'\\subsubsection'"

/-- The broken-outline diagnostic W0320 fires: named so the completeness
theorem below can point at the pushed value's code. -/
private def outlineGapDiag (p l : Nat) : Diag :=
  Diag.of .W0320
    s!"heading levels skip a step: {levelName p} is followed by {levelName l}"
    (help := some "descend one level at a time — here \\subsection \
(HTML §4.3.11, WCAG G141); \
a screen reader reads the gap as a broken outline")

/-- The heading rank a section level takes, the one outline fact every
text backend projects: level 0 is the document title, rank 1 — `h1` is
"for a top-level section" (HTML §4.3.6), `#` its markdown twin — and each
deeper level takes the next rank, capped at 4, the deepest level the
elaborator produces plus one. An IR outline without gaps (`outlineWalk`'s
judgement, below) therefore ships as a page outline without gaps (HTML
§4.3.11's conformance rule); `heading_renderings_agree` in Tests states
each backend's projection. -/
def headingRank (level : Nat) : Nat :=
  min (level + 1) 4

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
def outlineWalk (prev : Nat) (gapNamed titleNamed : Bool)
    (out : Array Diag) : List Nat → Array Diag
  | [] => out
  | l :: rest =>
    if l > prev + 1 && !gapNamed then
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
def outlineSkips (prev : Nat) : List Nat → Bool
  | [] => false
  | l :: rest => l > prev + 1 || outlineSkips l rest

/-- The document's outline skips a level: the fact W0320 exists to name
(HTML §4.3.11; WCAG technique G141). -/
def outlineHasSkip (doc : Doc) : Bool :=
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
def outlineDiags (doc : Doc) : Array Diag :=
  match (headingLevels doc.body).toList with
  | [] => #[]
  | l :: rest => outlineWalk l false false #[] rest

/-- A diagnostic already collected survives the rest of the walk. -/
private theorem outlineWalk_mem (d : Diag) :
    ∀ (ls : List Nat) (prev : Nat) (gN tN : Bool) (out : Array Diag),
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
    ∀ (ls : List Nat) (prev : Nat) (tN : Bool) (out : Array Diag),
      outlineSkips prev ls = true →
      ∃ d ∈ outlineWalk prev false tN out ls, d.code = "W0320"
  | l :: rest, prev, tN, out, hskip => by
    unfold outlineWalk
    by_cases hgap : l > prev + 1
    · refine ⟨outlineGapDiag prev l, ?_, by
        show DiagCode.code .W0320 = "W0320"
        decide +kernel⟩
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
theorem headings_no_skip_judged (doc : Doc)
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
def isPhysicalPage : Inline → Bool
  | .pageNumber => true
  | .pageCount => true
  | _ => false

/-- Does this inline content carry a physical-page placeholder anywhere?
`anyInline` over the one leaf predicate. -/
def hasPhysicalPage (xs : Array Inline) : Bool :=
  anyInline isPhysicalPage xs

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
theorem frame_sequence_carries_no_physical (s : ChromeSlot)
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

private theorem blockTextColumns_chain (l1 l2 : List (Option Nat × Array Block))
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

theorem dimInlineList_text (cover : Cover) (k : Nat) (pending : Bool)
    (xs : List Inline) (out : Array Inline) :
    plainTextList (dimInlineList cover k pending out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [dimInlineList, plainTextList]
  | x :: rest =>
    rw [dimInlineList, dimInlineList_text cover k pending rest]
    simp [plainTextList, plainTextList_append, dimInline_text cover k pending x,
      String.append_assoc]

theorem dimInline_text (cover : Cover) (k : Nat) (pending : Bool) (x : Inline) :
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
  | .role n body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k pending body.toList #[], plainTextList]
  | .link u body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k pending body.toList #[], plainTextList]
  | .underline body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text cover k pending body.toList #[], plainTextList]
  | .step n last body =>
    rw [dimInline]
    by_cases h : (!pending && stepPending n last k) = true
    · simp [h, plainTextOne, plainTextList,
        dimInlineList_text cover k true body.toList #[]]
    · simp [h, plainTextOne, dimInlineList_text cover k pending body.toList #[],
        plainTextList]
  | .image _ _ _ =>
    -- the walk leaves an image node whole (raster content dims in the
    -- backends' hands), and its text census is empty either way
    rfl
  | .formula _ _ _ =>
    -- the walk leaves a formula node whole (a pending formula dims in the
    -- backends' hands); its census is its source, untouched on both sides
    rfl
  | .text _ | .math _ _ | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _
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
theorem dimTableCells_text (cover : Cover) (k : Nat) (pending : Bool)
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

theorem dimTableRows_text (cover : Cover) (k : Nat) (pending : Bool)
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

theorem dimBlockList_text (cover : Cover) (k : Nat) (pending : Bool)
    (xs : List Block) (out : Array Block) (acc : String) :
    blockTextList acc (dimBlockList cover k pending out xs).toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [dimBlockList, blockTextList]
  | b :: rest =>
    rw [dimBlockList, dimBlockList_text cover k pending rest]
    simp [blockTextList, blockTextList_chain, dimBlock_text cover k pending b]

theorem dimBlock_text (cover : Cover) (k : Nat) (pending : Bool) (b : Block)
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
  | .ragged body =>
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
    by_cases h : pending = true
    · by_cases ht : title.isEmpty
      · simp [h, ht, blockTextOne,
          dimBlockList_text cover k true body.toList #[] _, blockTextList]
      · simp [h, ht, blockTextOne, plainText, plainTextList, plainTextOne,
          dimInlineList_text cover k true title.toList #[],
          dimBlockList_text cover k true body.toList #[] _, blockTextList]
    · simp [h, blockTextOne, plainText,
        dimInlineList_text cover k false title.toList #[], plainTextList,
        dimBlockList_text cover k false body.toList #[] _, blockTextList]
  | .role n body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending body.toList #[] acc, blockTextList]
  | .spaced g body =>
    rw [dimBlock]
    simp [blockTextOne, dimBlockList_text cover k pending body.toList #[] acc, blockTextList]
  | .columns cols =>
    rw [dimBlock]
    simp [blockTextOne, dimColumns_text cover k pending cols.toList #[] acc, blockTextColumns]
  | .step n last body =>
    -- No case split: the mode flip is just the argument the recursion takes.
    rw [dimBlock]
    simp [blockTextOne,
      dimBlockList_text cover k (pending || stepPending n last k) body.toList #[] acc,
      blockTextList]
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
  | .section _ _ _ _ | .note _ | .frame _ _ _ _ | .framefoot _
  | .setPalette _ | .setTokens _
  | .rule _ _ _ | .picture _ | .pagebreak | .bibliography _ _ _ => rfl
  | .algorithm n sm lines =>
    rw [dimBlock]
    show algLineText acc (dimAlgLines cover k pending #[] lines.toList).toList = _
    rw [dimAlgLines_text cover k pending lines.toList #[] acc]
    rfl
  | .table cols pl pr rows rules =>
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

theorem dimItems_text (cover : Cover) (k : Nat) (pending : Bool)
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

theorem dimColumns_text (cover : Cover) (k : Nat) (pending : Bool)
    (cols : List (Option Nat × Array Block))
    (out : Array (Option Nat × Array Block)) (acc : String) :
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
theorem dimBlocks_text (cover : Cover) (k : Nat) :
    Conserves blocksText (dimBlocks cover k) := fun xs => by
  simp [blocksText, dimBlocks, dimBlockList_text cover k false xs.toList #[] "",
    blockTextList]

/-- `algorithm_text`: the algorithm block's census is exactly its lines'
declared content and comments — display flags are settings and the
keywords a kind implies are generated by the backends (`AlgLine.rendered`),
so neither is ever counted, exactly as caption prefixes are not. -/
theorem algorithm_text (numbered semis : Bool) (lines : Array AlgLine) :
    blocksText #[Block.algorithm numbered semis lines]
      = algLineText "" lines.toList := rfl

-- The item-step flatten: unwrapping loses no text. A leading `\item<2->`
-- wrapper opens into its item, nothing recoloured, nothing reordered, so
-- the block census is fixed. Same accumulator-lemma-then-mutual-induction
-- shape as the dim walk above.

private theorem flattenLeadStep_text (item : Array Block) (acc : String) :
    blockTextList acc (flattenLeadStep item).toList
      = blockTextList acc item.toList := by
  unfold flattenLeadStep
  split
  next n l body h =>
    have h0 : item.toList[0]? = some (Block.step n l body) := by simpa using h
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
      simp [wl, hlen, blockTextList, blockTextList_chain, blockTextOne]
  next => rfl

mutual

theorem unwrapItemStepList_text (xs : List Block) (out : Array Block)
    (acc : String) :
    blockTextList acc (unwrapItemStepList out xs).toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [unwrapItemStepList, blockTextList]
  | b :: rest =>
    rw [unwrapItemStepList, unwrapItemStepList_text rest]
    simp [blockTextList, blockTextList_chain, unwrapItemStep_text b]

theorem unwrapItemStep_text (b : Block) (acc : String) :
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
  | .ragged body =>
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
  | .spaced g body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .columns cols =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepCols_text cols.toList #[] acc,
      blockTextColumns]
  | .step n l body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .only targets body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .nav spec body =>
    rw [unwrapItemStep]
    simp [blockTextOne, unwrapItemStepList_text body.toList #[] acc,
      blockTextList]
  | .frame t s v body =>
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
  | .logo _ | .rule _ _ _ | .picture _ | .table _ _ _ _ _
  | .bibliography _ _ _ => rfl

theorem unwrapItemStepItems_text (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (unwrapItemStepItems out items).toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [unwrapItemStepItems, blockTextItems]
  | item :: rest =>
    rw [unwrapItemStepItems, unwrapItemStepItems_text rest]
    simp [blockTextItems, blockTextItems_chain, flattenLeadStep_text,
      unwrapItemStepList_text item.toList #[], blockTextList]

theorem unwrapItemStepCols_text (cols : List (Option Nat × Array Block))
    (out : Array (Option Nat × Array Block)) (acc : String) :
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
theorem unwrapItemSteps_text : Conserves blocksText unwrapItemSteps := fun xs => by
  simp [blocksText, unwrapItemSteps, unwrapItemStepList_text xs.toList #[] "",
    blockTextList]

/-- An underline is a drawn decoration, never content: the text census
reads straight through the wrap, so `\underline` can neither add nor hide
a character — the conservation half of the underline convention (its
rules ride a sibling line; `underline_no_growth` in Layout is the metric
half). -/
theorem underline_text : Conserves plainText (fun xs => #[Inline.underline xs]) :=
  wrap_text .underline fun _ => rfl

-- Float numbering conserves the census: the pass writes the `num` field
-- and nothing else, so no caption and no body content moves. Same
-- accumulator-lemma-then-mutual-induction shape as the walks above.

mutual

theorem numberFloatList_text (c : FloatCtr) (acc : Array Block)
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

theorem numberFloatOne_text (c : FloatCtr) (b : Block) (s : String) :
    blockTextOne s (numberFloatOne c b).2 = blockTextOne s b := by
  match b with
  | .para _ | .equation _ _ | .section _ _ _ _ | .note _ | .verbatim _ _ _ | .logo _
  | .bibliography _ _ _ | .algorithm _ _ _
  | .framefoot _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .table _ _ _ _ _ => rfl
  | .list o items =>
    simp [numberFloatOne, blockTextOne,
      numberFloatItems_text c #[] items.toList, blockTextItems]
  | .center body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .ragged body =>
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
  | .spaced _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .columns cols =>
    simp [numberFloatOne, blockTextOne,
      numberFloatCols_text c #[] cols.toList, blockTextColumns]
  | .step _ _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .only _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .nav _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .frame _ _ _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .float kind _ capAbove body caption =>
    simp [numberFloatOne, blockTextOne, numberFloatList_text, blockTextList]

theorem numberFloatItems_text (c : FloatCtr) (acc : Array (Array Block))
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

theorem numberFloatCols_text (c : FloatCtr)
    (acc : Array (Option Nat × Array Block))
    (cols : List (Option Nat × Array Block)) (s : String) :
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
theorem numberFloats_text : Conserves blocksText numberFloats := fun xs => by
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
abbrev RoleRecolor := Palette → Option Color → Option String → Color → Color

mutual

def recolorRolesList (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) (ground : Option Color) (out : Array Block) :
    List Block → Array Block × Palette
  | [] => (out, pal)
  | b :: rest =>
    let r := recolorRolesBlock repal recolor pal ground b
    recolorRolesList repal recolor r.2 ground (out.push r.1) rest

def recolorRolesBlock (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) (ground : Option Color) : Block → Block × Palette
  | .para content =>
    (.para (recolorRolesInlines recolor pal ground #[] content.toList), pal)
  | .equation num content =>
    (.equation num (recolorRolesInlines recolor pal ground #[] content.toList), pal)
  -- A heading's title is judged on the page wherever it stands (the
  -- judge's headingCx carries no local ground); the walk mirrors it.
  | .section l st num title =>
    (.section l st num (recolorRolesInlines recolor pal none #[] title.toList), pal)
  | .list o items =>
    let r := recolorRolesItems repal recolor pal ground #[] items.toList
    (.list o r.1, r.2)
  | .center body =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    (.center r.1, r.2)
  | .ragged body =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    (.ragged r.1, r.2)
  | .quote body =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    (.quote r.1, r.2)
  | .abstract body =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    (.abstract r.1, r.2)
  -- The title sits on the bar when the palette in force declares one, on
  -- the page otherwise (`titledLook`, the one resolving site — the same
  -- ground the judge reads); the body keeps the enclosing ground.
  | .titled kind title body =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    (.titled kind
      (recolorRolesInlines recolor pal (titledLook pal kind).bar #[] title.toList)
      r.1, r.2)
  | .role n body =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    (.role n r.1, r.2)
  | .spaced g body =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    (.spaced g r.1, r.2)
  | .columns cols =>
    let r := recolorRolesColumns repal recolor pal ground #[] cols.toList
    (.columns r.1, r.2)
  | .step n last body =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    (.step n last r.1, r.2)
  | .only targets body =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    (.only targets r.1, r.2)
  | .nav spec body =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    (.nav spec r.1, r.2)
  -- The title sits on the frame-title bar when the palette in force
  -- declares one; a standout frame's body sits on the inversion — the
  -- grounds the judge reads, at the palette in force at the frame.
  | .frame title standout valign body =>
    let bodyGround := if standout then
        some ((pal.find? "standoutbg").getD ((pal.find? "fg").getD Color.black))
      else ground
    let r := recolorRolesList repal recolor pal bodyGround #[] body.toList
    (.frame (recolorRolesInlines recolor pal (pal.find? "frametitlebg") #[] title.toList)
      standout valign r.1, r.2)
  | .framefoot content =>
    (.framefoot (recolorRolesInlines recolor pal ground #[] content.toList), pal)
  -- The epoch boundary: the palette is rewritten where it stands, and the
  -- walk's context switches to the declared (pre-rewrite) state, the one
  -- the judge keyed its plan by.
  | .setPalette p => (.setPalette (repal p), p)
  | .setTokens tk => (.setTokens tk, pal)
  | .pagebreak => (.pagebreak, pal)
  -- A note is a side channel, verbatim and pictures carry no role-named
  -- runs, a logo is furniture, a rule is decorative ink: the judge reads
  -- none of them, so the walk leaves each whole.
  | .note body => (.note body, pal)
  | .verbatim c s sp => (.verbatim c s sp, pal)
  -- Lines are judged where they stand (`Contrast.usesBlock` descends into
  -- content and comment), so the realizer rewrites exactly there.
  | .algorithm n sm lines =>
    (.algorithm n sm (recolorRolesAlgLines recolor pal ground #[] lines.toList), pal)
  | .logo content => (.logo content, pal)
  | .rule c nm th => (.rule c nm th, pal)
  | .picture p => (.picture p, pal)
  | .table cols pl pr rows rules =>
    (.table cols pl pr (recolorRolesTableRows recolor pal ground #[] rows.toList) rules, pal)
  | .float fk num ca body caption =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    (.float fk num ca r.1
      (recolorRolesInlines recolor pal ground #[] caption.toList), r.2)
  | .bibliography src style items =>
    (.bibliography src style
      (recolorRolesBibItems recolor pal ground #[] items.toList), pal)

def recolorRolesItems (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) (ground : Option Color) (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block) × Palette
  | [] => (out, pal)
  | item :: rest =>
    let r := recolorRolesList repal recolor pal ground #[] item.toList
    recolorRolesItems repal recolor r.2 ground (out.push r.1) rest

def recolorRolesColumns (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) (ground : Option Color)
    (out : Array (Option Nat × Array Block)) :
    List (Option Nat × Array Block) → Array (Option Nat × Array Block) × Palette
  | [] => (out, pal)
  | (w, body) :: rest =>
    let r := recolorRolesList repal recolor pal ground #[] body.toList
    recolorRolesColumns repal recolor r.2 ground (out.push (w, r.1)) rest

def recolorRolesTableRows (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (out : Array (Array (Array Inline))) :
    List (Array (Array Inline)) → Array (Array (Array Inline))
  | [] => out
  | row :: rest =>
    recolorRolesTableRows recolor pal ground
      (out.push (recolorRolesTableCells recolor pal ground #[] row.toList)) rest

def recolorRolesTableCells (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (out : Array (Array Inline)) :
    List (Array Inline) → Array (Array Inline)
  | [] => out
  | cell :: rest =>
    recolorRolesTableCells recolor pal ground
      (out.push (recolorRolesInlines recolor pal ground #[] cell.toList)) rest

def recolorRolesBibItems (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (out : Array BibItem) :
    List BibItem → Array BibItem
  | [] => out
  | item :: rest =>
    recolorRolesBibItems recolor pal ground
      (out.push { item with
        content := recolorRolesInlines recolor pal ground #[] item.content.toList }) rest

def recolorRolesAlgLines (recolor : RoleRecolor) (pal : Palette)
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

def recolorRolesInlines (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (out : Array Inline) : List Inline → Array Inline
  | [] => out
  | x :: rest =>
    recolorRolesInlines recolor pal ground
      (out.push (recolorRolesInline recolor pal ground x)) rest

def recolorRolesInline (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) : Inline → Inline
  | .colored c nm body =>
    .colored (recolor pal ground nm c) nm
      (recolorRolesInlines recolor pal ground #[] body.toList)
  | .styled st body => .styled st (recolorRolesInlines recolor pal ground #[] body.toList)
  | .role n body => .role n (recolorRolesInlines recolor pal ground #[] body.toList)
  | .link u body => .link u (recolorRolesInlines recolor pal ground #[] body.toList)
  | .underline body => .underline (recolorRolesInlines recolor pal ground #[] body.toList)
  | .step n last body => .step n last (recolorRolesInlines recolor pal ground #[] body.toList)
  | .footnote n body => .footnote n (recolorRolesInlines recolor pal ground #[] body.toList)
  | .text s => .text s
  | .math d src => .math d src
  | .formula d src body => .formula d src body
  | .image src size alt => .image src size alt
  | .icon s l => .icon s l
  | .label k => .label k
  | .ref k p t tg => .ref k p t tg
  | .cite t keys => .cite t keys
  | .fill => .fill
  | .strut h => .strut h
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak e => .linebreak e

end

/-- The realization entry: the whole body walked once, page ground, the
document's own palette the opening epoch. -/
def recolorRoles (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) (xs : Array Block) : Array Block :=
  (recolorRolesList repal recolor pal none #[] xs.toList).1

private theorem blockTextBibItems_chain (l1 l2 : List BibItem) (acc : String) :
    blockTextBibItems acc (l1 ++ l2)
      = blockTextBibItems (blockTextBibItems acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextBibItems]
  | cons item rest ih => simp [blockTextBibItems, ih]

mutual

theorem recolorRolesInlines_text (recolor : RoleRecolor) (pal : Palette)
    (ground : Option Color) (xs : List Inline) (out : Array Inline) :
    plainTextList (recolorRolesInlines recolor pal ground out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [recolorRolesInlines, plainTextList]
  | x :: rest =>
    rw [recolorRolesInlines, recolorRolesInlines_text recolor pal ground rest]
    simp [plainTextList, plainTextList_append,
      recolorRolesInline_text recolor pal ground x, String.append_assoc]

theorem recolorRolesInline_text (recolor : RoleRecolor) (pal : Palette)
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
  | .role n body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .link u body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .underline body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .step n last body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .footnote n body =>
    rw [recolorRolesInline]
    simp [plainTextOne, recolorRolesInlines_text recolor pal ground body.toList #[],
      plainTextList]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .label _
  | .ref _ _ _ _ | .cite _ _ | .fill | .strut _ | .pageNumber | .pageCount
  | .linebreak _ => rfl

end

theorem recolorRolesTableCells_text (recolor : RoleRecolor) (pal : Palette)
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

theorem recolorRolesTableRows_text (recolor : RoleRecolor) (pal : Palette)
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

theorem recolorRolesBibItems_text (recolor : RoleRecolor) (pal : Palette)
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

theorem recolorRolesList_text (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) (ground : Option Color) (xs : List Block)
    (out : Array Block) (acc : String) :
    blockTextList acc (recolorRolesList repal recolor pal ground out xs).1.toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [recolorRolesList, blockTextList]
  | b :: rest =>
    rw [recolorRolesList,
      recolorRolesList_text repal recolor
        (recolorRolesBlock repal recolor pal ground b).2 ground rest]
    simp [blockTextList, blockTextList_chain,
      recolorRolesBlock_text repal recolor pal ground b]

theorem recolorRolesBlock_text (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) (ground : Option Color) (b : Block) (acc : String) :
    blockTextOne acc (recolorRolesBlock repal recolor pal ground b).1
      = blockTextOne acc b := by
  match b with
  | .para content =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor pal ground content.toList #[], plainTextList]
  | .equation num content =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor pal ground content.toList #[], plainTextList]
  | .section l st num title =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor pal none title.toList #[], plainTextList]
  | .list o items =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesItems_text repal recolor pal ground items.toList #[] acc,
      blockTextItems]
  | .center body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor pal ground body.toList #[] acc, blockTextList]
  | .ragged body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor pal ground body.toList #[] acc, blockTextList]
  | .quote body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor pal ground body.toList #[] acc, blockTextList]
  | .abstract body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor pal ground body.toList #[] acc, blockTextList]
  | .titled kind title body =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor pal (titledLook pal kind).bar title.toList #[],
      plainTextList,
      recolorRolesList_text repal recolor pal ground body.toList #[] _, blockTextList]
  | .role n body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor pal ground body.toList #[] acc, blockTextList]
  | .spaced g body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor pal ground body.toList #[] acc, blockTextList]
  | .columns cols =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesColumns_text repal recolor pal ground cols.toList #[] acc,
      blockTextColumns]
  | .step n last body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor pal ground body.toList #[] acc, blockTextList]
  | .only targets body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor pal ground body.toList #[] acc, blockTextList]
  | .nav spec body =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesList_text repal recolor pal ground body.toList #[] acc, blockTextList]
  | .frame title standout valign body =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor pal (pal.find? "frametitlebg") title.toList #[],
      plainTextList,
      recolorRolesList_text repal recolor pal
        (if standout then
          some ((pal.find? "standoutbg").getD ((pal.find? "fg").getD Color.black))
         else ground) body.toList #[] _,
      blockTextList]
  | .framefoot content =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor pal ground content.toList #[], plainTextList]
  | .setPalette _ | .setTokens _ | .pagebreak | .note _ | .verbatim _ _ _
  | .logo _ | .rule _ _ _ | .picture _ => rfl
  | .algorithm n sm lines =>
    rw [recolorRolesBlock]
    show algLineText acc
      (recolorRolesAlgLines recolor pal ground #[] lines.toList).toList = _
    rw [recolorRolesAlgLines_text recolor pal ground lines.toList #[] acc]
    rfl
  | .table cols pl pr rows rules =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesTableRows_text recolor pal ground rows.toList #[] acc,
      blockTextTableRows]
  | .float fk num ca body caption =>
    rw [recolorRolesBlock]
    simp [blockTextOne, plainText,
      recolorRolesInlines_text recolor pal ground caption.toList #[], plainTextList,
      recolorRolesList_text repal recolor pal ground body.toList #[] _, blockTextList]
  | .bibliography src style items =>
    rw [recolorRolesBlock]
    simp [blockTextOne,
      recolorRolesBibItems_text recolor pal ground items.toList #[] acc,
      blockTextBibItems]

theorem recolorRolesItems_text (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) (ground : Option Color) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (recolorRolesItems repal recolor pal ground out items).1.toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [recolorRolesItems, blockTextItems]
  | item :: rest =>
    rw [recolorRolesItems,
      recolorRolesItems_text repal recolor
        (recolorRolesList repal recolor pal ground #[] item.toList).2 ground rest]
    simp [blockTextItems, blockTextItems_chain,
      recolorRolesList_text repal recolor pal ground item.toList #[], blockTextList]

theorem recolorRolesColumns_text (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) (ground : Option Color)
    (cols : List (Option Nat × Array Block))
    (out : Array (Option Nat × Array Block)) (acc : String) :
    blockTextColumns acc (recolorRolesColumns repal recolor pal ground out cols).1.toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [recolorRolesColumns, blockTextColumns]
  | (w, body) :: rest =>
    rw [recolorRolesColumns,
      recolorRolesColumns_text repal recolor
        (recolorRolesList repal recolor pal ground #[] body.toList).2 ground rest]
    simp [blockTextColumns, blockTextColumns_chain,
      recolorRolesList_text repal recolor pal ground body.toList #[], blockTextList]

end

/-- Realization recolours, it never rewrites content: the text census is
fixed through the whole walk, whatever the plan's recolour and palette
rewrite do — a realized document says exactly what the declared one
said. -/
theorem recolorRoles_text (repal : Palette → Palette) (recolor : RoleRecolor)
    (pal : Palette) : Conserves blocksText (recolorRoles repal recolor pal) := fun xs => by
  simp [blocksText, recolorRoles,
    recolorRolesList_text repal recolor pal none xs.toList #[] "", blockTextList]

-- Backend conditionals: `keepFor` is one backend's view of the document,
-- and `keepFor_covers` is what stops a conditional from becoming a silent
-- delete. Structural recursion through `List`, as the walks above.

/-- The backend names an `{ifbackend}` target may spell: one per emitter,
exactly the values `\output{ formats = ... }` accepts (`Cli.Args.emitOne`
mirrors this list, and each backend passes its own entry to `keepFor`). -/
def backendNames : List String := ["pdf", "html", "md"]

/-- Does backend `t` keep this block? Only a conditional can exclude one. -/
def keptBy (t : String) : Block → Bool
  | .only targets _ => targets.contains t
  | .para _ | .equation _ _ | .section _ _ _ _ | .list _ _ | .center _ | .ragged _
  | .quote _ | .abstract _
  | .role _ _
  | .titled _ _ _
  | .spaced _ _
  | .verbatim _ _ _ | .columns _ | .step _ _ _ | .note _ | .logo _
  | .frame _ _ _ _ | .framefoot _ | .setPalette _ | .setTokens _
  | .rule _ _ _ | .nav _ _ | .picture _ | .pagebreak | .algorithm _ _ _
  | .table _ _ _ _ _ | .float _ _ _ _ _ | .bibliography _ _ _ => true

mutual

/-- The document as backend `t` sees it: an `.only` block whose targets
exclude `t` is dropped whole, everything else is kept, and the walk carries
into every body so a nested conditional resolves against its own targets.
Each backend applies this once at its entry, with its own name — the drop
decision lives here and nowhere else, so no backend can improvise a
different reading of the same target set. -/
def keepForOne (t : String) : Block → Block
  | .only targets body => .only targets (keepForList t body.toList).toArray
  | .nav spec body => .nav spec (keepForList t body.toList).toArray
  | .list o items => .list o (keepForItems t items.toList).toArray
  | .center body => .center (keepForList t body.toList).toArray
  | .ragged body => .ragged (keepForList t body.toList).toArray
  | .quote body => .quote (keepForList t body.toList).toArray
  | .abstract body => .abstract (keepForList t body.toList).toArray
  | .titled kind title body => .titled kind title (keepForList t body.toList).toArray
  | .role n body => .role n (keepForList t body.toList).toArray
  | .spaced g body => .spaced g (keepForList t body.toList).toArray
  | .columns cols => .columns (keepForColumns t cols.toList).toArray
  | .step n l body => .step n l (keepForList t body.toList).toArray
  | .note body => .note (keepForList t body.toList).toArray
  | .frame ti st v body => .frame ti st v (keepForList t body.toList).toArray
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
  | .table c pl pr rows rules => .table c pl pr rows rules
  -- Lines hold inlines: no conditional can nest in an algorithm.
  | .algorithm n sm lines => .algorithm n sm lines
  | .float k n ca body caption => .float k n ca (keepForList t body.toList).toArray caption
  -- Entries hold inlines: no conditional can nest in a reference list.
  | .bibliography src style items => .bibliography src style items

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

/-- Algorithm text leaves: each line's declared content is one leaf, its
comment another — a line survives a backend's view whole or not at all,
as a cell does. -/
def algTextLeaves (acc : List String) : List AlgLine → List String
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
def textLeavesList (acc : List String) : List Block → List String
  | [] => acc
  | b :: rest => textLeavesList (textLeavesOne acc b) rest

def textLeavesOne (acc : List String) : Block → List String
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
  | .ragged body => textLeavesList acc body.toList
  | .quote body => textLeavesList acc body.toList
  | .abstract body => textLeavesList acc body.toList
  | .titled _ title body => textLeavesList (plainText title :: acc) body.toList
  | .role _ body => textLeavesList acc body.toList
  | .spaced _ body => textLeavesList acc body.toList
  | .columns cols => textLeavesColumns acc cols.toList
  | .step _ _ body => textLeavesList acc body.toList
  | .note body => textLeavesList acc body.toList
  | .only _ body => textLeavesList acc body.toList
  | .nav _ body => textLeavesList acc body.toList
  | .frame title _ _ body => textLeavesList (plainText title :: acc) body.toList
  -- A rule is decorative ink; it carries no text (as `blockTextOne` reads it).
  | .rule _ _ _ => acc
  -- A picture's labels reach the census through the shipped runs, as
  -- `blockTextOne` reads it.
  | .picture _ => acc
  -- Each cell is one leaf: it survives a backend's view whole or not at
  -- all, which is what the conservation theorem needs to range over. The
  -- caption is a leaf beside its float's body, as a frame's title is.
  | .table _ _ _ rows _ => textLeavesTableRows acc rows.toList
  | .algorithm _ _ lines => algTextLeaves acc lines.toList
  | .float _ _ _ body caption => textLeavesList (plainText caption :: acc) body.toList
  -- Each entry is one leaf, as a cell is: it survives a backend's view
  -- whole or not at all.
  | .bibliography _ _ items => textLeavesBibItems acc items.toList

def textLeavesBibItems (acc : List String) : List BibItem → List String
  | [] => acc
  | item :: rest => textLeavesBibItems (plainText item.content :: acc) rest

def textLeavesTableRows (acc : List String) :
    List (Array (Array Inline)) → List String
  | [] => acc
  | row :: rest => textLeavesTableRows (textLeavesTableCells acc row.toList) rest

def textLeavesTableCells (acc : List String) : List (Array Inline) → List String
  | [] => acc
  | cell :: rest => textLeavesTableCells (plainText cell :: acc) rest

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
performs the same intersection as it walks in and fires E0334 exactly where
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
  | .ragged body => orphanFreeList avail body.toList
  | .quote body => orphanFreeList avail body.toList
  | .abstract body => orphanFreeList avail body.toList
  | .titled _ _ body => orphanFreeList avail body.toList
  | .role _ body => orphanFreeList avail body.toList
  | .spaced _ body => orphanFreeList avail body.toList
  | .columns cols => orphanFreeColumns avail cols.toList
  | .step _ _ body => orphanFreeList avail body.toList
  | .note body => orphanFreeList avail body.toList
  | .nav _ body => orphanFreeList avail body.toList
  | .frame _ _ _ body => orphanFreeList avail body.toList
  | .para _ | .equation _ _ | .section _ _ _ _ | .verbatim _ _ _ | .logo _ | .framefoot _
  | .setPalette _ | .setTokens _ | .algorithm _ _ _
  | .rule _ _ _ | .picture _ | .table _ _ _ _ _ | .pagebreak
  | .bibliography _ _ _ => true
  | .float _ _ _ body _ => orphanFreeList avail body.toList

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
  | .ragged body =>
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
  | .nav spec body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .frame title st v body =>
    rw [textLeavesOne, textLeavesOne,
      textLeavesList_acc (plainText title :: acc) body.toList,
      textLeavesList_acc [plainText title] body.toList]
    simp
  | .table c pl pr rows rules =>
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
  | .table c pl pr rows rules =>
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
  | .ragged body =>
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
condition whose violation elaboration diagnoses as E0334) — every declared
text leaf survives in at least one backend's kept document: the union over
the backends of what each `keepFor` keeps is the declared content. This is
the conservation theorem for the backend conditional, the one that stops
`{ifbackend}` from becoming a silent delete: dropping is only ever the
complement of another backend's keeping, or a named diagnostic. Stated over
the same `plainText` census machinery as the overlay conservation theorems
(`dimBlocks_text`), lifted to whole leaves because
`keepFor` drops whole subtrees. -/
theorem keepFor_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
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
def onlyFreeList : List Block → Bool
  | [] => true
  | b :: rest => onlyFreeOne b && onlyFreeList rest

def onlyFreeOne : Block → Bool
  | .only _ _ => false
  | .list _ items => onlyFreeItems items.toList
  | .center body => onlyFreeList body.toList
  | .ragged body => onlyFreeList body.toList
  | .quote body => onlyFreeList body.toList
  | .abstract body => onlyFreeList body.toList
  | .titled _ _ body => onlyFreeList body.toList
  | .role _ body => onlyFreeList body.toList
  | .spaced _ body => onlyFreeList body.toList
  | .columns cols => onlyFreeColumns cols.toList
  | .step _ _ body => onlyFreeList body.toList
  | .note body => onlyFreeList body.toList
  | .nav _ body => onlyFreeList body.toList
  | .frame _ _ _ body => onlyFreeList body.toList
  | .float _ _ _ body _ => onlyFreeList body.toList
  | .para _ | .equation _ _ | .section _ _ _ _ | .verbatim _ _ _ | .logo _ | .framefoot _
  | .setPalette _ | .setTokens _ | .rule _ _ _ | .picture _ | .algorithm _ _ _
  | .table _ _ _ _ _ | .pagebreak | .bibliography _ _ _ => true

def onlyFreeItems : List (Array Block) → Bool
  | [] => true
  | item :: rest => onlyFreeList item.toList && onlyFreeItems rest

def onlyFreeColumns : List (Option Nat × Array Block) → Bool
  | [] => true
  | (_, body) :: rest => onlyFreeList body.toList && onlyFreeColumns rest

end

def onlyFree (xs : Array Block) : Bool := onlyFreeList xs.toList

mutual

theorem keepForList_id (t : String) (xs : List Block)
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

theorem keepForOne_id (t : String) (b : Block)
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
  | .table c pl pr rows rules => rfl
  | .algorithm n sm lines => rfl
  | .bibliography src style items => rfl
  | .list o items =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForItems_id t items.toList h]
  | .center body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .ragged body =>
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
  | .spaced g body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .columns cols =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForColumns_id t cols.toList h]
  | .step n l body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .note body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .nav spec body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .frame ti st v body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .float k n ca body caption =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]

theorem keepForItems_id (t : String) (items : List (Array Block))
    (h : onlyFreeItems items = true) : keepForItems t items = items := by
  match items with
  | [] => rfl
  | item :: rest =>
    rw [onlyFreeItems, Bool.and_eq_true] at h
    rw [keepForItems, keepForList_id t item.toList h.1,
      keepForItems_id t rest h.2]

theorem keepForColumns_id (t : String) (cols : List (Option Nat × Array Block))
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
theorem keepFor_id (t : String) (xs : Array Block) (h : onlyFree xs = true) :
    keepFor t xs = xs := by
  rw [keepFor, keepForList_id t xs.toList h]


/-- The block face of `bibRefs`: the same leaf over a body not yet
assembled onto a `Doc` — the no-bibliography citation judge (Elab) reads
it where only the blocks exist. -/
def bibRefsBlocks (blocks : Array Block) : Array String :=
  foldBlocks (fun out b => match b with
    | .bibliography src _ _ => if out.contains src then out else out.push src
    | _ => out) (fun out _ => out) #[] blocks

/-- Every `.bib` source the document's `\bibliography` markers name, in
document order, deduplicated: the request value the CLI driver fulfils by
reading each file beside the document and handing its text to `Bib.apply`.
Files are effects, so the core never opens one — `imageRefs`' shape. -/
def bibRefs (doc : Doc) : Array String := bibRefsBlocks doc.body

/-- The document's declared bibliography style: the first
`\bibliographystyle` in document order, `none` when nothing declared —
LaTeX keeps one bibliography style per document. -/
def bibStyleName (doc : Doc) : Option String :=
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
def imageSrcsInlines (out : Array String) (xs : Array Inline) : Array String :=
  foldInlines imageSrcPush out xs

/-- The block face: `foldBlocks` with the same leaf. A `.bibliography`'s
items are formatted renderings and `Bib.apply` builds no image node, so
the fold's refusal to descend them loses nothing. -/
def imageSrcsBlocks (out : Array String) (xs : Array Block) : Array String :=
  foldBlocks (fun out _ => out) imageSrcPush out xs

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

/-- The image-source spelling of a boundary picture: an `.image` whose
source is this prefix plus the request's content hash. The driver fulfils
it from the boundary cache instead of the filesystem. -/
def picSrcPrefix : String := "leantex-pic:"

/-- FNV-1a over the wrapped source, two seeds, 32 hex digits: the boundary
cache key. A content hash, so an unchanged picture never re-runs the tool
and a changed one always does. -/
def picHash (s : String) : String := Id.run do
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

/-- Wrap one picture body for the boundary: `\documentclass{standalone}`,
the preamble declarations a standalone needs (collected from the document
by the elaborator's closed list), and the picture as written. The request
is a pure function of the document — `boundary_request_deterministic`
holds by that purity: two runs over one document state byte-identical
requests, so the cache key means something. -/
def wrapStandalone (preamble : String) (body : String) : String :=
  "\\documentclass{standalone}\n\\usepackage{tikz}\n" ++ preamble ++
    "\\begin{document}\n\\begin{tikzpicture}" ++ body ++
    "\\end{tikzpicture}\n\\end{document}\n"

/-- The boundary requests the shipped tree actually states: `pictureSrcs`
filtered to the hashes an `.image` node still references — a picture
pruned with its frame asks for nothing, exactly as a pruned
`\bibliography` does. -/
def pictureRefs (doc : Doc) : Array (String × String) :=
  let srcs := imageRefs doc
  doc.pictureSrcs.filter fun (h, _) => srcs.contains (picSrcPrefix ++ h)

/-- **The boundary request is environment-free.** What a document requests
at the boundary (`pictureRefs`) is a function of the document alone — the
wrapped standalone sources and the shipped tree — never of the fulfilment
side: repinning the tool field leaves every request untouched. The other
half of the statement is structural, not provable here: the request is
formed in the pure core (`Elab`'s picture arm routes on the door's
presence — a declaration value — and `wrapStandalone`/`picHash` take no
tool), which cannot read PATH, so whether a tool exists on the machine
decides *fulfilment* only — run, serve from the warm cache, or W0379
(`Main.resolvePictures`). The executable half — pinning the default tool
elaborates to the identical `Doc` — runs in `boundaryChecks`. -/
theorem boundary_request_env_free (doc : Doc) (t : Option String) :
    pictureRefs { doc with pictureTool := t } = pictureRefs doc := rfl

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
def logoInForce (init : Option (Array Inline))
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
theorem logo_frames_agree (init : Option (Array Inline))
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
def logoAlign (styles : Styles) : String :=
  ((styles.find? "logo").bind (·.align)).getD "right"

/-- Every image source the logo state ships — the preamble `\logo` and each
body declaration's content. A logo is decorative furniture by role
(WCAG 2.2 SC 1.1.1: content that is pure decoration needs no text
alternative and is implemented so assistive technology can ignore it — the
HTML backend ships `alt=""` on these), so the no-alternative census counts
these sources as decorative, never as missing. -/
def logoImageSrcs (doc : Doc) : Array String :=
  let out := foldBlocks (fun out b => match b with
    | .logo c => imageSrcsInlines out c
    | _ => out) (fun out _ => out) #[] doc.body
  match doc.logo with | some l => imageSrcsInlines out l | none => out

/-- One image node's contribution to the no-alternative census: an
`.image` whose `alt` is empty, its `src` collected once. A leaf
projection of the shared fold — the fold recurses, so this leaf reads
only the node itself; `imageSrcPush`'s shape. -/
private def sansAltStep (out : Array String)
    (x : Inline) : Array String :=
  match x with
  | .image src _ alt =>
    if alt.isEmpty && !out.contains src then out.push src else out
  | _ => out

/-- Every image the artifacts ship with no text alternative, deduplicated,
in document order: the backends read the body and the running head and
foot, so the census reads the same regions (`imageRefs`' scope for shipped
ink). A figure's caption has already become its image's `alt` by
elaboration (`setAltBlocks`), so a captioned figure is not counted — and a
logo's images are not counted either: a logo is decorative furniture by
role (`logoImageSrcs`), so its missing alternative is the conforming state,
never a defect. A boundary picture (`picSrcPrefix`) is not counted here:
its absent alternative is the one fact its trust label already reports —
N0023 says the picture's text is not in the document's census and its help
names the same fix (a caption or alt) — and the route was the engine's
default, not a declared image; one loss, one diagnostic. A caption or alt
still propagates and satisfies both. -/
def imagesSansAlt (doc : Doc) : Array String :=
  let out := foldBlocks (fun out _ => out) sansAltStep #[] doc.body
  let out := match doc.head with | some h => foldInlines sansAltStep out h | none => out
  let out := match doc.foot with | some f => foldInlines sansAltStep out f | none => out
  out.filter (fun src => !(logoImageSrcs doc).contains src &&
    !src.startsWith picSrcPrefix)

/-- The text-alternative judge's file-image face (WCAG 2.2 SC 1.1.1,
Non-text Content: non-text content has a text alternative that serves the
equivalent purpose; sufficient technique G94/H37 — the `alt` attribute).
One diagnostic per distinct source: an image a reader of the page sees and
a reader of the accessibility tree does not is a per-image fact, and the
source names which — with its span (`spanOf`, the elaborator's record), so
the reader goes to the line. Boundary pictures are judged by
`picAltDiags`, after the driver has fulfilled them. -/
def altDiags (doc : Doc) (spanOf : String → Option Span := fun _ => none) :
    Array Diag :=
  ((imagesSansAlt doc).filter fun src => !src.startsWith picSrcPrefix).map fun src =>
    Diag.of .W0376
      (s!"image '{src}' ships no text alternative; assistive technology " ++
        "reads nothing in its place (WCAG 2.2 SC 1.1.1)")
      (spanOf src)
      (help := some ("describe the image — \\includegraphics[alt={...}] — " ++
        "or caption its figure: the caption becomes the alternative"))

/-- The judge's boundary-picture face, read by the driver after fulfilment:
`shipped` says whether the picture's drawn box embeds — a picture the tool
failed on ships a placeholder box, not an image, and W0378 has named that
loss, so naming it here too would name one loss twice. The message speaks
of a picture in the author's words — the source spelling is the engine's
cache key (`picSrcPrefix`), never a word the author wrote — and the help
names the one door that exists: a captioned figure
(`\includegraphics[alt=...]` does not apply to a picture, and a bare
picture has no alt declaration). -/
def picAltDiags (doc : Doc) (spanOf : String → Option Span)
    (shipped : String → Bool) : Array Diag :=
  ((imagesSansAlt doc).filter fun src =>
      src.startsWith picSrcPrefix && shipped src).map fun src =>
    Diag.of .W0376
      ("this picture ships no text alternative; assistive technology " ++
        "reads nothing in its place (WCAG 2.2 SC 1.1.1)")
      (spanOf src)
      (help := some ("caption a figure around the picture: the caption " ++
        "becomes the alternative; a bare picture has no alt key"))

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
theorem alt_judged_complete (doc : Doc) (spanOf : String → Option Span) :
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
def linkReading (body : Array Inline) : String :=
  foldInlines
    (fun s x => match x with | .image _ _ alt => s ++ alt | _ => s)
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

/-- Every link the artifacts ship with no reading — no text, no icon
label, no image alternative — deduplicated by target, in document order:
the backends read the body, the running head and foot, and the logo, so
the census reads the same regions (`imageRefs`' scope for shipped ink). -/
def linksSansText (doc : Doc) : Array String :=
  let out := foldBlocks (fun out _ => out) sansTextLinkStep #[] doc.body
  let out := match doc.head with | some h => foldInlines sansTextLinkStep out h | none => out
  let out := match doc.foot with | some f => foldInlines sansTextLinkStep out f | none => out
  match doc.logo with | some l => foldInlines sansTextLinkStep out l | none => out

/-- The link-purpose judge (WCAG 2.2 SC 2.4.4, Link Purpose (In Context):
the purpose of each link can be determined from the link text; sufficient
technique H30). One diagnostic per distinct target: a link a reader can
follow and an assistive reader cannot name is a per-link fact, and the
target names which. -/
def linkDiags (doc : Doc) : Array Diag :=
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
theorem links_judged_complete (doc : Doc) :
    linkDiags doc = #[] ↔ linksSansText doc = #[] := by
  rw [← Array.size_eq_zero_iff, ← Array.size_eq_zero_iff, linkDiags,
    Array.size_map]

mutual

/-- One leaf-parameterised map hosts every leaf-rewrite walk over the tree:
`f` rewrites each childless node — applied to the node itself, never to a
wrapper, whose body recurses below so the checker sees the recursion, as
`foldInline`'s shape does. `setAltBlocks`, `resolveRefs`, and
`Layout.substPage` are its leaf functions: a leaf function carries the one
rewrite, and the explicit-arm obligation lives here, once. -/
def mapInlines (f : Inline → Inline) (xs : Array Inline) : Array Inline :=
  mapInlineList f #[] xs.toList

def mapInlineList (f : Inline → Inline) (out : Array Inline) :
    List Inline → Array Inline
  | [] => out
  | x :: rest => mapInlineList f (out.push (mapInline f x)) rest

def mapInline (f : Inline → Inline) : Inline → Inline
  | .styled st body => .styled st (mapInlineList f #[] body.toList)
  | .colored c n body => .colored c n (mapInlineList f #[] body.toList)
  | .role n body => .role n (mapInlineList f #[] body.toList)
  | .link u body => .link u (mapInlineList f #[] body.toList)
  | .underline body => .underline (mapInlineList f #[] body.toList)
  | .step n l body => .step n l (mapInlineList f #[] body.toList)
  | .footnote n body => .footnote n (mapInlineList f #[] body.toList)
  | .text s => f (.text s)
  | .math d src => f (.math d src)
  | .formula d src body => f (.formula d src body)
  | .image src size alt => f (.image src size alt)
  | .icon s l => f (.icon s l)
  | .label k => f (.label k)
  | .ref k p t tg => f (.ref k p t tg)
  | .cite tx keys => f (.cite tx keys)
  | .fill => f .fill
  | .strut h => f (.strut h)
  | .pageNumber => f .pageNumber
  | .pageCount => f .pageCount
  | .linebreak e => f (.linebreak e)

end

def mapTableCells (f : Inline → Inline) (out : Array (Array Inline)) :
    List (Array Inline) → Array (Array Inline)
  | [] => out
  | cell :: rest => mapTableCells f (out.push (mapInlines f cell)) rest

def mapTableRows (f : Inline → Inline) (out : Array (Array (Array Inline))) :
    List (Array (Array Inline)) → Array (Array (Array Inline))
  | [] => out
  | row :: rest => mapTableRows f (out.push (mapTableCells f #[] row.toList)) rest

def mapBibItems (f : Inline → Inline) (out : Array BibItem) :
    List BibItem → Array BibItem
  | [] => out
  | i :: rest =>
    mapBibItems f (out.push { i with content := mapInlines f i.content }) rest

mutual

/-- The block face of the map: every inline region — a paragraph's content,
a title, a caption, each table cell, a formatted bibliography entry, the
running furniture — is mapped, and every block wrapper keeps its shape.
One descent for the whole leaf-rewrite family, so a rewrite cannot
silently skip a region a sibling walk reaches: two of the three hand-rolled
copies this map replaced skipped real ones. -/
def mapAlgLines (f : Inline → Inline) (out : Array AlgLine) :
    List AlgLine → Array AlgLine
  | [] => out
  | l :: rest =>
    mapAlgLines f (out.push
      { depth := l.depth
        kind := l.kind
        content := mapInlines f l.content
        comment := l.comment.map (mapInlines f) }) rest

def mapBlocks (f : Inline → Inline) (xs : Array Block) : Array Block :=
  mapBlockList f #[] xs.toList

def mapBlockList (f : Inline → Inline) (out : Array Block) :
    List Block → Array Block
  | [] => out
  | b :: rest => mapBlockList f (out.push (mapBlock f b)) rest

def mapBlock (f : Inline → Inline) : Block → Block
  | .para content => .para (mapInlines f content)
  | .equation n content => .equation n (mapInlines f content)
  | .section l st n title => .section l st n (mapInlines f title)
  | .list o items => .list o (mapBlockItems f #[] items.toList)
  | .center body => .center (mapBlockList f #[] body.toList)
  | .ragged body => .ragged (mapBlockList f #[] body.toList)
  | .quote body => .quote (mapBlockList f #[] body.toList)
  | .abstract body => .abstract (mapBlockList f #[] body.toList)
  | .titled kind title body =>
    .titled kind (mapInlines f title) (mapBlockList f #[] body.toList)
  | .role n body => .role n (mapBlockList f #[] body.toList)
  | .spaced g body => .spaced g (mapBlockList f #[] body.toList)
  | .columns cols => .columns (mapBlockCols f #[] cols.toList)
  | .step n l body => .step n l (mapBlockList f #[] body.toList)
  | .only targets body => .only targets (mapBlockList f #[] body.toList)
  | .nav spec body => .nav spec (mapBlockList f #[] body.toList)
  | .note body => .note (mapBlockList f #[] body.toList)
  | .frame title st v body =>
    .frame (mapInlines f title) st v (mapBlockList f #[] body.toList)
  | .framefoot content => .framefoot (mapInlines f content)
  | .float k num ca body caption =>
    .float k num ca (mapBlockList f #[] body.toList) (mapInlines f caption)
  | .table c pl pr rows rules =>
    .table c pl pr (mapTableRows f #[] rows.toList) rules
  | .algorithm n sm lines => .algorithm n sm (mapAlgLines f #[] lines.toList)
  | .logo content => .logo (mapInlines f content)
  | .bibliography src style items =>
    .bibliography src style (mapBibItems f #[] items.toList)
  | .verbatim c s spec =>
    .verbatim c s { spec with caption := spec.caption.map fun (n, cap) =>
      (n, mapInlines f cap) }
  | .setPalette pal => .setPalette pal
  | .setTokens tk => .setTokens tk
  | .pagebreak => .pagebreak
  | .rule c n th => .rule c n th
  | .picture pic => .picture pic

def mapBlockItems (f : Inline → Inline) (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block)
  | [] => out
  | item :: rest => mapBlockItems f (out.push (mapBlockList f #[] item.toList)) rest

def mapBlockCols (f : Inline → Inline) (out : Array (Option Nat × Array Block)) :
    List (Option Nat × Array Block) → Array (Option Nat × Array Block)
  | [] => out
  | (w, body) :: rest =>
    mapBlockCols f (out.push (w, mapBlockList f #[] body.toList)) rest

end

mutual

/-- The census face of the map, per node: a leaf function that conserves
each node's own census conserves every node's. `mapInlines_text` and
`mapBlocks_text` are the walk-level schema; a leaf-rewrite states its
census fact as their one-line instance instead of one hand induction per
walk. -/
theorem mapInline_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (x : Inline) :
    plainTextOne (mapInline f x) = plainTextOne x := by
  match x with
  | .styled st body =>
    show plainTextList (mapInlineList f #[] body.toList).toList = _
    rw [mapInlineList_text f hf body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .colored c n body =>
    show plainTextList (mapInlineList f #[] body.toList).toList = _
    rw [mapInlineList_text f hf body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .role n body =>
    show plainTextList (mapInlineList f #[] body.toList).toList = _
    rw [mapInlineList_text f hf body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .link u body =>
    show plainTextList (mapInlineList f #[] body.toList).toList = _
    rw [mapInlineList_text f hf body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .underline body =>
    show plainTextList (mapInlineList f #[] body.toList).toList = _
    rw [mapInlineList_text f hf body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .step n l body =>
    show plainTextList (mapInlineList f #[] body.toList).toList = _
    rw [mapInlineList_text f hf body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .footnote n body =>
    show plainTextList (mapInlineList f #[] body.toList).toList = _
    rw [mapInlineList_text f hf body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .strut _
  | .pageNumber | .pageCount | .linebreak _ => exact hf _

theorem mapInlineList_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (xs : List Inline)
    (out : Array Inline) :
    plainTextList (mapInlineList f out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [mapInlineList, plainTextList]
  | x :: rest =>
    rw [mapInlineList, mapInlineList_text f hf rest (out.push (mapInline f x))]
    rw [Array.toList_push, plainTextList_append]
    simp [plainTextList, mapInline_text f hf x, String.append_assoc]

end

/-- The `Conserves` schema over the generic map, inline face: whatever the
leaf function, if it conserves each node's census the walk conserves the
content's. -/
theorem mapInlines_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) :
    Conserves plainText (mapInlines f) := fun xs => by
  show plainTextList (mapInlineList f #[] xs.toList).toList = _
  rw [mapInlineList_text f hf xs.toList #[]]
  simp [plainTextList, plainText]

private theorem mapAlgLines_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (ls : List AlgLine)
    (out : Array AlgLine) (acc : String) :
    algLineText acc (mapAlgLines f out ls).toList
      = algLineText (algLineText acc out.toList) ls := by
  match ls with
  | [] => simp [mapAlgLines, algLineText]
  | l :: rest =>
    rw [mapAlgLines, mapAlgLines_text f hf rest]
    rw [Array.toList_push, algLineText_chain]
    have hm : ∀ xs, plainText (mapInlines f xs) = plainText xs := mapInlines_text f hf
    cases hc : l.comment <;> simp [algLineText, hc, hm]


mutual

/-- The Bool fold un-threads: the accumulator rides outside as one `||`,
which is what lets `anyInline p = false` decompose per node below. -/
theorem foldInline_or (p : Inline → Bool) (b : Bool) (x : Inline) :
    foldInline (fun a y => a || p y) b x
      = (b || foldInline (fun a y => a || p y) false x) := by
  match x with
  | .styled st body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .colored c n body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .role n body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .link u body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .underline body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .step n l body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .footnote n body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .strut _
  | .pageNumber | .pageCount | .linebreak _ => simp [foldInline]

theorem foldInlineList_or (p : Inline → Bool) (b : Bool) (xs : List Inline) :
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
theorem mapInline_id (f : Inline → Inline) (p : Inline → Bool)
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
  | .underline body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .step n l body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .footnote n body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .strut _
  | .pageNumber | .pageCount | .linebreak _ =>
    exact hf _ (by simpa [foldInline] using h)

theorem mapInlineList_id (f : Inline → Inline) (p : Inline → Bool)
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
theorem mapInlines_id (f : Inline → Inline) (p : Inline → Bool)
    (hf : ∀ x, p x = false → f x = x) (xs : Array Inline)
    (h : anyInline p xs = false) : mapInlines f xs = xs := by
  rw [mapInlines, mapInlineList_id f p hf xs.toList #[] h]
  simp

private theorem mapTableCells_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (cells : List (Array Inline))
    (out : Array (Array Inline)) (acc : String) :
    blockTextTableCells acc (mapTableCells f out cells).toList
      = blockTextTableCells (blockTextTableCells acc out.toList) cells := by
  match cells with
  | [] => simp [mapTableCells, blockTextTableCells]
  | cell :: rest =>
    rw [mapTableCells, mapTableCells_text f hf rest]
    rw [Array.toList_push, blockTextTableCells_chain]
    simp [blockTextTableCells, mapInlines_text f hf cell]

private theorem mapTableRows_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (rows : List (Array (Array Inline)))
    (out : Array (Array (Array Inline))) (acc : String) :
    blockTextTableRows acc (mapTableRows f out rows).toList
      = blockTextTableRows (blockTextTableRows acc out.toList) rows := by
  match rows with
  | [] => simp [mapTableRows, blockTextTableRows]
  | row :: rest =>
    rw [mapTableRows, mapTableRows_text f hf rest]
    rw [Array.toList_push, blockTextTableRows_chain]
    simp [blockTextTableRows, blockTextTableCells, mapTableCells_text f hf row.toList #[]]

private theorem mapBibItems_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (items : List BibItem)
    (out : Array BibItem) (acc : String) :
    blockTextBibItems acc (mapBibItems f out items).toList
      = blockTextBibItems (blockTextBibItems acc out.toList) items := by
  match items with
  | [] => simp [mapBibItems, blockTextBibItems]
  | i :: rest =>
    rw [mapBibItems, mapBibItems_text f hf rest]
    rw [Array.toList_push, blockTextBibItems_chain]
    simp [blockTextBibItems, mapInlines_text f hf i.content]

mutual

theorem mapBlock_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (acc : String) (b : Block) :
    blockTextOne acc (mapBlock f b) = blockTextOne acc b := by
  match b with
  | .para content => simp [mapBlock, blockTextOne, mapInlines_text f hf content]
  | .equation n content =>
    simp [mapBlock, blockTextOne, mapInlines_text f hf content]
  | .section l st n title =>
    simp [mapBlock, blockTextOne, mapInlines_text f hf title]
  | .list o items =>
    show blockTextItems acc (mapBlockItems f #[] items.toList).toList = _
    rw [mapBlockItems_text f hf items.toList #[]]
    rfl
  | .center body =>
    show blockTextList acc (mapBlockList f #[] body.toList).toList = _
    rw [mapBlockList_text f hf body.toList #[]]
    rfl
  | .ragged body =>
    show blockTextList acc (mapBlockList f #[] body.toList).toList = _
    rw [mapBlockList_text f hf body.toList #[]]
    rfl
  | .quote body =>
    show blockTextList acc (mapBlockList f #[] body.toList).toList = _
    rw [mapBlockList_text f hf body.toList #[]]
    rfl
  | .abstract body =>
    show blockTextList acc (mapBlockList f #[] body.toList).toList = _
    rw [mapBlockList_text f hf body.toList #[]]
    rfl
  | .titled kind title body =>
    show blockTextList (acc ++ plainText (mapInlines f title))
      (mapBlockList f #[] body.toList).toList = _
    rw [mapInlines_text f hf title, mapBlockList_text f hf body.toList #[]]
    rfl
  | .role n body =>
    show blockTextList acc (mapBlockList f #[] body.toList).toList = _
    rw [mapBlockList_text f hf body.toList #[]]
    rfl
  | .spaced g body =>
    show blockTextList acc (mapBlockList f #[] body.toList).toList = _
    rw [mapBlockList_text f hf body.toList #[]]
    rfl
  | .columns cols =>
    show blockTextColumns acc (mapBlockCols f #[] cols.toList).toList = _
    rw [mapBlockCols_text f hf cols.toList #[]]
    rfl
  | .step n l body =>
    show blockTextList acc (mapBlockList f #[] body.toList).toList = _
    rw [mapBlockList_text f hf body.toList #[]]
    rfl
  | .only targets body =>
    show blockTextList acc (mapBlockList f #[] body.toList).toList = _
    rw [mapBlockList_text f hf body.toList #[]]
    rfl
  | .nav spec body =>
    show blockTextList acc (mapBlockList f #[] body.toList).toList = _
    rw [mapBlockList_text f hf body.toList #[]]
    rfl
  | .note body =>
    show blockTextList acc (mapBlockList f #[] body.toList).toList = _
    rw [mapBlockList_text f hf body.toList #[]]
    rfl
  | .frame title st v body =>
    show blockTextList (acc ++ plainText (mapInlines f title))
      (mapBlockList f #[] body.toList).toList = _
    rw [mapInlines_text f hf title, mapBlockList_text f hf body.toList #[]]
    rfl
  | .framefoot content =>
    simp [mapBlock, blockTextOne, mapInlines_text f hf content]
  | .float k num ca body caption =>
    show blockTextList (acc ++ plainText (mapInlines f caption))
      (mapBlockList f #[] body.toList).toList = _
    rw [mapInlines_text f hf caption, mapBlockList_text f hf body.toList #[]]
    rfl
  | .table c pl pr rows rules =>
    show blockTextTableRows acc (mapTableRows f #[] rows.toList).toList = _
    rw [mapTableRows_text f hf rows.toList #[]]
    rfl
  | .algorithm n sm lines =>
    show algLineText acc (mapAlgLines f #[] lines.toList).toList = _
    rw [mapAlgLines_text f hf lines.toList #[]]
    rfl
  | .logo content => simp [mapBlock, blockTextOne, mapInlines_text f hf content]
  | .bibliography src style items =>
    show blockTextBibItems acc (mapBibItems f #[] items.toList).toList = _
    rw [mapBibItems_text f hf items.toList #[]]
    rfl
  -- The listing caption maps as a float's does, and the leaf rewrite
  -- conserves its text; the body is one opaque string.
  | .verbatim _ _ spec =>
    cases hc : spec.caption with
    | none => simp [mapBlock, blockTextOne, ListingSpec.capText, hc]
    | some p =>
      simp [mapBlock, blockTextOne, ListingSpec.capText, hc,
        mapInlines_text f hf p.2]
  | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ => rfl

theorem mapBlockList_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (bs : List Block)
    (out : Array Block) (acc : String) :
    blockTextList acc (mapBlockList f out bs).toList
      = blockTextList (blockTextList acc out.toList) bs := by
  match bs with
  | [] => simp [mapBlockList, blockTextList]
  | b :: rest =>
    rw [mapBlockList, mapBlockList_text f hf rest]
    rw [Array.toList_push, blockTextList_chain]
    simp [blockTextList, mapBlock_text f hf]

theorem mapBlockItems_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (mapBlockItems f out items).toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [mapBlockItems, blockTextItems]
  | item :: rest =>
    rw [mapBlockItems, mapBlockItems_text f hf rest]
    rw [Array.toList_push, blockTextItems_chain]
    simp [blockTextItems, blockTextList, mapBlockList_text f hf item.toList #[]]

theorem mapBlockCols_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (cols : List (Option Nat × Array Block))
    (out : Array (Option Nat × Array Block)) (acc : String) :
    blockTextColumns acc (mapBlockCols f out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [mapBlockCols, blockTextColumns]
  | (w, body) :: rest =>
    rw [mapBlockCols, mapBlockCols_text f hf rest]
    rw [Array.toList_push, blockTextColumns_chain]
    simp [blockTextColumns, blockTextList, mapBlockList_text f hf body.toList #[]]

end

/-- The `Conserves` schema over the generic map, block face:
`setAltBlocks_text` is its one-line instance, and the next leaf-rewrite's
census fact costs the same one line. -/
theorem mapBlocks_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) :
    Conserves blocksText (mapBlocks f) := fun xs => by
  show blockTextList "" (mapBlockList f #[] xs.toList).toList = _
  rw [mapBlockList_text f hf xs.toList #[]]
  rfl

/-- Give every image that has no `alt` yet this text: how a `figure`'s
caption becomes the accessible name of the image it captions. The walk is
`mapBlocks`, whose descent is total, so the caption reaches an image
wherever the body put it — in a list, under a wrapper, in a table cell.
(The hand-rolled walk this replaced skipped those bodies through a
wildcard arm; an image already carrying an alt keeps its own, so an inner
float's caption still wins over the outer's.) -/
private def setAltLeaf (alt : String)
    (x : Inline) : Inline :=
  match x with
  | .image src size old => .image src size (if old.isEmpty then alt else old)
  | _ => x

def setAltBlocks (alt : String) (xs : Array Block) : Array Block :=
  mapBlocks (setAltLeaf alt) xs

/-- Caption-to-alt is markup, never content: the census does not read an
image's text alternative, so the walk ships exactly the text census the
body had — the schema's first one-line instance. -/
theorem setAltBlocks_text (alt : String) :
    Conserves blocksText (setAltBlocks alt) :=
  mapBlocks_text _ (fun x => by cases x <;> rfl)

/-- One character of a label's anchor: word characters and the punctuation
label keys conventionally carry (`fig:scm`, `eq.1`, `a-b`, `x_y`) survive
verbatim; anything else — whitespace included — folds to a hyphen. -/
def labelAnchorChar (c : Char) : Char :=
  if c.isAlpha || c.isDigit || c == ':' || c == '.' || c == '-' || c == '_' then c
  else '-'

/-- The id a `\label` key takes in the HTML page and a resolved reference
targets: the key sanitised character-wise — one resolving site for both
ends, so a link and its anchor cannot disagree. An empty key still yields
an id, HTML §3.2.6's non-emptiness. Two distinct keys can fold to one
anchor only when they differ in folded characters, which the key
conventions above never use. -/
def labelAnchor (key : String) : String :=
  match key.toList.map labelAnchorChar with
  | [] => "label"
  | l => String.ofList l

/-- The sanitiser never lets a character through that the kept set refuses:
whatever the key spelled, the anchor's characters are word characters, the
kept punctuation, or the fold hyphen — never `bad`. -/
theorem labelAnchorChar_not (c bad : Char)
    (hbad : (bad.isAlpha || bad.isDigit || bad == ':' || bad == '.' ||
      bad == '-' || bad == '_') = false) :
    labelAnchorChar c ≠ bad := by
  unfold labelAnchorChar
  split <;> rintro rfl <;> simp_all

/-- The label key is author text entering an `id` attribute and an `href`,
so it owes the same statement `roleClass_single_token` makes for authored
class names: no character of an anchor is ASCII whitespace (HTML §3.2.6's
id contract) or a quote (the attribute-breakout characters `escapeAttr`
kills). Here the statement needs no alphabet hypothesis — the sanitiser is
total over whatever the document spelled. -/
theorem labelAnchor_single_token (key : String) :
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
inductive RefKind where
  | heading | equation | figure | table | algorithm
  deriving Repr, BEq

/-- One label's binding: the number it bound to, with the kind of the
numbered thing when elaboration made one. A binding the engine numbers
without a node of any kind — a bare `\refstepcounter` — carries `none`:
what such a label names has no kind, so a `\cref` to it sets the plain
number, named (W0380). -/
structure RefBinding where
  kind : Option RefKind
  num : String
  deriving Repr, BEq

/-- The label table resolution spends: each key with the binding its
`\label` took in flow order (`none`: the label stood where nothing
numbers). Elaboration builds it — the first declaration of a key wins,
W0350 names the rest — and `resolveRefs` is the single pass over the IR
that resolves every reference against it, so no backend re-scans for
labels. -/
abbrev RefTable := Array (String × Option RefBinding)

/-- cleveref's name for a kind: the one resolving site both `refText`
readers use, so `\cref` and `\namecref` cannot disagree on a kind's name.
Every heading level takes the section name, as cleveref's subsection
names are the section's own (its english block). -/
def crefNameOf (loc : Locale) : RefKind → CrefName
  | .heading => loc.crefSection
  | .equation => loc.crefEquation
  | .figure => loc.crefFigure
  | .table => loc.crefTable
  | .algorithm => loc.crefAlgorithm

/-- Every kind, for the coverage contract: an added constructor fails
`all_complete` until it is listed, and listed is covered
(`crefNameOf_covers`) — the DiagCode registry's shape. -/
def RefKind.all : List RefKind :=
  [.heading, .equation, .figure, .table, .algorithm]

theorem RefKind.all_complete (k : RefKind) : RefKind.all.contains k := by
  cases k <;> rfl

/-- Every label kind the engine assigns has its cleveref names, all four
forms, in every shipped locale — with the range conjunction beside them.
Quantified over `Locale.builtin` (adding a locale is entering the
contract) and `RefKind.all` (complete by `RefKind.all_complete`): the
statement behind `\cref` never printing an empty name. -/
theorem crefNameOf_covers :
    (Locale.builtin.all fun l =>
      (RefKind.all.all fun k =>
        !(crefNameOf l k).one.isEmpty && !(crefNameOf l k).many.isEmpty &&
        !(crefNameOf l k).capOne.isEmpty && !(crefNameOf l k).capMany.isEmpty)
      && !l.crefRangeTo.isEmpty) = true := by decide +kernel

/-- A cref-form number: equation numbers keep their parentheses in every
cleveref form (cleveref.sty `\creflabelformat{equation}{...\textup{(#1)}}`);
every other kind shows the bare number. -/
def crefNum (b : RefBinding) : String :=
  if b.kind == some .equation then "(" ++ b.num ++ ")" else b.num

/-- The text one resolved reference shows, the one rendering site
(`resolveOneRef` and its theorems read it): `\ref`'s bare number,
`\eqref`'s parentheses, and cleveref's forms over the binding's kind —
name and number joined by the package's own no-break space. A kindless
binding (a bare `\refstepcounter`) sets the plain number under every
cleveref form, and W0349's judge names it (W0380). -/
def refText (loc : Locale) (form : RefForm) (b : RefBinding) : String :=
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

/-- One reference against the table. A key bound to a number takes exactly
its form's text over the binding (`refText`) and the label's anchor; a key
the table cannot number keeps LaTeX's own `??` and no target (the
elaborator has already named it, W0349). -/
def resolveOneRef (loc : Locale) (table : RefTable) (key : String)
    (form : RefForm) : Inline :=
  match table.find? (·.1 == key) with
  | some (_, some b) =>
    .ref key form (refText loc form b) (some (labelAnchor key))
  | _ => .ref key form "??" none

/-- Resolution's one rewrite: every `.ref` is rewritten from the table
(`resolveOneRef_exact` is its statement), everything else keeps its shape
and is walked by the generic map. -/
private def resolveRefLeaf (loc : Locale) (table : RefTable)
    (x : Inline) : Inline :=
  match x with
  | .ref key form _ _ => resolveOneRef loc table key form
  | _ => x

-- conserves: none — resolution rewrites a ref's placeholder text to its
-- number, which is the pass's whole point; `resolveOneRef_exact` is its
-- statement.
def resolveRefInline (loc : Locale) (table : RefTable) (x : Inline) : Inline :=
  mapInline (resolveRefLeaf loc table) x

-- conserves: none — the block face of resolveRefInline, same reason.
def resolveRefs (loc : Locale) (table : RefTable) (xs : Array Block) : Array Block :=
  mapBlocks (resolveRefLeaf loc table) xs

/-- References resolve to what they name: when the table binds `key` to
binding `b` — elaboration binds a key declared exactly once to the numbered
node in force where its `\label` stood — the resolved reference shows
exactly its form's text over `b` (`refText`) and targets exactly that
label's anchor. The `\ref` and the `\label` cannot disagree, because both
read this one entry. -/
theorem resolveOneRef_exact (loc : Locale) (table : RefTable) (key : String)
    (form : RefForm)
    (b : RefBinding) (h : ∃ e ∈ table, e.1 = key ∧ e.2 = some b)
    (huniq : ∀ e ∈ table, e.1 = key → e.2 = some b) :
    resolveOneRef loc table key form =
      .ref key form (refText loc form b)
        (some (labelAnchor key)) := by
  unfold resolveOneRef
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
theorem resolveOneRef_missing (loc : Locale) (table : RefTable) (key : String)
    (form : RefForm) (h : ∀ e ∈ table, e.1 ≠ key) :
    resolveOneRef loc table key form = .ref key form "??" none := by
  unfold resolveOneRef
  have hfind : table.find? (·.1 == key) = none := by
    rw [Array.find?_eq_none]
    intro e hmem
    simp [h e hmem]
  rw [hfind]

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

/-- Labels inside algorithm lines, bound to the binding in force — a
`\label` under a captioned algorithm float resolves to its number. -/
private def algFloatLabels (float : Option RefBinding)
    (out : Array (String × Option RefBinding)) :
    List AlgLine → Array (String × Option RefBinding)
  | [] => out
  | l :: rest =>
    algFloatLabels float (match l.comment with
      | some c => foldInlineList (floatLabelPush float)
          (foldInlineList (floatLabelPush float) out l.content.toList) c.toList
      | none => foldInlineList (floatLabelPush float) out l.content.toList) rest

mutual

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
label commands"); here it resolves to the number the author captioned. -/
def floatLabelOne (float : Option RefBinding) (out : Array (String × Option RefBinding)) :
    Block → Array (String × Option RefBinding)
  | .para content => foldInlineList (floatLabelPush float) out content.toList
  | .equation _ content => foldInlineList (floatLabelPush none) out content.toList
  | .section _ _ _ title => foldInlineList (floatLabelPush none) out title.toList
  | .list _ items => floatLabelItems float out items.toList
  | .center body => floatLabelList float out body.toList
  | .ragged body => floatLabelList float out body.toList
  | .quote body => floatLabelList float out body.toList
  | .abstract body => floatLabelList float out body.toList
  | .titled _ title body =>
    floatLabelList float (foldInlineList (floatLabelPush float) out title.toList)
      body.toList
  | .role _ body => floatLabelList float out body.toList
  | .spaced _ body => floatLabelList float out body.toList
  | .columns cols => floatLabelCols float out cols.toList
  | .step _ _ body => floatLabelList float out body.toList
  | .only _ body => floatLabelList float out body.toList
  | .nav _ body => floatLabelList float out body.toList
  | .note body => floatLabelList float out body.toList
  | .frame title _ _ body =>
    floatLabelList float (foldInlineList (floatLabelPush float) out title.toList)
      body.toList
  | .framefoot content => foldInlineList (floatLabelPush float) out content.toList
  | .float kind num _ body caption =>
    let mine := match num with
      | none => float
      | some m =>
        match kind with
        -- A subfloat letters under its parent: the binding keeps the
        -- parent's kind, as cleveref's subfigure names are the figure's.
        | .sub => some { kind := float.bind (·.kind)
                         num := ((float.map (·.num)).getD "") ++ subLetter m }
        | .figure => some { kind := some .figure, num := toString m }
        | .table => some { kind := some .table, num := toString m }
        | .algorithm => some { kind := some .algorithm, num := toString m }
    floatLabelList mine (foldInlineList (floatLabelPush mine) out caption.toList)
      body.toList
  | .table _ _ _ rows _ => foldTableRows (floatLabelPush float) out rows.toList
  | .algorithm _ _ lines => algFloatLabels float out lines.toList
  | .logo content => foldInlineList (floatLabelPush float) out content.toList
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .bibliography _ _ _ => out

def floatLabelList (float : Option RefBinding) (out : Array (String × Option RefBinding)) :
    List Block → Array (String × Option RefBinding)
  | [] => out
  | b :: rest => floatLabelList float (floatLabelOne float out b) rest

def floatLabelItems (float : Option RefBinding) (out : Array (String × Option RefBinding)) :
    List (Array Block) → Array (String × Option RefBinding)
  | [] => out
  | item :: rest => floatLabelItems float (floatLabelList float out item.toList) rest

def floatLabelCols (float : Option RefBinding) (out : Array (String × Option RefBinding)) :
    List (Option Nat × Array Block) → Array (String × Option RefBinding)
  | [] => out
  | (_, body) :: rest => floatLabelCols float (floatLabelList float out body.toList) rest

end

/-- `floatLabelOne` over the numbered body: every label with the float
binding in force where it stands, the table's float half. -/
def floatLabelRows (xs : Array Block) : RefTable :=
  floatLabelList none #[] xs.toList

/-- The label table with its float rows filled from the numbered IR: an
entry whose key's first `.label` stands under a captioned float takes that
float's number; every other entry keeps elaboration's binding (headings
and equations number at elaboration; a key bound nowhere keeps `none` and
W0349 names it). `rows` is `floatLabelRows` over the numbered body. -/
def withFloatRows (labels rows : RefTable) : RefTable :=
  labels.map fun e =>
    match rows.find? (·.1 == e.1) with
    | some (_, some n) => (e.1, some n)
    | _ => e

/-- The merge keeps keys and takes exactly the collect's binding: when the
collect's first row for `key` carries a number and elaboration recorded
the key at all, the merged table's answer for `key` is that number. -/
theorem withFloatRows_finds (labels rows : RefTable) (key : String) (b : RefBinding)
    (hrow : rows.find? (·.1 == key) = some (key, some b))
    (hkey : (labels.find? (·.1 == key)).isSome) :
    (withFloatRows labels rows).find? (·.1 == key) = some (key, some b) := by
  unfold withFloatRows
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hkey
  have hekey : e.1 = key := by simpa using Array.find?_some he
  rw [Array.find?_map]
  have hp : ((fun x : String × Option RefBinding => x.1 == key) ∘ fun e =>
      match rows.find? (·.1 == e.1) with
      | some (_, some n) => (e.1, some n)
      | _ => e) = fun e : String × Option RefBinding => e.1 == key := by
    funext x
    cases hx : rows.find? (·.1 == x.1) with
    | none => simp [Function.comp, hx]
    | some p =>
      obtain ⟨pk, pv⟩ := p
      cases pv <;> simp [Function.comp, hx]
  rw [hp, he, Option.map_some]
  rw [hekey, hrow]

/-- Floats are numbered once, from the proved walk. `numberFloats` assigns
every captioned float's number (`numberFloats_exact`: gapless, 1-based,
document order), `floatLabelRows` reads those numbers off the numbered
nodes where each `\label` stands, `withFloatRows` carries them into the
table, and resolution shows precisely that entry: a resolved reference to
a float shows exactly the number the float node carries, and targets the
label's anchor. Before this pipeline, elaboration *predicted* the number
and nothing related predictor to assigner; now there is no predictor, and
the agreement is this theorem, stated over the engine's own functions. -/
theorem refs_agree_with_numbering (loc : Locale) (labels : RefTable) (xs : Array Block)
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
  unfold resolveOneRef
  rw [h]

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
