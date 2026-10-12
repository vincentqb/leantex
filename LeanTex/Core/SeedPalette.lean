module

public import LeanTex.Core.Color
public import LeanTex.Core.DesignRole
public import LeanTex.Core.ContrastRatio
public import LeanTex.Core.Oklab
import LeanTex.Core.ContrastSolve

/-!
A palette generated from its seeds: an ink, a paper and an accent (and, if
the author names them, an alert, an example and a neutral), shipped exactly,
and every other role derived from them by stated rules in Oklab, each
checked against the contrast its sites owe.

* Grounds are tints solved by their WCAG 2.2 ratio to the page, at a family
  hue whose chroma grows with distance from the page (`Family.tint`): a
  neutral family for surfaces and bands, the accent's for washes. The
  neutral hue is the paper's where it has one, else the ink's, else the
  accent's — Radix Colors' pairing of a gray scale with its accent
  (https://www.radix-ui.com/colors/docs/palette-composition/composing-a-palette).
  Chroma grows at κ per unit of lightness, measured on Tailwind v4's
  slate 50–300 (0.16–0.22) and orange 50–200 (0.76–0.83)
  (https://tailwindcss.com/docs/colors), capped at a peak.
* Inks are the quietest tone of their family that meets the text or the
  non-text target on every ground they stand on — Material 3's tonal rule
  (https://m3.material.io/styles/color/system/how-the-system-works): a key
  colour fixes hue and chroma, the ground chooses the tone. An accent seed
  that already passes ships as itself.
* A warm accent's darker tones turn toward red (`Oklab.Okl.turn`), as
  Tailwind's amber and yellow 500 → 700 and Radix amber 9 → 11 do; any
  other hue is held.
* Targets sit 0.10 above WCAG 2.2's gates (SC 1.4.3 text 4.5:1, SC 1.4.11
  non-text 3:1), because `contrastMilli` truncates by up to 0.007.

A generated palette carries its contract (`Generated.valid`): every site it
creates meets its target, every ground stands within its band, its tints keep
their family's chroma and hue, and both block styles' pairs read. Nothing
here runs when a module initializes; a document's `\palette[seeds]` calls
`generate` once per seeds.
-/

namespace LeanTex.Core.SeedPalette

open Ir Oklab Contrast

/-- The colours an author names. `ink`, `paper` and `accent` ship exactly as
the page's text, ground and accent; `alert` and `example`, where named, are
the families those roles take their tones from; `neutral` overrides the
hue surfaces and muted inks take. -/
public structure Seeds where
  ink : Color
  paper : Color
  accent : Color
  alert : Option Color := none
  exampleColor : Option Color := none
  neutral : Option Color := none
  deriving Repr, BEq, Inhabited

/-- How a block's title and body are painted: `tonal` titles in the ink on a
neutral band over a neutral body, the alert's on the accent's band over its
wash; `strong` titles on the ink over an accent wash, the decks' hand look. -/
public inductive Blocks where
  | tonal
  | strong
  deriving Repr, BEq, DecidableEq, Inhabited

public def Blocks.all : List Blocks := [.tonal, .strong]

public def Blocks.ofName? : String → Option Blocks
  | "tonal" => some .tonal
  | "strong" => some .strong
  | _ => none

public def Blocks.name : Blocks → String
  | .tonal => "tonal"
  | .strong => "strong"

/-- The ratios a palette is generated to, ×1000: the grounds' ratios to the
page (a neutral body and band, a rule, the accent's wash and band), the
least ratio between a band and the body below it, and the targets its text
and non-text inks meet. -/
public structure Targets where
  body : Nat
  band : Nat
  rule : Nat
  wash : Nat
  soft : Nat
  pair : Nat
  text : Nat
  edge : Nat
  deriving Repr, BEq, Inhabited

/-- How far a generated ink stands above its WCAG 2.2 gate. -/
public def margin : Nat := 100

/-- A light page: the class's ground depth, text at 4.6:1, edges at 3.1:1. -/
@[expose] public def Targets.light (d : GroundDepth) : Targets :=
  { body := d.body, band := d.band, rule := d.rule, wash := d.body, soft := d.band,
    pair := d.pair, text := aaText + margin, edge := aaNonText + margin }

/-- A dark page: grounds stand further from a dark page to read as apart,
and text at 6.9:1, where WCAG 2's ratio understates how faint light text on
a dark ground reads — calibrated against the screen's shipped dark colours
(`Ir.Role.row`'s dark column), within ΔEOK 0.025. -/
@[expose] public def Targets.dark : Targets :=
  { body := 1190, band := 1400, rule := 1700, wash := 1120, soft := 1300, pair := 1100,
    text := 6900, edge := aaNonText + margin }

/-- Whether the paper is the darker of the two seeds. -/
@[expose] public def Seeds.dark (s : Seeds) : Bool := decide (luminance s.paper < luminance s.ink)

@[expose] public def Seeds.targets (s : Seeds) (d : GroundDepth) : Targets :=
  if s.dark then Targets.dark else Targets.light d

/-! ## Families -/

/-- A hue family: a direction `(a, b)` of length `norm` (0 on the neutral
axis), the chroma its inks take (`peak`), and how its tints' chroma grows
from `base` at the page, `kappa` thousandths per unit of lightness, up to
`peak`. Scales are `labOf`'s. -/
public structure Family where
  a : Int
  b : Int
  norm : Int
  peak : Int
  base : Int
  kappa : Int
  deriving Repr, BEq, Inhabited

/-- Oklab chroma at `labOf`'s scale, from thousandths. -/
private def milliChroma (m : Nat) : Int := (m : Int) * 10 ^ 15

public def chromaOf (c : Color) : Int := (Nat.sqrt (chromaSq (labOf c)).toNat : Int)

private def familyOf (c : Color) (peak base kappa : Int) : Family :=
  let l := labOf c
  { a := l.a, b := l.b, norm := Nat.sqrt (chromaSq l).toNat, peak, base, kappa }

/-- The neutral family: the named neutral's hue, else the paper's where it
shows one (chroma ≥ 0.003), else the ink's (≥ 0.015), else the accent's;
its inks at the source's chroma held to 0.012–0.030, or 0.020 from the
accent. A tinted paper's own chroma is where its tints start. -/
public def neutralFamily (s : Seeds) : Family :=
  let clamp (c : Int) := max (milliChroma 12) (min (milliChroma 30) c)
  match s.neutral with
  | some n => familyOf n (clamp (chromaOf n)) 0 200
  | none =>
    if milliChroma 3 ≤ chromaOf s.paper then
      familyOf s.paper (clamp (chromaOf s.paper)) (chromaOf s.paper) 200
    else if milliChroma 15 ≤ chromaOf s.ink then familyOf s.ink (clamp (chromaOf s.ink)) 0 200
    else familyOf s.accent (milliChroma 20) 0 200

/-- An accent family: the seed's own hue and chroma. -/
public def accentFamily (c : Color) : Family := familyOf c (chromaOf c) 0 800

/-- The fraction of the family's direction a chroma is. -/
private def Family.frac (fam : Family) (c : Int) : Nat :=
  if fam.norm ≤ 0 then 0 else (c * fracOne / fam.norm).toNat

/-- A tint at lightness `L` over a page at `Lp`, before gamut mapping:
chroma `base + κ·|Lp − L|` up to the peak, at the family's hue. -/
public def Family.tintRaw (fam : Family) (Lp L : Int) : Okl :=
  let d := if L ≤ Lp then Lp - L else L - Lp
  { L, a := fam.a, b := fam.b, f := fam.frac (min fam.peak (fam.base + fam.kappa * d / 1000)) }

/-- The tint, brought into the gamut at its lightness and hue. -/
public def Family.tint (fam : Family) (Lp L : Int) : Okl := (fam.tintRaw Lp L).toGamut

/-- An ink at lightness `L` before gamut mapping: the family's peak chroma;
a warm seed (`warm` = its hue and lightness) turns toward red below its own
lightness, fully a quarter of the axis down. -/
public def Family.inkRaw (fam : Family) (warm : Option (Int × Int)) (L : Int) : Okl :=
  let dir : Int × Int := match warm with
    | some (h, ls) =>
      if L < ls then turnBy (-(Okl.turn h ((ls - L) * fracOne / (25 * 10 ^ 16)).toNat)) fam.a fam.b
      else (fam.a, fam.b)
    | none => (fam.a, fam.b)
  { L, a := dir.1, b := dir.2, f := fam.frac fam.peak }

/-- The ink, brought into the gamut at its lightness and hue. -/
public def Family.ink (fam : Family) (warm : Option (Int × Int)) (L : Int) : Okl :=
  (fam.inkRaw warm L).toGamut

/-- A seed's hue and lightness, where its darker tones turn. -/
private def warmOf (c : Color) : Option (Int × Int) :=
  let l := labOf c
  some (hueMilli l.a l.b, l.L)

/-! ## Solving -/

/-- How far from the grey's lightness a tint's or an ink's boundary is
looked for first, at `labOf`'s scale: 0.06 of the axis. -/
private def guessSpan : Int := 6 * 10 ^ 16

/-- The step a quantized answer is moved by toward the passing side when
quantizing took it across the boundary: a 2⁻¹⁰ of the axis, about a quarter
of an 8-bit step. -/
private def nudge : Int := 10 ^ 18 / 1024

/-- The lightness at which the candidate's luminance meets `want` (10⁻⁷
units), by the secant method from the guess: luminance along a lightness
axis is monotone, so a few steps close the gap that a bisection would
spend a dozen on. -/
private def secant (lum : Int → Int) (want : Int) (guess : Int) : Int := Id.run do
  let mut a := guess
  let mut ya := lum a
  let mut b := guess + (if ya > want then -2 else 2) * 10 ^ 16
  let mut yb := lum b
  for _ in [0:6] do
    if yb == ya || (yb - want).natAbs ≤ 20 then break
    let next := max 0 (min (10 ^ 18) (b - (yb - want) * (b - a) / (yb - ya)))
    a := b
    ya := yb
    b := next
    yb := lum b
  return b

/-- The search over a lightness axis: the candidate at `L` (`at_`, in
gamut), the lightness where its luminance meets `want` found by `secant`,
then the quantized colour moved toward the passing side (`darker`: toward
black) until it passes `ok` itself. Where twelve nudges do not reach a
passing colour, the boundary is bisected over the whole axis instead, from
the failing end `f` to the passing end `p`. -/
private def search (at_ : Int → Okl) (want : Nat) (darker : Bool) (ok : Color → Bool)
    (f p guess : Int) : Option Color :=
  let dir : Int := if darker then -1 else 1
  let L := secant (fun L => ((at_ L).luminance : Int)) want guess
  match (List.range 13).findSome? fun (k : Nat) =>
      let c := (at_ (L + dir * nudge * Int.ofNat k)).toColor
      if ok c then some c else none with
  | some c => some c
  | none =>
    let pass := fun L => ok (at_ L).toColor
    if pass p then some (at_ (ContrastSolve.bisect pass 20 f p)).toColor else none

/-- The ground at `target` contrast to the page: lightness bisected from the
page toward the ink's side, looked for first beside the grey at that
contrast. -/
private def solveGround (fam : Family) (page : Color) (dark : Bool) (target : Nat) : Option Color :=
  let lp := (labOf page).L
  let far : Int := if dark then 10 ^ 18 else 0
  let want := ContrastSolve.luminanceAt page target dark
  search (fam.tint lp) want (!dark) (fun c => decide (target ≤ contrastMilli c page)) lp far
    (ContrastSolve.greyLightness want)

/-- The quietest tone meeting `target` on every ground: the lightness nearest
the grounds that passes on all of them, searched from white (`light`) or
from black, looked for first beside the grey the most demanding ground asks
for, at the chroma the gamut holds there. -/
private def solveInk (raw : Int → Okl) (grounds : List Color) (target : Nat) (light : Bool) :
    Option Color :=
  let (f, p) : Int × Int := if light then (10 ^ 18, 0) else (0, 10 ^ 18)
  let wants := grounds.map fun g => ContrastSolve.luminanceAt g target (!light)
  let want := if light then wants.foldl min 10000000 else wants.foldl max 0
  let guess := ContrastSolve.greyLightness want
  let cap := (raw guess).toGamut.f
  let at_ := fun L => let o := raw L; ({ o with f := min o.f cap } : Okl).toGamut
  search at_ want light (fun c => grounds.all fun g => decide (target ≤ contrastMilli c g)) f p guess

/-- A seed where it already passes on every ground, else its family's tone. -/
private def seedOr (seed : Color) (grounds : List Color) (target : Nat)
    (tone : Option Color) : Option Color :=
  if grounds.all fun g => decide (target ≤ contrastMilli seed g) then some seed else tone

/-! ## The palette -/

/-- Every derived colour of a generated palette. -/
public structure Colors where
  surface : Color
  surfaceStrong : Color
  rule : Color
  accentWash : Color
  accentSoft : Color
  muted : Color
  diagramMuted : Color
  mutedOnInverse : Color
  accentText : Color
  accentEdge : Color
  accentOnInverse : Color
  alert : Color
  alertBand : Color
  exampleText : Option Color
  exampleBand : Color
  deriving Repr, BEq, Inhabited

/-- A registry role's colour in a generated palette: the seeds as given, the
derived roles, and nothing for a role generation does not set. -/
@[expose] public def Colors.role (s : Seeds) (c : Colors) : Ir.Role → Option Color
  | .page => some s.paper
  | .ink => some s.ink
  | .accent => some s.accent
  | .muted => some c.muted
  | .alert => some c.alert
  | .example => c.exampleText
  | .focus => some c.accentEdge
  | .surface => some c.surface
  | .surfaceStrong => some c.surfaceStrong
  | .accentWash => some c.accentWash
  | .accentSoft => some c.accentSoft
  | .accentText => some c.accentText
  | .accentEdge => some c.accentEdge
  | .mutedOnInverse => some c.mutedOnInverse
  | .accentOnInverse => some c.accentOnInverse
  | .diagramMuted => some c.diagramMuted
  | .alertBandInk => some c.alertBand
  | .exampleBandInk => some c.exampleBand
  | .rule => some c.rule
  | .covered | .marker | .codeSurface | .paper | .printInk
  | .frameTitleBar | .frameTitleInk | .frameSubtitleInk | .sectionTitleInk | .footBand | .footInk
  | .blockTitleBar | .alertTitleBar | .exampleTitleBar
  | .blockTitleInk | .alertTitleInk | .exampleTitleInk
  | .blockBodyInk | .alertBodyInk | .exampleBodyInk
  | .blockBodyGround | .alertBodyGround | .exampleBodyGround
  | .standoutGround | .standoutInk | .titlePageGround | .titlePageInk | .separator
  | .progressFill | .progressTrack | .sectionProgressFill | .sectionProgressTrack
  | .codeInk | .codeKeyword | .codeName | .codeLiteral | .codeComment | .codeError => none

/-- The palette roles generation derives: every role it sets but the seeds. -/
@[expose] public def derivedRoles : List Ir.Role :=
  [.muted, .alert, .example, .rule, .focus, .surface, .surfaceStrong, .accentWash, .accentSoft,
   .accentText, .accentEdge, .mutedOnInverse, .accentOnInverse, .diagramMuted, .alertBandInk,
   .exampleBandInk]

/-- The palette roles generation sets: the seeds' three, then what it derives. -/
@[expose] public def tierRoles : List Ir.Role := [.page, .ink, .accent] ++ derivedRoles

/-- The colours a generated palette paints its furniture in, each element
role bound to the palette role it reads, in both block styles: the progress
bar in the accent over the accent's band, the title separator in the
accent. Decorative marks, so no contrast is owed; their hue is the seeds'
rather than any bundle's, the one entry point every colour comes through. -/
@[expose] public def furniture : List (Ir.Role × Ir.Role) :=
  [(.progressFill, .accent), (.progressTrack, .accentSoft), (.separator, .accent)]

/-- The element roles a block style binds, each to the palette role it reads:
the title's bar and ink and the body's ground and ink, for each kind. Under
`strong`, the alert title stands on the accent where the ink reads on it,
else on the ink in the accent's inverse tone. -/
@[expose] public def bindings (s : Seeds) (t : Targets) : Blocks → List (Ir.Role × Ir.Role)
  | .tonal =>
    [(.blockTitleBar, .surfaceStrong), (.blockTitleInk, .ink),
     (.blockBodyGround, .surface), (.blockBodyInk, .ink),
     (.alertTitleBar, .accentSoft), (.alertTitleInk, .alertBandInk),
     (.alertBodyGround, .accentWash), (.alertBodyInk, .ink),
     (.exampleTitleBar, .surfaceStrong), (.exampleTitleInk, .exampleBandInk),
     (.exampleBodyGround, .surface), (.exampleBodyInk, .ink)]
  | .strong =>
    let onAccent := decide (t.text ≤ contrastMilli s.ink s.accent)
    [(.blockTitleBar, .ink), (.blockTitleInk, .page),
     (.blockBodyGround, .accentWash), (.blockBodyInk, .ink),
     (.alertTitleBar, if onAccent then .accent else .ink),
     (.alertTitleInk, if onAccent then .ink else .accentOnInverse),
     (.alertBodyGround, .accentWash), (.alertBodyInk, .ink),
     (.exampleTitleBar, .ink), (.exampleTitleInk, .accentOnInverse),
     (.exampleBodyGround, .accentWash), (.exampleBodyInk, .ink)]

/-- The block elements beamer colours, each with the roles of its two
channels, read off the registry rows (`Row.beamer`). -/
public def beamerElements : List (String × Ir.Role × Ir.Role) :=
  [("block title", .blockTitleInk, .blockTitleBar),
   ("block title alerted", .alertTitleInk, .alertTitleBar),
   ("block title example", .exampleTitleInk, .exampleTitleBar),
   ("block body", .blockBodyInk, .blockBodyGround),
   ("block body alerted", .alertBodyInk, .alertBodyGround),
   ("block body example", .exampleBodyInk, .exampleBodyGround)]

/-- The export's block bindings: each element with the palette roles its two
channels read under the style. -/
public def beamerBlocks (s : Seeds) (t : Targets) (b : Blocks) : List (String × Ir.Role × Ir.Role) :=
  beamerElements.filterMap fun (e, fg, bg) => do
    let f ← (bindings s t b).lookup fg
    let g ← (bindings s t b).lookup bg
    pure (e, f, g)

/-- The pairs a block style paints, each a title or body ink over its
ground, read through the style's bindings. -/
public def blockPairs (s : Seeds) (t : Targets) (c : Colors) (b : Blocks) : List (Color × Color) :=
  (beamerBlocks s t b).filterMap fun (_, f, g) => do
    let cf ← Colors.role s c f
    let cg ← Colors.role s c g
    pure (cf, cg)

/-- The sites a generated palette creates: each derived ink on every ground
it stands on, with the target it owes, under the role it is reported by. -/
public def sites (s : Seeds) (t : Targets) (c : Colors) : List (Ir.Role × Color × Color × Nat) :=
  [(.ink, s.ink, s.paper, t.text), (.ink, s.ink, c.surface, t.text),
   (.ink, s.ink, c.surfaceStrong, t.text), (.ink, s.ink, c.accentWash, t.text),
   (.muted, c.muted, s.paper, t.text), (.muted, c.muted, c.surface, t.text),
   (.muted, c.muted, c.accentWash, t.text),
   (.diagramMuted, c.diagramMuted, s.paper, t.edge), (.diagramMuted, c.diagramMuted, c.surface, t.edge),
   (.diagramMuted, c.diagramMuted, c.surfaceStrong, t.edge),
   (.mutedOnInverse, c.mutedOnInverse, s.ink, t.text),
   (.accentText, c.accentText, s.paper, t.text), (.accentText, c.accentText, c.surface, t.text),
   (.accentText, c.accentText, c.accentWash, t.text),
   (.accentEdge, c.accentEdge, s.paper, t.edge), (.accentEdge, c.accentEdge, c.surface, t.edge),
   (.accentEdge, c.accentEdge, c.accentSoft, t.edge),
   (.accentOnInverse, c.accentOnInverse, s.ink, t.text),
   (.alert, c.alert, s.paper, t.text), (.alert, c.alert, c.surface, t.text),
   (.alert, c.alert, c.accentWash, t.text),
   (.alertBandInk, c.alertBand, c.accentSoft, t.text),
   (.exampleBandInk, c.exampleBand, c.surfaceStrong, t.text)] ++
  match c.exampleText with
  | some e => [(.example, e, s.paper, t.text), (.example, e, c.surface, t.text)]
  | none => []

/-- How far above its target a ground may stand: a fiftieth of the target —
0.022 at a deck body's 1.12:1, about two and a half 8-bit steps of a light
tint, the room the search's quantized answer needs — and proportionally more
near a dark page, where a step moves the ratio further. -/
public def groundSlack (target : Nat) : Nat := target / 50

/-- One 8-bit step's worth of chroma near the page, `labOf`'s scale. -/
public def chromaStep : Int := 4 * 10 ^ 15

/-- The chroma below which a tint shows no hue to hold. -/
public def hueFloor : Int := 5 * 10 ^ 15

/-- The grounds, each with its family and the ratio it is solved to. -/
public def grounds (s : Seeds) (t : Targets) (c : Colors) : List (Ir.Role × Family × Color × Nat) :=
  let n := neutralFamily s
  let a := accentFamily s.accent
  [(.surface, n, c.surface, t.body), (.surfaceStrong, n, c.surfaceStrong, t.band),
   (.rule, n, c.rule, t.rule), (.accentWash, a, c.accentWash, t.wash),
   (.accentSoft, a, c.accentSoft, t.soft)]

/-- The chroma a family's tint keeps at a ground's own lightness: what the
search asked for, after gamut mapping. -/
public def floorAt (fam : Family) (page g : Color) : Int :=
  let o := fam.tint (labOf page).L (labOf g).L
  (Nat.sqrt (chromaSq o.lab).toNat : Int)

/-- Whether a direction stands within 10° of the family's: on its side, and
its cross product at most tan 10° (0.176327) of its dot product. -/
public def withinTenDegrees (fam : Family) (g : Color) : Bool :=
  let l := labOf g
  let dot := fam.a * l.a + fam.b * l.b
  let cross := fam.a * l.b - fam.b * l.a
  decide (0 < dot) && decide ((if cross < 0 then -cross else cross) * 1000000 ≤ 176327 * dot)

/-- A ground stands in its band: its ratio within `groundSlack` of its
target, its chroma at the family's within one step, and its hue the
family's where it has chroma enough to show one. -/
public def hueOk (fam : Family) (page g : Color) : Bool :=
  decide (floorAt fam page g < hueFloor) || withinTenDegrees fam g

private theorem hueOk_within {fam : Family} {page g : Color} (h : hueOk fam page g = true)
    (hf : hueFloor ≤ floorAt fam page g) : withinTenDegrees fam g = true := by
  simp only [hueOk, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd hf (Int.not_le.mpr h)
  · exact h

public def groundOk (page : Color) (fam : Family) (g : Color) (target : Nat) : Bool :=
  decide (target ≤ contrastMilli g page) && decide (contrastMilli g page ≤ target + groundSlack target) &&
    decide (floorAt fam page g - chromaStep ≤ chromaOf g) && hueOk fam page g

/-- **The contract a generated palette carries**: every site meets its
target, every block pair of both styles reads, every ground stands in its
band, and each band stands `pair` apart from the body below it. -/
public def contract (s : Seeds) (t : Targets) (c : Colors) : Bool :=
  (sites s t c).all (fun (_, i, g, r) => decide (r ≤ contrastMilli i g)) &&
  (Blocks.all.all fun b => (blockPairs s t c b).all fun (i, g) => decide (t.text ≤ contrastMilli i g)) &&
  (grounds s t c).all (fun (_, fam, g, r) => groundOk s.paper fam g r) &&
  decide (t.pair ≤ contrastMilli c.surfaceStrong c.surface) &&
  decide (t.pair ≤ contrastMilli c.accentSoft c.accentWash)

/-- A generated palette: its colours, and the proof they meet the contract.
The seeds are parameters, never outputs the generator may change. -/
public structure Generated (s : Seeds) (t : Targets) where
  colors : Colors
  valid : contract s t colors = true

/-- Why seeds generate no palette: the role whose colour could not be found
or does not meet what its sites owe. -/
public structure Failure where
  role : Ir.Role
  detail : String
  /-- The seed is a CMYK colour, which has no sRGB tones to derive. -/
  cmyk : Bool := false
  deriving Repr, BEq

private def fail {α : Type} (role : Ir.Role) (detail : String) : Except Failure α :=
  .error { role, detail }

private def failCmyk {α : Type} (role : Ir.Role) : Except Failure α :=
  .error { role, detail := "a CMYK seed has no sRGB tones to derive", cmyk := true }

private def need {α : Type} (role : Ir.Role) (detail : String) : Option α → Except Failure α
  | some v => .ok v
  | none => fail role detail

/-- The first check a candidate palette fails, named by its role. -/
private def firstFailure (s : Seeds) (t : Targets) (c : Colors) : Option Failure :=
  let ratio (m : Nat) := s!"{m / 1000}.{(m % 1000) / 100}{(m % 100) / 10}"
  match (sites s t c).find? (fun (_, i, g, r) => !decide (r ≤ contrastMilli i g)) with
  | some (role, i, g, r) =>
    some { role, detail := s!"{ratio (contrastMilli i g)}:1 where {ratio r}:1 is owed" }
  | none =>
    match (grounds s t c).find? (fun (_, fam, g, r) => !groundOk s.paper fam g r) with
    | some (role, _, g, r) =>
      some { role, detail := s!"{ratio (contrastMilli g s.paper)}:1 to the page where {ratio r}:1 is asked" }
    | none =>
      if !decide (t.pair ≤ contrastMilli c.surfaceStrong c.surface) then
        some { role := .surfaceStrong, detail := "the band stands too near the body below it" }
      else if !decide (t.pair ≤ contrastMilli c.accentSoft c.accentWash) then
        some { role := .accentSoft, detail := "the accent's band stands too near its wash" }
      else if !(Blocks.all.all fun b => (blockPairs s t c b).all fun (i, g) =>
          decide (t.text ≤ contrastMilli i g)) then
        some { role := .alertTitleBar, detail := "a block title does not read on its bar" }
      else none

/-- Solve every derived role, in the order each one's grounds exist. -/
private def candidate (s : Seeds) (t : Targets) : Except Failure Colors := do
  let dark := s.dark
  let light := !dark
  let n := neutralFamily s
  let a := accentFamily s.accent
  let warmA := if dark then none else warmOf s.accent
  let surface ← need .surface "no neutral tint reaches the body's ratio" (solveGround n s.paper dark t.body)
  let surfaceStrong ← need .surfaceStrong "no neutral tint reaches the band's ratio"
    (solveGround n s.paper dark t.band)
  let rule ← need .rule "no neutral tint reaches the rule's ratio" (solveGround n s.paper dark t.rule)
  let accentWash ← need .accentWash "no accent tint reaches the wash's ratio"
    (solveGround a s.paper dark t.wash)
  let accentSoft ← need .accentSoft "no accent tint reaches the band's ratio"
    (solveGround a s.paper dark t.soft)
  let neutralInk := n.inkRaw none
  let accentInk := a.inkRaw warmA
  let muted ← need .muted "no neutral tone reads on the page and its fills"
    (solveInk neutralInk [s.paper, surface, accentWash] t.text light)
  let diagramMuted ← need .diagramMuted "no neutral tone stands out from the page and its fills"
    (solveInk neutralInk [s.paper, surface, surfaceStrong] t.edge light)
  let mutedOnInverse ← need .mutedOnInverse "no neutral tone reads on the ink"
    (solveInk neutralInk [s.ink] t.text dark)
  let accentText ← need .accentText "no accent tone reads on the page and its fills"
    (seedOr s.accent [s.paper, surface, accentWash] t.text
      (solveInk accentInk [s.paper, surface, accentWash] t.text light))
  let accentEdge ← need .accentEdge "no accent tone stands out from the page and its fills"
    (seedOr s.accent [s.paper, surface, accentSoft] t.edge
      (solveInk accentInk [s.paper, surface, accentSoft] t.edge light))
  let accentOnInverse ← need .accentOnInverse "no accent tone reads on the ink"
    (seedOr s.accent [s.ink] t.text (solveInk (a.inkRaw none) [s.ink] t.text dark))
  let alert ← match s.alert with
    | none => pure accentText
    | some al =>
      let fam := accentFamily al
      let warm := if dark then none else warmOf al
      need .alert "no alert tone reads on the page and its fills"
        (seedOr al [s.paper, surface, accentWash] t.text
          (solveInk (fam.inkRaw warm) [s.paper, surface, accentWash] t.text light))
  let alertFam := (s.alert.map accentFamily).getD a
  let alertWarm := if dark then none else warmOf (s.alert.getD s.accent)
  let alertBand ← need .alertBandInk "no alert tone reads on the accent's band"
    (seedOr alert [accentSoft] t.text
      (solveInk (alertFam.inkRaw alertWarm) [accentSoft] t.text light))
  let exampleText ← match s.exampleColor with
    | none => pure none
    | some ex =>
      let fam := accentFamily ex
      let warm := if dark then none else warmOf ex
      some <$> need .example "no example tone reads on the page and its fills"
        (seedOr ex [s.paper, surface] t.text
          (solveInk (fam.inkRaw warm) [s.paper, surface] t.text light))
  let exampleFam := (s.exampleColor.map accentFamily).getD n
  let exampleWarm := if dark then none else s.exampleColor.bind warmOf
  let exampleBand ← need .exampleBandInk "no example tone reads on the band"
    (seedOr (exampleText.getD muted) [surfaceStrong] t.text
      (solveInk (exampleFam.inkRaw exampleWarm) [surfaceStrong] t.text light))
  return { surface, surfaceStrong, rule, accentWash, accentSoft, muted, diagramMuted,
           mutedOnInverse, accentText, accentEdge, accentOnInverse, alert, alertBand, exampleText,
           exampleBand }

/-- **Generate a palette** from its seeds at the targets of a class's depth
and the paper's polarity. A CMYK seed is refused: this sRGB operation cannot
keep its print components. -/
public def generate (s : Seeds) (t : Targets) : Except Failure (Generated s t) := do
  if s.ink.cmyk.isSome then failCmyk .ink
  if s.paper.cmyk.isSome then failCmyk .page
  if s.accent.cmyk.isSome then failCmyk .accent
  let c ← candidate s t
  if h : contract s t c = true then return ⟨c, h⟩
  else
    match firstFailure s t c with
    | some f => .error f
    | none => fail .surface "the palette does not meet its contract"

/-! ## The class's default palette -/

/-- The seeds the engine's own screen colours are generated from where a
document declares none (`Ir.ClassColors.ink`, `.paper`, `.accent`). -/
@[expose] public def classSeeds : Seeds :=
  { ink := ClassColors.ink, paper := ClassColors.paper, accent := ClassColors.accent }

/-- A generated palette as a document keeps it: the seeds, the targets they
were generated to, the block style, and the colours, so a generated role
standing on another ground can take its family's tone there (`toneOn`). -/
public structure SeedState where
  seeds : Seeds
  targets : Targets
  blocks : Blocks
  colors : Colors
  deriving Repr, BEq, Inhabited

/-- What a generated palette derives from its seeds: each role generation
derives, at its colour. -/
@[expose] public def derivedEntries (st : SeedState) : List (Ir.Role × Color) :=
  derivedRoles.filterMap fun r => (Colors.role st.seeds st.colors r).map (r, ·)

/-- Every palette role a generated palette installs, in order: the seeds as
the page's ground, text and accent, then what is derived from them. -/
@[expose] public def entries (st : SeedState) : List (Ir.Role × Color) :=
  [(.page, st.seeds.paper), (.ink, st.seeds.ink), (.accent, st.seeds.accent)] ++
    derivedEntries st

/-- Each element role a generated palette's block style and furniture bind,
beside the palette role it reads: the element takes that role's colour as the
palette holds it once the palette roles are installed (`Ir.Palette.applySeedsUnder`). -/
@[expose] public def bound (st : SeedState) : List (Ir.Role × Ir.Role) :=
  bindings st.seeds st.targets st.blocks ++ furniture

/-- The element roles a generated palette's block style and furniture bind. -/
@[expose] public def elementRoles : List Ir.Role :=
  [.blockTitleBar, .blockTitleInk, .blockBodyGround, .blockBodyInk, .alertTitleBar,
   .alertTitleInk, .alertBodyGround, .alertBodyInk, .exampleTitleBar, .exampleTitleInk,
   .exampleBodyGround, .exampleBodyInk, .progressFill, .progressTrack, .separator]

/-- The element roles a block style and the furniture bind, in either style. -/
public theorem bound_elements (s : Seeds) (t : Targets) (b : Blocks) :
    (bindings s t b ++ furniture).map Prod.fst = elementRoles := by
  cases b <;> rfl

/-- **No binding rewrites a seed**: the element roles a block style and the
furniture bind are never the page's text, ground or accent. -/
public theorem bindings_seeds_exact (s : Seeds) (t : Targets) (b : Blocks) :
    ∀ x ∈ bindings s t b ++ furniture, x.1 ≠ .ink ∧ x.1 ≠ .page ∧ x.1 ≠ .accent := by
  intro x hx
  have hm := List.mem_map_of_mem (f := Prod.fst) hx
  rw [bound_elements] at hm
  have hall : ∀ r ∈ elementRoles, r ≠ .ink ∧ r ≠ .page ∧ r ≠ .accent := by decide
  exact hall _ hm

/-- **The seeds ship exactly**: after the seeds, a generated palette derives
and binds nothing that names the page's text, ground or accent, so what it
installs for those three roles is the author's colours
(`Ir.Palette.applySeedsUnder_seeds_exact` reads it off the install). -/
public theorem generate_seeds_exact (st : SeedState) :
    (∀ x ∈ derivedEntries st, x.1 ≠ .ink ∧ x.1 ≠ .page ∧ x.1 ≠ .accent) ∧
      ∀ x ∈ bound st, x.1 ≠ .ink ∧ x.1 ≠ .page ∧ x.1 ≠ .accent := by
  refine ⟨fun x hx => ?_, bindings_seeds_exact st.seeds st.targets st.blocks⟩
  obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp hx
  obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp he
  have hall : ∀ r ∈ derivedRoles, r ≠ .ink ∧ r ≠ .page ∧ r ≠ .accent := by decide
  exact hall r hr

/-- Whether a ground is the light side: white stands less apart from it than black. -/
private def lightGround (g : Color) : Bool :=
  decide (contrastMilli Color.white g < contrastMilli Color.black g)

/-- A generated text role on a ground it does not read on: on the ink, the
inverse ink generation already holds, under its own role; on any other
ground, its family's quietest tone that reads there. Only the roles text is
set in re-tone: the alert, the muted step, the example. -/
public def SeedState.toneOn (st : SeedState) (r : Ir.Role) (g : Color) :
    Option (Color × Option Ir.Role) :=
  let s := st.seeds
  let solve (fam : Family) (warm : Option (Int × Int)) : Option Color :=
    let light := lightGround g
    solveInk (fam.inkRaw (if light then warm else none)) [g] st.targets.text light
  match r with
  | .alert =>
    if g == s.ink && s.alert.isNone then some (st.colors.accentOnInverse, some .accentOnInverse)
    else (solve ((s.alert.map accentFamily).getD (accentFamily s.accent))
      (warmOf (s.alert.getD s.accent))).map fun c => (c, none)
  | .muted =>
    if g == s.ink then some (st.colors.mutedOnInverse, some .mutedOnInverse)
    else (solve (neutralFamily s) none).map fun c => (c, none)
  | .example =>
    (s.exampleColor.bind fun ex => solve (accentFamily ex) (warmOf ex)).map fun c => (c, none)
  | _ => none

/-! ## What a generated palette guarantees -/

private theorem contract_parts {s : Seeds} {t : Targets} {c : Colors} (h : contract s t c = true) :
    (sites s t c).all (fun (_, i, g, r) => decide (r ≤ contrastMilli i g)) = true ∧
    (Blocks.all.all fun b => (blockPairs s t c b).all fun (i, g) =>
      decide (t.text ≤ contrastMilli i g)) = true ∧
    (grounds s t c).all (fun (_, fam, g, r) => groundOk s.paper fam g r) = true ∧
    t.pair ≤ contrastMilli c.surfaceStrong c.surface ∧
    t.pair ≤ contrastMilli c.accentSoft c.accentWash := by
  simp only [contract, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **Every site a generated palette creates meets its target**, in both
block styles: each derived ink on each ground it stands on, and each block
title and body over its ground — 0.10 above WCAG 2.2's gate. -/
public theorem generated_sites_contract {s : Seeds} {t : Targets} (p : Generated s t) :
    (∀ x ∈ sites s t p.colors, x.2.2.2 ≤ contrastMilli x.2.1 x.2.2.1) ∧
      ∀ b : Blocks, ∀ x ∈ blockPairs s t p.colors b, t.text ≤ contrastMilli x.1 x.2 := by
  obtain ⟨h1, h2, -, -, -⟩ := contract_parts p.valid
  refine ⟨fun x hx => ?_, fun b x hx => ?_⟩
  · have := List.all_eq_true.mp h1 x hx
    exact of_decide_eq_true this
  · have hb := List.all_eq_true.mp h2 b (by cases b <;> simp [Blocks.all])
    exact of_decide_eq_true (List.all_eq_true.mp hb x hx)

/-- **Each ground stands in its band**: at least its target ratio to the
page and at most `groundSlack` above it, with the chroma its family's tint
keeps at its lightness, less one 8-bit step. -/
public theorem tint_between {s : Seeds} {t : Targets} (p : Generated s t) :
    ∀ x ∈ grounds s t p.colors,
      x.2.2.2 ≤ contrastMilli x.2.2.1 s.paper ∧
        contrastMilli x.2.2.1 s.paper ≤ x.2.2.2 + groundSlack x.2.2.2 ∧
        floorAt x.2.1 s.paper x.2.2.1 - chromaStep ≤ chromaOf x.2.2.1 := by
  obtain ⟨-, -, h3, -, -⟩ := contract_parts p.valid
  intro x hx
  have := List.all_eq_true.mp h3 x hx
  simp only [groundOk, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2⟩

/-- **A block's title band stands apart from its body**, at least `pair` to
one between the neutral band and body and between the accent's band and
wash, and each holds its family's hue within 10° wherever it has the chroma
to show one. -/
public theorem blockPair_between {s : Seeds} {t : Targets} (p : Generated s t) :
    t.pair ≤ contrastMilli p.colors.surfaceStrong p.colors.surface ∧
      t.pair ≤ contrastMilli p.colors.accentSoft p.colors.accentWash ∧
      ∀ x ∈ grounds s t p.colors,
        hueFloor ≤ floorAt x.2.1 s.paper x.2.2.1 → withinTenDegrees x.2.1 x.2.2.1 = true := by
  obtain ⟨-, -, h3, h4, h5⟩ := contract_parts p.valid
  refine ⟨h4, h5, fun x hx hf => ?_⟩
  have := List.all_eq_true.mp h3 x hx
  simp only [groundOk, Bool.and_eq_true] at this
  exact hueOk_within this.2 hf

/-! ## The TeX export -/

private theorem beamerBlocks_pair {s : Seeds} {t : Targets} {c : Colors} {b : Blocks}
    {element : String} {fg bg : Ir.Role} (h : (element, fg, bg) ∈ beamerBlocks s t b)
    {cf cg : Color} (hf : Colors.role s c fg = some cf) (hg : Colors.role s c bg = some cg) :
    (cf, cg) ∈ blockPairs s t c b :=
  List.mem_filterMap.mpr ⟨(element, fg, bg), h, by simp [hf, hg]⟩

/-- Every beamer element the generated palette writes, in first-written
order, with the roles its two channels read: each generated role's own
elements (`Row.beamer`), then each element role its block style and its
furniture bind, at the role it reads. -/
public def beamerChannels (st : SeedState) : List (String × Option Ir.Role × Option Ir.Role) :=
  let writes : List (String × Ir.Channel × Ir.Role) :=
    (tierRoles.filter fun r => (Colors.role st.seeds st.colors r).isSome).flatMap
        (fun r => r.row.beamer.map fun (e, ch) => (e, ch, r)) ++
      (bindings st.seeds st.targets st.blocks ++ furniture).flatMap fun (el, src) =>
        el.row.beamer.map fun (e, ch) => (e, ch, src)
  writes.foldl (fun acc (e, ch, r) =>
    match acc.find? (·.1 == e) with
    | some _ => acc.map fun row => if row.1 != e then row else
        match ch with
        | .fg => (e, some r, row.2.2)
        | .bg => (e, row.2.1, some r)
    | none => acc ++ [match ch with
        | .fg => (e, some r, none)
        | .bg => (e, none, some r)]) []

/-- **The export**: an xcolor colour for each role the registry names for
export (`Row.exportName`), in registry order, at its generated colour — the
print projection a TeX build reads. -/
public def declarations (stem : String) (st : SeedState) : String :=
  String.join (Ir.Role.all.filterMap fun r => do
    let n ← r.row.exportName
    let c ← Colors.role st.seeds st.colors r
    pure ("\\definecolor{" ++ stem ++ n ++ "}{HTML}{" ++ Color.hexByte c.r ++ Color.hexByte c.g ++
      Color.hexByte c.b ++ "}\n"))

/-- The export with every beamer element the palette writes bound to the
colours its channels read (`beamerChannels`): the page's text and ground,
the canvas, the muted footline and its page number, the alert, the six block
elements in the style, the progress bar and the title separator. -/
public def beamerDeclarations (stem : String) (st : SeedState) : String :=
  let name (r : Ir.Role) := stem ++ r.row.exportName.getD ""
  declarations stem st ++ String.join ((beamerChannels st).map fun (e, fg, bg) =>
    let parts := (fg.map fun r => "fg=" ++ name r).toList ++ (bg.map fun r => "bg=" ++ name r).toList
    "\\setbeamercolor{" ++ e ++ "}{" ++ ",".intercalate parts ++ "}\n")

/-- **Every exported block binding reads**, in both styles: its foreground
over its ground meets the generated text target, at least WCAG 2.2's 4.5:1. -/
public theorem generated_beamer_contract {s : Seeds} {t : Targets} (p : Generated s t)
    (ht : aaText ≤ t.text) (b : Blocks) {element : String} {fg bg : Ir.Role}
    (h : (element, fg, bg) ∈ beamerBlocks s t b) {cf cg : Color}
    (hf : Colors.role s p.colors fg = some cf) (hg : Colors.role s p.colors bg = some cg) :
    aaText ≤ contrastMilli cf cg :=
  Nat.le_trans ht ((generated_sites_contract p).2 b _ (beamerBlocks_pair h hf hg))

end LeanTex.Core.SeedPalette
