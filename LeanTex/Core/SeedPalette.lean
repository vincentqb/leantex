module

public import LeanTex.Core.Color
public import LeanTex.Core.DesignRole
public import LeanTex.Core.ContrastRatio
public import LeanTex.Core.Oklab
import LeanTex.Core.ContrastSolve

/-! A palette generated from its seeds: ink, paper and accent shipped exactly, every other role
derived in Oklab by stated rules (Radix's gray pairing, Tailwind's chroma growth, Material 3's
tonal rule) at its use's floor in its medium, or its cover's edge (WCAG 2.2), checked against it. -/

namespace LeanTex.Core.SeedPalette

open Ir Oklab Contrast

/-- The colours an author names: ink, paper and accent shipped exactly, and optional alert,
example and neutral families. -/
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

/-- The ratios a palette is generated to, ×1000: its grounds' to the page, a band's to its body,
text's on the page (`text`) and on the ink (`inverse`), marks' (`edge`), the medium's text floor the
more scheme leaves standing (`floor`), and the share its medium covers pending steps at (`cover`). -/
public structure Targets where
  body : Nat
  band : Nat
  rule : Nat
  wash : Nat
  soft : Nat
  pair : Nat
  text : Nat
  inverse : Nat
  edge : Nat
  floor : Nat
  cover : Option Nat := none
  deriving Repr, BEq, Inhabited

/-- How far a generated ink on a dark page, or on the ink, stands above its WCAG 2.2 gate, past
`contrastMilli`'s truncation of up to 0.007. -/
public def margin : Nat := 100

/-- A light page: the class's ground depth, text and marks at the medium's floors themselves
(WCAG 2.2 SC 1.4.3, SC 1.4.11), and text on the ink at 4.6:1, where WCAG 2 understates how faint
light text on a dark ground reads. -/
@[expose] public def Targets.light (d : GroundDepth) : Targets :=
  { body := d.body, band := d.band, rule := d.rule, wash := d.body, soft := d.band,
    pair := d.pair, text := d.text, inverse := aaText + margin, edge := aaNonText, floor := d.text }

/-- A dark page: grounds further apart, and text at 6.5:1, where WCAG 2 understates how faint
light text on a dark ground reads; the values are calibrated to the screen `Tests.Schemes` holds. -/
@[expose] public def Targets.dark : Targets :=
  { body := 1190, band := 1400, rule := 1700, wash := 1120, soft := 1300, pair := 1100,
    text := 6500, inverse := 6500, edge := aaNonText + margin, floor := 6500 }

/-- The same polarity where the reader asks more contrast: text at SC 1.4.6's 7:1 and edges at
4.5:1, each plus `margin`, rules at 3:1. -/
@[expose] public def Targets.more (t : Targets) : Targets :=
  { t with
    rule := 3000, text := aaaText + margin, inverse := aaaText + margin, edge := moreNonText + margin }

/-- Whether the paper is the darker of the two seeds. -/
@[expose] public def Seeds.dark (s : Seeds) : Bool := decide (luminance s.paper < luminance s.ink)

@[expose] public def Seeds.targets (s : Seeds) (d : GroundDepth) : Targets :=
  if s.dark then Targets.dark else Targets.light d

/-- The targets in a scheme: the polarity's, more where the scheme asks it. -/
@[expose] public def Seeds.targetsIn (s : Seeds) (d : GroundDepth) (sc : Ir.Scheme) : Targets :=
  if sc.more then (s.targets d).more else s.targets d

/-- A hue family at `labOf`'s scales: a direction `(a, b)` of length `norm`, its inks' chroma
`peak`, and its tints' chroma growing from `base` by `kappa` per unit of lightness. -/
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

/-- The neutral family: the named neutral's hue, else the paper's where it shows one (chroma
≥ 0.003), else the ink's (≥ 0.015), else the accent's. -/
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

/-- The family an accent's tints take: its own, and on a dark page, whose tints of a yellow-green
are dark ones of the disliked region, its hue's past the region's warm edge. -/
public def tintFamily (s : Seeds) : Family :=
  accentFamily (if s.dark then ContrastSolve.turnPast s.accent else s.accent)

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

/-- The step a quantized answer is moved by toward the passing side when
quantizing took it across the boundary: a 2⁻¹⁰ of the axis, about a quarter
of an 8-bit step. -/
private def nudge : Int := lightTop / 1024

/-- The lightness where the candidate's luminance meets `want` (10⁻⁷ units), by the secant
method. -/
private def secant (lum : Int → Int) (want : Int) (guess : Int) : Int := Id.run do
  let mut a := guess
  let mut ya := lum a
  let mut b := guess + (if ya > want then -2 else 2) * 10 ^ 16
  let mut yb := lum b
  for _ in [0:6] do
    if yb == ya || (yb - want).natAbs ≤ 20 then break
    let next := max 0 (min lightTop (b - (yb - want) * (b - a) / (yb - ya)))
    a := b
    ya := yb
    b := next
    yb := lum b
  return b

/-- The search along a lightness axis: the secant's answer nudged toward the passing side, else
bisected over the whole axis. -/
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
  let far : Int := if dark then lightTop else 0
  let want := ContrastSolve.luminanceAt page target dark
  search (fam.tint lp) want (!dark) (fun c => decide (target ≤ contrastMilli c page)) lp far
    (ContrastSolve.greyLightness want)

/-- The quietest tone meeting `target` on every ground and passing `ok`, searched from white
(`light`) or black. -/
private def solveInk (raw : Int → Okl) (grounds : List Color) (target : Nat) (light : Bool)
    (ok : Color → Bool := fun _ => true) : Option Color :=
  let (f, p) : Int × Int := if light then (lightTop, 0) else (0, lightTop)
  let wants := grounds.map fun g => ContrastSolve.luminanceAt g target (!light)
  let want := if light then wants.foldl min 10000000 else wants.foldl max 0
  let guess := ContrastSolve.greyLightness want
  let cap := (raw guess).toGamut.f
  let at_ := fun L => let o := raw L; ({ o with f := min o.f cap } : Okl).toGamut
  search at_ want light (fun c => (grounds.all fun g => decide (target ≤ contrastMilli c g)) && ok c)
    f p guess

/-- A seed where it already passes on every ground, shipped exactly, else its family's tone. -/
private def seedOr (seed : Color) (grounds : List Color) (target : Nat)
    (tone : Option Color) : Option Color :=
  if grounds.all fun g => decide (target ≤ contrastMilli seed g) then some seed else tone

/-- The ratio the ink reads at on a container's mark: the more scheme's text target, so one mark
reads in every light scheme. -/
public def markInk : Nat := aaaText + margin

/-- Whether the accent serves a light page as a container, as Material 3's Fidelity keeps its source
colour: no alert seed is named, the accent fails the medium's text floor on the paper, its own tone
there would be disliked or keep under half its chroma, and the ink reads on it at `markInk`. -/
public def Seeds.container (s : Seeds) (t : Targets) : Bool :=
  !s.dark && s.alert.isNone && !decide (t.floor ≤ contrastMilli s.accent s.paper) &&
    decide (markInk ≤ contrastMilli s.ink s.accent) &&
    match solveInk ((accentFamily s.accent).inkRaw none) [s.paper] t.floor true with
    | some c => ContrastSolve.disliked c || decide (2 * chromaOf c < chromaOf s.accent)
    | none => true

/-- How far a text tone's sRGB covered forms stand above 3:1, for the channel rounding a renderer
composites them with. -/
public def srgbSlack : Nat := 10

/-- The 8-bit alpha a browser composites an opacity of `pct`% with. -/
public def alphaOf (pct : Nat) : Nat := (pct * 255 + 50) / 100

/-- Whether a text tone keeps the covered-state contract at a cover share on a page in each covered
form the artifacts show: mixed toward the page in Oklab, as the PDF covers and `W0345` judges, and
in sRGB, as beamer's transparency and a browser's 8-bit opacity cover, `srgbSlack` above. -/
public def coverKept (share : Option Nat) (page c : Color) : Bool :=
  share.all fun f => coverHolds page c (Oklab.cover f page c) &&
    coverHolds page c (c.mixSrgb f page) (aaNonText + srgbSlack) &&
    coverHolds page c (c.overSrgb (alphaOf f) 255 page) (aaNonText + srgbSlack)

/-- The targets at a depth under the cover share a document declares, where its medium covers
pending steps and the share shows them. -/
@[expose] public def Seeds.targetsAt (s : Seeds) (d : GroundDepth) (share : Option Nat) : Targets :=
  { s.targets d with cover := if d.stage then share.filter (0 < ·) else none }

/-- The cover share a palette's derived text keeps: its targets', where the tone search's passing
end, black on a light page and white on a dark one, keeps it. -/
public def Seeds.coverOf (s : Seeds) (t : Targets) : Option Nat :=
  let far := if s.dark then Color.white else Color.black
  if coverKept t.cover s.paper far then t.cover else none

/-- Whether a colour is one of the seeds a palette ships exactly as text. -/
public def Seeds.textSeed (s : Seeds) (c : Color) : Bool :=
  c == s.ink || c == s.accent || s.alert == some c || s.exampleColor == some c

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
  /-- The ground an alert stands on where the accent serves the page as a
  container (`Seeds.container`): the accent itself. -/
  alertMark : Option Color := none
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
  | .alertMark => c.alertMark
  | .covered | .marker | .codeSurface | .paper | .printInk
  | .frameTitleBar | .frameTitleInk | .frameSubtitleInk | .sectionTitleInk | .footBand | .footInk
  | .blockTitleBar | .alertTitleBar | .exampleTitleBar
  | .blockTitleInk | .alertTitleInk | .exampleTitleInk
  | .blockBodyInk | .alertBodyInk | .exampleBodyInk
  | .blockBodyGround | .alertBodyGround | .exampleBodyGround
  | .standoutGround | .standoutInk | .titlePageGround | .titlePageInk | .separator
  | .progressFill | .progressTrack | .sectionProgressFill | .sectionProgressTrack
  | .codeInk | .codeKeyword | .codeName | .codeLiteral | .codeComment | .codeError => none

/-- A registry role's colour among the seeds alone: the page's ground, text
and accent, and nothing for a role generation derives. -/
@[expose] public def seedRole (s : Seeds) : Ir.Role → Option Color
  | .page => some s.paper
  | .ink => some s.ink
  | .accent => some s.accent
  | .muted | .alert | .example | .covered | .marker | .codeSurface | .rule | .focus
  | .surface | .surfaceStrong | .accentWash | .accentSoft | .accentText | .accentEdge
  | .mutedOnInverse | .accentOnInverse | .diagramMuted | .alertBandInk | .exampleBandInk
  | .paper | .printInk
  | .frameTitleBar | .frameTitleInk | .frameSubtitleInk | .sectionTitleInk | .footBand | .footInk
  | .blockTitleBar | .alertTitleBar | .exampleTitleBar
  | .blockTitleInk | .alertTitleInk | .exampleTitleInk
  | .blockBodyInk | .alertBodyInk | .exampleBodyInk
  | .blockBodyGround | .alertBodyGround | .exampleBodyGround
  | .standoutGround | .standoutInk | .titlePageGround | .titlePageInk | .separator
  | .progressFill | .progressTrack | .sectionProgressFill | .sectionProgressTrack
  | .codeInk | .codeKeyword | .codeName | .codeLiteral | .codeComment | .codeError
  | .alertMark => none

/-- The palette roles generation derives: every role it sets but the seeds. -/
@[expose] public def derivedRoles : List Ir.Role :=
  [.muted, .alert, .example, .rule, .focus, .surface, .surfaceStrong, .accentWash, .accentSoft,
   .accentText, .accentEdge, .mutedOnInverse, .accentOnInverse, .diagramMuted, .alertBandInk,
   .exampleBandInk, .alertMark]

/-- The palette roles generation sets: the seeds' three, then what it derives. -/
@[expose] public def tierRoles : List Ir.Role := [.page, .ink, .accent] ++ derivedRoles

/-- The furniture's element roles bound to the palette roles they read: the progress bar and the
title separator in the accent. -/
@[expose] public def furniture : List (Ir.Role × Ir.Role) :=
  [(.progressFill, .accent), (.progressTrack, .accentSoft), (.separator, .accent)]

/-- The element roles a block style binds, each to the palette role it reads. -/
@[expose] public def bindings (s : Seeds) (t : Targets) : Blocks → List (Ir.Role × Ir.Role)
  | .tonal =>
    [(.blockTitleBar, .surfaceStrong), (.blockTitleInk, .ink),
     (.blockBodyGround, .surface), (.blockBodyInk, .ink),
     (.alertTitleBar, .accentSoft), (.alertTitleInk, .alertBandInk),
     (.alertBodyGround, .accentWash), (.alertBodyInk, .ink),
     (.exampleTitleBar, .surfaceStrong), (.exampleTitleInk, .exampleBandInk),
     (.exampleBodyGround, .surface), (.exampleBodyInk, .ink)]
  | .strong =>
    let onAccent := decide (t.inverse ≤ contrastMilli s.ink s.accent)
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

/-- The grounds an ink facing the page is solved on: the paper, and on a dark page its fills too,
a light page's fills taking their family's tone at use (`SeedState.toneOn`). -/
public def facing (s : Seeds) (fills : List Color) : List Color :=
  s.paper :: (if s.dark then fills else [])

/-- The sites a generated palette creates: each derived ink on every ground
it stands on, with the target it owes, under the role it is reported by. -/
public def sites (s : Seeds) (t : Targets) (c : Colors) : List (Ir.Role × Color × Color × Nat) :=
  let face (r : Ir.Role) (i : Color) (fills : List Color) (target : Nat) :
      List (Ir.Role × Color × Color × Nat) :=
    (facing s fills).map fun g => (r, i, g, target)
  [(.ink, s.ink, s.paper, t.text), (.ink, s.ink, c.surface, t.text),
   (.ink, s.ink, c.surfaceStrong, t.text), (.ink, s.ink, c.accentWash, t.text)] ++
  face .muted c.muted [c.surface, c.accentWash] t.text ++
  face .diagramMuted c.diagramMuted [c.surface, c.surfaceStrong] t.edge ++
  [(.mutedOnInverse, c.mutedOnInverse, s.ink, t.inverse)] ++
  face .accentText c.accentText [c.surface, c.accentWash] t.text ++
  face .accentEdge c.accentEdge [c.surface, c.accentSoft] t.edge ++
  [(.accentOnInverse, c.accentOnInverse, s.ink, t.inverse)] ++
  face .alert c.alert [c.surface, c.accentWash] t.text ++
  [(.alertBandInk, c.alertBand, c.accentSoft, t.text),
   (.exampleBandInk, c.exampleBand, c.surfaceStrong, t.text)] ++
  (match c.exampleText with
   | some e => face .example e [c.surface] t.text
   | none => []) ++
  match c.alertMark with
  | some m => [(.alert, c.alert, m, max aaText t.text)]
  | none => []

/-- How far above its target a ground may stand: a fiftieth of the target. -/
public def groundSlack (target : Nat) : Nat := target / 50

/-- One 8-bit step's worth of chroma near the page, `labOf`'s scale. -/
public def chromaStep : Int := 4 * 10 ^ 15

/-- The chroma below which a tint shows no hue to hold. -/
public def hueFloor : Int := 5 * 10 ^ 15

/-- The grounds, each with its family and the ratio it is solved to. -/
public def grounds (s : Seeds) (t : Targets) (c : Colors) : List (Ir.Role × Family × Color × Nat) :=
  let n := neutralFamily s
  let a := tintFamily s
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

/-- The text tones the cover binds: the accent's text, the alert and the example's text where the
generator derives them, a seed shipping as given. -/
public def coverTones (s : Seeds) (c : Colors) : List Color :=
  ([c.accentText, c.alert] ++ c.exampleText.toList).filter (!s.textSeed ·)

/-- The contract a generated palette carries: every site meets its target, every block pair reads,
every ground stands in its band, and the covered text keeps its cover's contract. -/
public def contract (s : Seeds) (t : Targets) (c : Colors) : Bool :=
  (sites s t c).all (fun (_, i, g, r) => decide (r ≤ contrastMilli i g)) &&
  (Blocks.all.all fun b => (blockPairs s t c b).all fun (i, g) => decide (t.text ≤ contrastMilli i g)) &&
  (grounds s t c).all (fun (_, fam, g, r) => groundOk s.paper fam g r) &&
  decide (t.pair ≤ contrastMilli c.surfaceStrong c.surface) &&
  decide (t.pair ≤ contrastMilli c.accentSoft c.accentWash) &&
  (coverTones s c).all (coverKept (s.coverOf t) s.paper)

/-- A generated palette: its colours and the proof they meet the contract. -/
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
      else
        let tones := [(Ir.Role.accentText, some c.accentText), (.alert, some c.alert),
          (.example, c.exampleText)]
        let fails (x : Color) : Bool := !s.textSeed x && !coverKept (s.coverOf t) s.paper x
        (tones.find? fun (_, x) => x.any fails).map fun (role, _) =>
          { role, detail := "its covered form stands under 3:1 from it, or as loud on the page" }

/-- A colour's OKLCH hue, in millidegrees. -/
private def hueOf (c : Color) : Int :=
  let l := labOf c
  hueMilli l.a l.b

/-- A tone out of the disliked region: the warm-turned one, else the family's own hue's, else, where
one of them was disliked, the seed's hue past the region's warm edge at the floor (`bandClear`). -/
private def undisliked (turned own : Option Color) (cleared : Unit → Option Color) : Option Color :=
  let ok := fun c => !ContrastSolve.disliked c
  ((turned.filter ok).orElse fun _ => own.filter ok).orElse fun _ =>
    if turned.isSome || own.isSome then cleared () else none

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
    (solveGround (tintFamily s) s.paper dark t.wash)
  let accentSoft ← need .accentSoft "no accent tint reaches the band's ratio"
    (solveGround (tintFamily s) s.paper dark t.soft)
  let neutralInk := n.inkRaw none
  let toneAt (lightG : Bool) (seed : Option Color) (fam : Family) (warm : Option (Int × Int))
      (gs : List Color) (target : Nat) (ok : Color → Bool) : Option Color :=
    undisliked (solveInk (fam.inkRaw warm) gs target lightG ok)
      (solveInk (fam.inkRaw none) gs target lightG ok)
      fun _ => seed.bind fun c => ContrastSolve.bandClear target gs (hueOf c) ok
  let tone := toneAt light
  let any : Color → Bool := fun _ => true
  let kept := coverKept (s.coverOf t) s.paper
  let muted ← need .muted "no neutral tone reads on the page and its fills"
    (solveInk neutralInk (facing s [surface, accentWash]) t.text light)
  let diagramMuted ← need .diagramMuted "no neutral tone stands out from the page and its fills"
    (solveInk neutralInk (facing s [surface, surfaceStrong]) t.edge light)
  let mutedOnInverse ← need .mutedOnInverse "no neutral tone reads on the ink"
    (solveInk neutralInk [s.ink] t.inverse dark)
  let container := s.container t
  let accentText ← if container then pure s.ink else
    need .accentText "no accent tone reads on the page and its fills"
      (seedOr s.accent (facing s [surface, accentWash]) t.text
        (tone (some s.accent) a warmA (facing s [surface, accentWash]) t.text kept))
  let accentEdge ← if container then pure s.ink else
    need .accentEdge "no accent tone stands out from the page and its fills"
      (seedOr s.accent (facing s [surface, accentSoft]) t.edge
        (tone (some s.accent) a warmA (facing s [surface, accentSoft]) t.edge any))
  let accentOnInverse ← need .accentOnInverse "no accent tone reads on the ink"
    (seedOr s.accent [s.ink] t.inverse (toneAt dark (some s.accent) a none [s.ink] t.inverse any))
  let alert ← match s.alert with
    | none => pure accentText
    | some al =>
      let fam := accentFamily al
      let warm := if dark then none else warmOf al
      need .alert "no alert tone reads on the page and its fills"
        (seedOr al (facing s [surface, accentWash]) t.text
          (tone (some al) fam warm (facing s [surface, accentWash]) t.text kept))
  let alertFam := (s.alert.map accentFamily).getD a
  let alertWarm := if dark then none else warmOf (s.alert.getD s.accent)
  let alertBand ← if container then pure s.ink else
    need .alertBandInk "no alert tone reads on the accent's band"
      (seedOr alert [accentSoft] t.text
        (tone (some (s.alert.getD s.accent)) alertFam alertWarm [accentSoft] t.text any))
  let exampleText ← match s.exampleColor with
    | none => pure none
    | some ex =>
      let fam := accentFamily ex
      let warm := if dark then none else warmOf ex
      some <$> need .example "no example tone reads on the page and its fills"
        (seedOr ex (facing s [surface]) t.text (tone (some ex) fam warm (facing s [surface]) t.text kept))
  let exampleFam := (s.exampleColor.map accentFamily).getD n
  let exampleWarm := if dark then none else s.exampleColor.bind warmOf
  let exampleBand ← need .exampleBandInk "no example tone reads on the band"
    (seedOr (exampleText.getD muted) [surfaceStrong] t.text
      (tone s.exampleColor exampleFam exampleWarm [surfaceStrong] t.text any))
  return { surface, surfaceStrong, rule, accentWash, accentSoft, muted, diagramMuted,
           mutedOnInverse, accentText, accentEdge, accentOnInverse, alert, alertBand, exampleText,
           exampleBand, alertMark := if container then some s.accent else none }

/-- Generate a palette from its seeds at the given targets; a CMYK seed is refused. -/
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

/-- The secondary ink an ink and page derive, by a generated palette's muted rule at a document's
floor, which a bundle meets in whichever class installs it. -/
public def mutedFor (ink paper : Color) : Option Color :=
  let s : Seeds := { ink, paper, accent := ink }
  solveInk ((neutralFamily s).inkRaw none) [paper] (s.targets .documents).text (!s.dark)

/-- The seeds the engine's own colours are generated from where a document declares none. -/
@[expose] public def classSeeds : Seeds :=
  { ink := ClassColors.ink, paper := ClassColors.paper, accent := ClassColors.accent }

/-- The lightness of a dark screen's page, 0.20 at `labOf`'s scale, and the
most chroma it keeps, 0.012: a near-neutral of the document's own hue. -/
public def darkPageL : Int := 2 * 10 ^ 17

public def darkPageChroma : Int := 12 * 10 ^ 15

/-- The page a scheme of the other polarity stands on: a dark near-neutral of the seeds' hue,
or white. -/
public def schemePaper (s : Seeds) (dark : Bool) : Color :=
  if dark then
    let fam := neutralFamily s
    let f := fam.frac (min fam.peak darkPageChroma)
    (Okl.toGamut { L := darkPageL, a := fam.a, b := fam.b, f }).toColor
  else ClassColors.paper

/-- Seeds carried to a scheme of the given polarity; `none` where a text seed has no legible
tone there. -/
public def Seeds.carry (s : Seeds) (dark : Bool) : Option Seeds :=
  if s.dark == dark then some s else
  let paper := schemePaper s dark
  let text (c : Color) := ContrastSolve.adapt (aaText + margin) s.paper paper c paper
  let named (c : Option Color) : Option (Option Color) := match c with
    | some c => (text c).map some
    | none => some none
  match text s.ink, named s.alert, named s.exampleColor with
  | some ink, some alert, some exampleColor =>
    some { ink, paper, accent := ContrastSolve.undislike (ContrastSolve.reflect s.paper paper s.accent)
           alert := alert.map ContrastSolve.undislike, exampleColor := exampleColor.map ContrastSolve.undislike
           neutral := s.neutral.map (ContrastSolve.reflect s.paper paper) }
  | _, _, _ => none

/-- The class's default seeds as a scheme carries them: as they are on the
printed page and a light screen, carried to a dark page on a dark one. -/
public def classSeedsIn (s : Ir.Scheme) : Seeds :=
  if s.onDark then (classSeeds.carry true).getD classSeeds else classSeeds

/-- A generated palette as a document keeps it: seeds, targets, block style and colours, and
whether a bundle generated it. -/
public structure SeedState where
  seeds : Seeds
  targets : Targets
  blocks : Blocks
  colors : Colors
  bundle : Bool := false
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

public theorem bound_elements (s : Seeds) (t : Targets) (b : Blocks) :
    (bindings s t b ++ furniture).map Prod.fst = elementRoles := by
  cases b <;> rfl

public theorem bindings_seeds_exact (s : Seeds) (t : Targets) (b : Blocks) :
    ∀ x ∈ bindings s t b ++ furniture, x.1 ≠ .ink ∧ x.1 ≠ .page ∧ x.1 ≠ .accent := by
  intro x hx
  have hm := List.mem_map_of_mem (f := Prod.fst) hx
  rw [bound_elements] at hm
  have hall : ∀ r ∈ elementRoles, r ≠ .ink ∧ r ≠ .page ∧ r ≠ .accent := by decide
  exact hall _ hm

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

/-- A generated text role's tone on a ground it does not read on: the inverse ink, or its family's
quietest legible tone, out of the disliked region. -/
public def SeedState.toneOn (st : SeedState) (r : Ir.Role) (g : Color) :
    Option (Color × Option Ir.Role) :=
  let s := st.seeds
  let light := lightGround g
  let solve (seed : Option Color) (fam : Family) (warm : Option (Int × Int)) : Option Color :=
    let at_ (w : Option (Int × Int)) := solveInk (fam.inkRaw (if light then w else none)) [g]
      st.targets.text light
    undisliked (at_ warm) (at_ none) fun _ =>
      seed.bind fun c => ContrastSolve.bandClear st.targets.text [g] (hueOf c)
  match r with
  | .alert =>
    if g == s.ink && s.alert.isNone then some (st.colors.accentOnInverse, some .accentOnInverse)
    else (solve (some (s.alert.getD s.accent)) ((s.alert.map accentFamily).getD (accentFamily s.accent))
      (warmOf (s.alert.getD s.accent))).map fun c => (c, none)
  | .muted =>
    if g == s.ink then some (st.colors.mutedOnInverse, some .mutedOnInverse)
    else (solve none (neutralFamily s) none).map fun c => (c, none)
  | .example =>
    (s.exampleColor.bind fun ex => solve (some ex) (accentFamily ex) (warmOf ex)).map fun c => (c, none)
  | .accentText =>
    if g == s.ink then some (st.colors.accentOnInverse, some .accentOnInverse)
    else (solve (some s.accent) (accentFamily s.accent) (warmOf s.accent)).map fun c => (c, none)
  | _ => none

private theorem contract_parts {s : Seeds} {t : Targets} {c : Colors} (h : contract s t c = true) :
    (sites s t c).all (fun (_, i, g, r) => decide (r ≤ contrastMilli i g)) = true ∧
    (Blocks.all.all fun b => (blockPairs s t c b).all fun (i, g) =>
      decide (t.text ≤ contrastMilli i g)) = true ∧
    (grounds s t c).all (fun (_, fam, g, r) => groundOk s.paper fam g r) = true ∧
    t.pair ≤ contrastMilli c.surfaceStrong c.surface ∧
    t.pair ≤ contrastMilli c.accentSoft c.accentWash := by
  simp only [contract, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩

/-- **A generated palette's derived text tones keep the covered-state contract** in each covered
form, at the share its targets cover at wherever that share binds (`Seeds.coverOf`). -/
public theorem generated_cover_contract {s : Seeds} {t : Targets} (p : Generated s t) :
    ∀ x ∈ coverTones s p.colors, coverKept (s.coverOf t) s.paper x = true := by
  have h := p.valid
  simp only [contract, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2

public theorem generated_sites_contract {s : Seeds} {t : Targets} (p : Generated s t) :
    (∀ x ∈ sites s t p.colors, x.2.2.2 ≤ contrastMilli x.2.1 x.2.2.1) ∧
      ∀ b : Blocks, ∀ x ∈ blockPairs s t p.colors b, t.text ≤ contrastMilli x.1 x.2 := by
  obtain ⟨h1, h2, -, -, -⟩ := contract_parts p.valid
  refine ⟨fun x hx => ?_, fun b x hx => ?_⟩
  · have := List.all_eq_true.mp h1 x hx
    exact of_decide_eq_true this
  · have hb := List.all_eq_true.mp h2 b (by cases b <;> simp [Blocks.all])
    exact of_decide_eq_true (List.all_eq_true.mp hb x hx)

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

private theorem beamerBlocks_pair {s : Seeds} {t : Targets} {c : Colors} {b : Blocks}
    {element : String} {fg bg : Ir.Role} (h : (element, fg, bg) ∈ beamerBlocks s t b)
    {cf cg : Color} (hf : Colors.role s c fg = some cf) (hg : Colors.role s c bg = some cg) :
    (cf, cg) ∈ blockPairs s t c b :=
  List.mem_filterMap.mpr ⟨(element, fg, bg), h, by simp [hf, hg]⟩

/-- Every beamer element the generated palette writes, first written first, with its two
channels' roles. -/
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

/-- The export: an xcolor colour for each role the registry names for export, in registry order,
and an accent's mark under its role's key too. -/
public def declarations (stem : String) (st : SeedState) : String :=
  let defs := String.join (Ir.Role.all.filterMap fun r => do
    let n ← r.row.exportName
    let c ← Colors.role st.seeds st.colors r
    pure ("\\definecolor{" ++ stem ++ n ++ "}{HTML}{" ++ c.hex (hash := false) ++ "}\n"))
  -- the mark under its role's key too, which both engines read (`Ir.Role.ofXcolor?`)
  let mark := match st.colors.alertMark, Ir.Role.alertMark.row.key, Ir.Role.alertMark.row.exportName with
    | some _, some key, some n => "\\colorlet{" ++ key ++ "}{" ++ stem ++ n ++ "}\n"
    | _, _, _ => ""
  defs ++ mark

/-- The export with every beamer element the palette writes bound to its channels' colours. -/
public def beamerDeclarations (stem : String) (st : SeedState) : String :=
  let name (r : Ir.Role) := stem ++ r.row.exportName.getD ""
  declarations stem st ++ String.join ((beamerChannels st).map fun (e, fg, bg) =>
    let parts := (fg.map fun r => "fg=" ++ name r).toList ++ (bg.map fun r => "bg=" ++ name r).toList
    "\\setbeamercolor{" ++ e ++ "}{" ++ ",".intercalate parts ++ "}\n")

public theorem generated_beamer_contract {s : Seeds} {t : Targets} (p : Generated s t)
    (b : Blocks) {element : String} {fg bg : Ir.Role}
    (h : (element, fg, bg) ∈ beamerBlocks s t b) {cf cg : Color}
    (hf : Colors.role s p.colors fg = some cf) (hg : Colors.role s p.colors bg = some cg) :
    t.text ≤ contrastMilli cf cg :=
  (generated_sites_contract p).2 b _ (beamerBlocks_pair h hf hg)

end LeanTex.Core.SeedPalette
