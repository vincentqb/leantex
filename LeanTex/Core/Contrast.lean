import LeanTex.Core.Oklab
import LeanTex.Core.Theme
import LeanTex.Core.Layout
import Std.Data.HashMap
import Std.Data.HashSet

/-!
Colour as a checkable contract: WCAG 2.2 relative luminance and contrast
ratio as pure integer arithmetic over the engine's 8-bit `Color`.

Sources, and the rule taken from each:

* https://www.w3.org/TR/WCAG22/#dfn-relative-luminance — for sRGB,
  L = 0.2126·R + 0.7152·G + 0.0722·B where each channel c/255 is linearised
  as c'/12.92 when c' ≤ 0.04045, else ((c' + 0.055)/1.055)^2.4. (The 0.04045
  threshold is the errata'd value; the older 0.03928 makes no difference for
  8-bit channels — no 8-bit value falls between them.)
* https://www.w3.org/TR/WCAG22/#dfn-contrast-ratio — ratio =
  (L1 + 0.05)/(L2 + 0.05), lighter over darker, range 1:1 to 21:1. Note 3
  there: when no background is specified, white is assumed.
* https://www.w3.org/TR/WCAG22/#contrast-minimum — SC 1.4.3 (AA): text 4.5:1;
  large-scale text 3:1; text in inactive components or pure decoration exempt.
  Large-scale is ≥ 18pt, or ≥ 14pt bold (glossary, "large scale").
* https://www.w3.org/TR/WCAG22/#contrast-enhanced — SC 1.4.6 (AAA): 7:1,
  large text 4.5:1.
* https://www.w3.org/TR/WCAG22/#non-text-contrast — SC 1.4.11 (AA): visual
  information required to identify UI components (the focus indicator here)
  needs 3:1 against adjacent colours.
* https://www.w3.org/TR/WCAG22/#use-of-color — SC 1.4.1 (A): colour must not
  be the only visual means of conveying information. In this engine a link
  carries an underline in both backends and `\alert` maps to bold, so neither
  relies on colour; the checks live in the test suite.
* https://ctan.org/pkg/xcolor (Kern, *Extending LaTeX's color facilities*),
  §2 "colour expressions": `a!P!b` is the convex combination P/100·a +
  (1−P/100)·b computed in the first colour's model, a trailing `!P` fills
  up with white. `Ir.Color.mix`/`Ir.Palette.resolve` implement exactly
  that, on raw sRGB components — the model xcolor computes rgb mixes in.
  Consequence, stated rather than claimed away: sRGB components are not
  perceptually linear, so `a!50!b` is xcolor's midpoint, not the colour a
  viewer would judge halfway between `a` and `b`.

WCAG 2.x is the standard in force; APCA (the WCAG 3 draft contrast method,
https://www.w3.org/TR/wcag-3.0/) is not implemented here because it is a
working draft.

These are the thresholds the engine's own shipped pairings are proved
against (kernel-checked `decide` over the integer arithmetic below), and
the ones document-level diagnostics report.
-/

namespace LeanTex.Core.Contrast

open LeanTex.Core.Ir LeanTex.Core.Dim
open LeanTex.Core.Oklab (channelLinear)

/-- WCAG relative luminance in units of 10⁻⁷ (0 = black, 10⁷ = white):
0.2126·R + 0.7152·G + 0.0722·B over the linearised channels
(`Oklab.channelLinear` — the one tabulation of the sRGB transfer function,
declared beside its other consumer). The division
truncates below 10⁻⁷ — three orders of magnitude finer than any threshold
comparison made here. -/
def luminance (c : Color) : Nat :=
  (2126 * (channelLinear.getD c.r.toNat 0)
    + 7152 * (channelLinear.getD c.g.toNat 0)
    + 722 * (channelLinear.getD c.b.toNat 0)) / 10000

/-- WCAG contrast ratio ×1000, truncated: (L₁ + 0.05)/(L₂ + 0.05) with the
lighter luminance on top. `contrastMilli .black .white = 21000` — the 21:1
the definition names as the maximum. Truncation misstates the real-valued
ratio by less than 0.007 (channel rounding ≤ 1.5·10⁻⁷ per luminance, over
the +0.05 floor); every claim proved here clears its threshold by margins
a thousandfold wider. -/
def contrastMilli (a b : Color) : Nat :=
  let la := luminance a
  let lb := luminance b
  ((max la lb + 500000) * 1000) / (min la lb + 500000)

/-- `4.62:1` from 4627: the human spelling of a milli ratio, for messages. -/
def ratioString (milli : Nat) : String :=
  let frac := (milli % 1000) / 10
  s!"{milli / 1000}.{if frac < 10 then "0" else ""}{frac}:1"

/-- SC 1.4.3 (AA), normal text: 4.5:1. -/
def aaText : Nat := 4500
/-- SC 1.4.3 (AA), large-scale text (≥ 18pt, or ≥ 14pt bold): 3:1. -/
def aaLargeText : Nat := 3000
/-- SC 1.4.11 (AA), non-text UI information such as the focus indicator: 3:1. -/
def aaNonText : Nat := 3000

/-- The colour pairings one variant of the engine's own stylesheet creates:
text inks over the two backgrounds it paints, and the focus indicator. A
new token that gets paired with another belongs here, so the contract below
covers it. -/
structure ThemeColors where
  ink : Color
  surface : Color
  muted : Color
  accent : Color
  tint : Color
  rule : Color
  deriving Repr, BEq

/-- Every pairing this variant's stylesheet creates clears the threshold for
its role: body and marker text on the page (SC 1.4.3, 4.5:1), code text on
its tint (SC 1.4.3), and the focus indicator on the page (SC 1.4.11, 3:1).
`rule` is pure decoration — a hairline under a heading conveys nothing the
heading does not — and pure decoration is exempt by both criteria. -/
def ThemeColors.contractHolds (t : ThemeColors) : Bool :=
  contrastMilli t.ink t.surface ≥ aaText
    && contrastMilli t.muted t.surface ≥ aaText
    && contrastMilli t.ink t.tint ≥ aaText
    && contrastMilli t.accent t.surface ≥ aaNonText

/-- The light token set `HtmlDoc.baseCss` ships. -/
def light : ThemeColors := {
  ink := { r := 0x18, g := 0x18, b := 0x1B }
  surface := { r := 0xFA, g := 0xFA, b := 0xF9 }
  muted := { r := 0x71, g := 0x71, b := 0x7A }
  accent := { r := 0x1D, g := 0x4E, b := 0xD8 }
  tint := { r := 0xF4, g := 0xF4, b := 0xF5 }
  rule := { r := 0xE4, g := 0xE4, b := 0xE7 }
}

/-- The dark token set behind `prefers-color-scheme: dark`. Not an inversion
of `light`: the accent is the same hue two tints lighter, because the light
accent reads at 2.64:1 on this surface — under the 3:1 the focus indicator
needs (SC 1.4.11) — and inverting ink/surface does nothing for a colour that
was chosen against a light page. -/
def dark : ThemeColors := {
  ink := { r := 0xFA, g := 0xFA, b := 0xF9 }
  surface := { r := 0x18, g := 0x18, b := 0x1B }
  muted := { r := 0xA1, g := 0xA1, b := 0xAA }
  accent := { r := 0x60, g := 0xA5, b := 0xFA }
  tint := { r := 0x27, g := 0x27, b := 0x2A }
  rule := { r := 0x3F, g := 0x3F, b := 0x46 }
}

/-- No shipped light bundle regresses into an illegible pair. -/
theorem light_contract : light.contractHolds = true := by decide +kernel

/-- The dark variant is held to the same contract, not assumed from the
light one. -/
theorem dark_contract : dark.contractHolds = true := by decide +kernel

/-- The PDF default — black ink on the unpainted (white) page — clears the
AA text threshold; 21:1 is the definition's own maximum. (Named `_aa`,
not `_text`: `_text` is the registered census-conservation suffix, and a
registry is only a registry if a suffix has one meaning.) -/
theorem pdf_default_aa : contrastMilli Color.black Color.white ≥ aaText := by
  decide +kernel

/-! ## Realization: a role names a hue; the contract chooses its lightness

A palette role declares a hue and chroma; on each ground it ships on, the
engine realizes the lightness that meets the pair's requirement. Sources,
and the rule taken from each:

* https://m3.material.io/styles/color/system/how-the-system-works —
  Material 3 tonal palettes: a key color fixes hue and chroma, and each
  role takes a *tone* (lightness) chosen against its surface so the pair
  meets its contrast; the 40/100 and 90/10 tone pairings exist exactly to
  make the on-color legible on its container.
* https://www.radix-ui.com/colors — one named scale realizes differently
  on light and dark grounds; the hue is the identity, the lightness the
  ground's choice.
* https://tailwindcss.com/docs/colors (v4) — each named hue is an OKLCH
  ladder: one (hue, chroma) family, eleven lightness steps, picked per
  ground.
* https://www.w3.org/TR/WCAG22/#contrast-minimum — the requirement judged:
  SC 1.4.3's 4.5:1 (text) and 3:1 (large-scale text); SC 1.4.11's 3:1 for
  non-text state information. The judged quantity is `contrastMilli`, the
  WCAG relative-luminance ratio — monotone in lightness moving away from
  the ground, which is what the binary search below rides.

The solver searches the Oklab lightness axis at the declared `(a, b)`
(hue and chroma held fixed, exactly Material's tonal walk), taking the
nearest passing lightness to the declared one; when no lightness at that
chroma reaches the ratio (a saturated hue against a mid ground), chroma
reduces stepwise toward the neutral axis before giving up. `none` means
the declared colour stands and the pairing warning fires as before —
realization is never silent and never approximate: every returned colour
re-judges against the requirement by construction
(`realize_meets_contract`), and a pair that already passes is returned
unchanged (`realize_id_of_passing`). -/

/-- The candidate at lightness `L` (the `labOf` 10¹⁸ scale) with chroma
scaled to `f`% of the declared: hue held, tone the variable. -/
private def realizeCand (lab : Oklab.Lab) (f : Nat) (L : Int) : Color :=
  Oklab.toColorOfLab
    { L := L, a := (f : Int) * lab.a / 100, b := (f : Int) * lab.b / 100 }

/-- Binary search on structural fuel between a failing lightness and a
passing one, returning the passing side of the boundary; 60 halvings close
the 10¹⁸ lightness range. The monotonicity assumption only steers the
search — correctness is the caller's re-judgement of the result. -/
private def realizeBisect (pass : Int → Bool) : Nat → Int → Int → Int
  | 0, _, p => p
  | fuel + 1, f, p =>
    let mid := (f + p) / 2
    if mid == f || mid == p then p
    else if pass mid then realizeBisect pass fuel f mid
    else realizeBisect pass fuel mid p

/-- The `labOf` lightness of pure white, the top of the searched axis. -/
private def realizeLMax : Int := 10 ^ 18

/-- The nearest passing lightness at one chroma fraction: both directions
searched, the boundary nearer the declared lightness taken; `none` when
neither end of the axis reaches the requirement at this chroma. -/
private def realizeAt (req : Nat) (ground : Color) (lab : Oklab.Lab)
    (f : Nat) : Option Color :=
  let pass := fun L => decide (req ≤ contrastMilli (realizeCand lab f L) ground)
  if pass lab.L then some (realizeCand lab f lab.L)
  else
    let up := if pass realizeLMax then
        some (realizeBisect pass 60 lab.L realizeLMax) else none
    let down := if pass 0 then some (realizeBisect pass 60 lab.L 0) else none
    match up, down with
    | some u, some d =>
      some (realizeCand lab f (if u - lab.L ≤ lab.L - d then u else d))
    | some u, none => some (realizeCand lab f u)
    | none, some d => some (realizeCand lab f d)
    | none, none => none

/-- Realize a colour on a ground: unchanged when the pair already meets
`req` (milli-ratio, `contrastMilli`'s scale); otherwise the nearest
lightness at the declared hue and chroma that does, reducing chroma toward
the neutral axis when the full-chroma axis never reaches it; `none` when
nothing does — the declared colour then stands and the pairing diagnostic
fires as before. -/
def realize (req : Nat) (ground c : Color) : Option Color :=
  if req ≤ contrastMilli c ground then some c
  -- A colour carrying a print model is declared in DeviceCMYK: realizing
  -- it would repaint the declaration in sRGB and silently drop the
  -- declared components, so the pair keeps its warning instead.
  else if c.cmyk.isSome then none
  else
    (([100, 75, 50, 25, 0] : List Nat).findSome? fun f =>
        realizeAt req ground (Oklab.labOf c) f).bind fun cand =>
      if req ≤ contrastMilli cand ground then some cand else none

/-- The realized colour passes the pair's requirement whenever the solver
returns one — the postcondition by construction: every return is guarded
by the judged quantity itself, so no monotonicity or search argument is
load-bearing. -/
theorem realize_meets_contract {req : Nat} {ground c c' : Color}
    (h : realize req ground c = some c') : req ≤ contrastMilli c' ground := by
  unfold realize at h
  split at h
  next hp => cases h; exact hp
  next =>
    split at h
    next => cases h
    next =>
      match hb : ([100, 75, 50, 25, 0] : List Nat).findSome? fun f =>
          realizeAt req ground (Oklab.labOf c) f with
      | none => rw [hb] at h; cases h
      | some cand =>
        rw [hb, Option.bind_some] at h
        split at h
        next hp => cases h; exact hp
        next => cases h

/-- A pair that already passes is unchanged: realization is the identity
on every legible pairing, so a passing document's artifact cannot move. -/
theorem realize_id_of_passing {req : Nat} {ground c : Color}
    (h : req ≤ contrastMilli c ground) : realize req ground c = some c := by
  simp [realize, h]

-- The document-level check: the pairings a document's own colours create.

private def hexOf (c : Color) : String :=
  s!"#{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}"

/-- One palette-entry realization: applied to the palette equal to `pal`
wherever it stands (the document's or a `.setPalette`'s), so every reader
of the key — both backends through `Design.ofDoc`, the layout's per-epoch
reads — resolves the realized value. -/
private structure PalWrite where
  pal : Palette
  key : String
  value : Color
  deriving Repr, BEq

/-- One run-level realization: a role-named colour on the ground the judge
read it against, and the value that ships there. -/
private structure RunWrite where
  role : String
  declared : Color
  ground : Color
  value : Color
  deriving Repr, BEq

/-- What one judge produces: its diagnostics — an N0022 note where a
failing pair realized, the pairing warning where none could — and the
realization plan `realizeDoc` applies. -/
private structure Judged where
  diags : Array Diag := #[]
  palWrites : Array PalWrite := #[]
  runWrites : Array RunWrite := #[]

/-- The N0022 note: the role kept its hue and chroma; the engine chose its
lightness on this ground (`realize`, whose sources the docstring above
names). -/
private def realizedNote (role : String) (ground : Color)
    (groundName : Option String) (c c' : Color) (req : Nat) : Diag :=
  let dir := if luminance c' ≥ luminance c then "lighter" else "darker"
  Diag.of .N0022
    (s!"'{role}' is realized {dir} ({hexOf c'}) on {groundName.getD "the page"} " ++
      s!"({hexOf ground}) to meet {ratioString req}")

/-- One coloured text occurrence: the name it was used under when it had
one, the colour, whether it stood as large-scale text (≥ 18pt, or bold
≥ 14pt — the WCAG 2.2 glossary sizes, against the document's own resolved
base size) — and the epoch it stood in: the effective page under it and
whether it was decorative-exempt there. A pairing is judged against the
palette in force where it is used, never the document's final one. -/
private structure Use where
  name : Option String
  color : Color
  large : Bool
  /-- The effective page under this use: the local ground where one stands
  (the frame-title bar, the standout inversion), else the epoch palette's
  `bg`, else the shipped light surface when undeclared (WCAG
  contrast-ratio Note 3). Per pair, not per token: the same colour is
  judged once per surface it sits on. -/
  surface : Color
  /-- What the diagnostic calls the surface; `none` reads "the page". -/
  groundName : Option String := none
  /-- Exempt where it stood: `covered`, a name the epoch's decorative set
  carries, or an anonymous value a decorative entry names. -/
  exempt : Bool
  /-- The palette in force at the use: what a realization of this pairing
  is keyed by, and where a matching entry is rewritten. -/
  pal : Palette
  deriving BEq

/-- The walk's fold state: the palette in force (epoch), the uses with
their epochs resolved, and the design sites the per-epoch resolved-pair
judge needs — which epochs shipped a titled frame, a standout frame, or
pending overlay content. Palettes dedup on push: a document has few
epochs, and each is judged once. -/
private structure UseAcc where
  pal : Palette
  uses : Array Use := #[]
  /-- Every `.setPalette` snapshot met, in flow order: the epochs whose
  effective ink/page pair is judged beside epoch 0's. -/
  epochs : Array Palette := #[]
  titledPals : Array Palette := #[]
  /-- Epochs that shipped a titled block, per kind: the kind's resolved
  title pair is judged against the palette in force at the block. -/
  blockPals : Array (TitledKind × Palette) := #[]
  standoutPals : Array Palette := #[]
  pendingPals : Array Palette := #[]

private def pushUnique [BEq α] (xs : Array α) (p : α) : Array α :=
  if xs.contains p then xs else xs.push p

/-- The effective page of a palette: its `bg`, else the shipped light
surface (the same rule `effectivePair` applies to epoch 0). -/
private def surfaceOf (pal : Palette) : Color :=
  (pal.find? "bg").getD light.surface

/-- The ground a titled block's title stands on: the kind's bar where the
palette declares one, the epoch's own page where it does not. One resolving
site, read by the per-use walk, the resolved-pair judge, and the judged-pair
census alike — `titled_ground_agree` holds them to it.

The undeclared page resolves through `surfaceOf`, not `Color.white`, because
that is what the artifacts ship: `Layout` carries an unbarred title run's
ground as `none` — paper it paints no fill for — and under a `none` ground
the PDF leaves white paper while HTML's body takes `--surface`
(`light.surface`, `HtmlDoc.baseCss`). `light.surface` is the darker of the
two, so a pair that passes here passes on the white page too; grounding on
white instead judged the lighter one and passed titles the HTML page fails —
#757575 reads 4.61:1 on white and 4.41:1 on the surface it ships on. -/
private def titledGround (pal : Palette) (kind : TitledKind) : Color :=
  (titledLook pal kind).bar.getD (surfaceOf pal)

/-- The text-size context of the walk below. `size` follows the layout
semantics: a size declaration sets a factor over the document base (`base`
here, so `\normalfont` can restore it), it does not compound. -/
private structure UseCx where
  base : Sp
  size : Sp
  bold : Bool := false
  cur : Option (Option String × Color) := none
  /-- The local ground under this content, when it is not the page: the
  frame-title bar, the standout inversion. A pairing is judged against
  the surface it actually sits on — the same colour can pass on the page
  and fail on the bar (per-pair resolution, not per-token). -/
  ground : Option Color := none
  /-- What the diagnostic calls the ground ("the frame-title bar"); `none`
  reads "the page". -/
  groundName : Option String := none

private def UseCx.large (cx : UseCx) : Bool :=
  cx.size ≥ Dim.pt 18 || (cx.bold && cx.size ≥ Dim.pt 14)

private def UseCx.style (cx : UseCx) : Style → UseCx
  | .bold => { cx with bold := true }
  | .medium => { cx with bold := false }
  -- WCAG 2.2's large-text criterion says "bold"; the registry boundary
  -- `Weight.isBold` (700) is where a series starts counting as that.
  | .series w => { cx with bold := w.isBold }
  | .normal => { cx with size := cx.base, bold := false }
  | .size n => match sizeScale.lookup n with
    | some k => { cx with size := cx.base * k / 1000 }
    | none => cx
  | _ => cx

private def UseAcc.use (acc : UseAcc) (cx : UseCx) (nm : Option String)
    (c : Color) : UseAcc :=
  let exempt := match nm with
    | some n => n == "covered" || acc.pal.decorative.contains n
    | none => acc.pal.decorative.any (fun n => acc.pal.find? n == some c)
  let u : Use := { name := nm
                   color := c
                   large := cx.large
                   surface := cx.ground.getD (surfaceOf acc.pal)
                   groundName := cx.groundName
                   exempt := exempt
                   pal := acc.pal }
  { acc with uses := acc.uses.push u }

/-- Pending overlay content: a step whose range starts (or ends) past the
first step covers on some handout page — the fact that gates the covered
judgement, recorded against the epoch it happens in. -/
private def UseAcc.step (acc : UseAcc) (n : Nat) (last : Option Nat) : UseAcc :=
  if max n (last.getD n) ≥ 2 then
    { acc with pendingPals := pushUnique acc.pendingPals acc.pal }
  else acc

/-- The context a heading's title sets: the layout's own per-level sizes —
`Layout.sectionSize`, the one function titles are set with — in bold. The
level-0 title takes the scale's LARGE step, the elaborator's `\maketitle`
size, which `sectionSize` does not serve. Judging at the size the page
ships is what makes the large-scale call (WCAG 2.2 glossary: ≥ 18pt, or
bold ≥ 14pt) the page's own: a re-spelled absolute here once judged a
phantom 14 pt bold while a 9 pt base set its sections at 12.96 pt. -/
private def headingCx (base : Sp) : Nat → UseCx
  | 0 => { base, size := scaleStep base "LARGE"
           bold := true }
  | l => { base, size := Layout.sectionSize { fontSize := base } l, bold := true }

/-- The judge and the page agree on heading sizes by construction: for the
sectioning levels, `headingCx` reads `Layout.sectionSize` — the function
the layout sets titles with — so the WCAG large-scale judgement is made at
the size the page ships, never at a re-spelled absolute. Stated so the
derivation cannot drift back: the old 14 pt / 12 pt absolutes passed a
9 pt-base section (12.96 pt on the page, not large-scale) as a phantom
14 pt bold, which is — the judge passing text the page fails, the exact
defect class it exists to catch. -/
theorem contrast_judges_what_layout_sets (base : Sp) :
    ∀ l : Nat, 0 < l →
      (headingCx base l).size = Layout.sectionSize { fontSize := base } l
  | _ + 1, _ => rfl
  | 0, h => absurd h (Nat.lt_irrefl 0)

mutual

private def usesInlines (cx : UseCx) (acc : UseAcc) (xs : List Inline) :
    UseAcc :=
  match xs with
  | [] => acc
  | x :: rest => usesInlines cx (usesInline cx acc x) rest

private def usesInline (cx : UseCx) (acc : UseAcc) : Inline → UseAcc
  | .text s =>
    match cx.cur with
    | some (nm, c) =>
      if s.toList.any (fun ch => !ch.isWhitespace) then
        acc.use cx nm c
      else acc
    | none => acc
  -- a resolved reference is ink in the current colour, like a number
  | .math _ _ | .formula _ _ _ | .pageNumber | .pageCount | .ref _ _ _ _ =>
    match cx.cur with
    | some (nm, c) => acc.use cx nm c
    | none => acc
  -- an anchor ships no ink
  | .label _ => acc
  | .styled st body => usesInlines (cx.style st) acc body.toList
  | .colored c nm body => usesInlines { cx with cur := some (nm, c) } acc body.toList
  -- a role names its content; the ink inside keeps the current colour
  | .role _ body => usesInlines cx acc body.toList
  | .link _ body => usesInlines cx acc body.toList
  | .underline body => usesInlines cx acc body.toList
  | .step n last body => usesInlines cx (acc.step n last) body.toList
  -- An alternative is never covered: it is inked at full colour or not
  -- inked at all, so no alt range makes a palette pending.
  | .alt _ _ active otherwise =>
    usesInlines cx (usesInlines cx acc active.toList) otherwise.toList
  -- a note's body is ink like any other; it holds the contrast contract
  | .footnote _ body => usesInlines cx acc body.toList
  | .fill | .strut _ | .linebreak _ => acc
  -- An image carries no text; its alt is read by a screen reader, not set
  -- in a colour.
  | .image _ _ _ => acc
  -- An icon is ink in the current colour: it holds the contrast contract
  -- like a glyph of text, because it is one.
  | .icon _ _ =>
    match cx.cur with
    | some (nm, c) => acc.use cx nm c
    | none => acc
  -- An unresolved citation's marks are ink in the current colour, as text.
  | .cite _ _ =>
    match cx.cur with
    | some (nm, c) => acc.use cx nm c
    | none => acc

private def usesBlocks (cx : UseCx) (acc : UseAcc) (xs : List Block) :
    UseAcc :=
  match xs with
  | [] => acc
  | b :: rest => usesBlocks cx (usesBlock cx acc b) rest

private def usesBlock (cx : UseCx) (acc : UseAcc) : Block → UseAcc
  | .para content => usesInlines cx acc content.toList
  | .equation _ content => usesInlines cx acc content.toList
  | .section level _ _ title =>
    usesInlines { headingCx cx.base level with cur := cx.cur } acc title.toList
  | .list _ items => usesItems cx acc items.toList
  | .center body => usesBlocks cx acc body.toList
  | .ragged body => usesBlocks cx acc body.toList
  | .quote body => usesBlocks cx acc body.toList
  | .abstract body => usesBlocks cx acc body.toList
  | .titled kind title body =>
    -- The block is a design site of its epoch: the kind's resolved title
    -- pair is judged against the palette in force here. The title's own
    -- runs are judged on the ground Layout paints under them — the bar
    -- when the palette declares one, the page otherwise.
    let acc := if title.isEmpty then acc else
      { acc with blockPals := pushUnique acc.blockPals (kind, acc.pal) }
    let look := titledLook acc.pal kind
    let titleCx := { cx with
      bold := true
      ground := look.bar
      groundName := look.bar.map (fun _ => "the block-title bar") }
    usesBlocks cx (usesInlines titleCx acc title.toList) body.toList
  | .role _ body => usesBlocks cx acc body.toList
  | .spaced _ body => usesBlocks cx acc body.toList
  | .columns cols => usesColumns cx acc cols.toList
  | .step n last body => usesBlocks cx (acc.step n last) body.toList
  | .alt _ _ active otherwise =>
    usesBlocks cx (usesBlocks cx acc active.toList) otherwise.toList
  -- Conditional content is judged whichever backend carries it: a colour
  -- pairing is wrong on the surface that shows it, so no target set
  -- exempts it. A nav's links are page text like any other.
  | .only _ body => usesBlocks cx acc body.toList
  | .nav _ body => usesBlocks cx acc body.toList
  | .frame title standout _ _ body =>
    -- A frame title sets at `\large\bfseries` (the shipped bundles'
    -- template): the scale's own step, never a re-spelled factor. The
    -- frame is a design site of its epoch: the resolved-pair judge tests
    -- the frame-title bar and the standout inversion against the palette
    -- in force here, not the document's final one.
    let acc := if title.isEmpty then acc else
      { acc with titledPals := pushUnique acc.titledPals acc.pal }
    let acc := if standout then
      { acc with standoutPals := pushUnique acc.standoutPals acc.pal }
      else acc
    let titleCx := cx.style (.size "large")
    let titleCx := { titleCx with
      bold := true
      ground := acc.pal.find? "frametitlebg"
      groundName := (acc.pal.find? "frametitlebg").map
        (fun _ => "the frame-title bar") }
    -- A standout frame's content sits on the inversion, never the page:
    -- the ground Layout paints (`standoutbg`, else the palette's `fg`).
    let bodyCx := if standout then
        { cx with ground := some ((acc.pal.find? "standoutbg").getD
            ((acc.pal.find? "fg").getD Color.black))
                  groundName := some "the standout frame" }
      else cx
    usesBlocks bodyCx (usesInlines titleCx acc title.toList) body.toList
  -- A framefoot note lands as footer text on the page: its own declared
  -- colours are judged; its default colour is the muted key, judged once
  -- at the palette level.
  | .framefoot content => usesInlines cx acc content.toList
  -- The epoch boundary: the palette in force changes here, in flow order,
  -- and every use after it is judged against the new state.
  | .setPalette p => { acc with pal := p, epochs := acc.epochs.push p }
  | .setTokens _ => acc
  -- Every cell is page text at the body size, judged in whatever colour
  -- wraps it; a caption is page text beside its float's body.
  | .table _ _ _ rows _ =>
    rows.foldl (fun o row => row.foldl (fun o cell => usesInlines cx o cell.toList) o) acc
  -- A line's content and comment are page text, judged in whatever colour
  -- wraps them; the generated keyword and comment furniture takes the
  -- muted role, judged once per bundle at the palette level.
  | .algorithm _ _ lines =>
    lines.foldl (fun o l =>
      let o := usesInlines cx o l.content.toList
      match l.comment with
      | some c => usesInlines cx o c.toList
      | none => o) acc
  | .float _ _ _ body caption =>
    usesBlocks cx (usesInlines cx acc caption.toList) body.toList
  -- Each entry's content is page text at the body size, like a cell's.
  | .bibliography _ _ items =>
    items.foldl (fun o item => usesInlines cx o item.content.toList) acc
  -- A note is a side channel, never page text; verbatim carries no
  -- colour; a rule is decorative ink, not text, so the text-contrast
  -- contract does not judge it; a logo declaration is furniture, not
  -- page text. A picture's labels sit on the picture's own fills, not on
  -- the page, so judging them against the page surface would be judging
  -- the wrong pairing; the label-on-fill contract is still owed (recorded
  -- in the slice report).
  | .verbatim _ _ spec =>
    match spec.caption with
    | some (_, cap) => usesInlines cx acc cap.toList
    | none => acc
  | .note _ | .rule _ _ _ | .logo _ | .picture _
  | .pagebreak => acc

private def usesItems (cx : UseCx) (acc : UseAcc) :
    List (Array Block) → UseAcc
  | [] => acc
  | item :: rest => usesItems cx (usesBlocks cx acc item.toList) rest

private def usesColumns (cx : UseCx) (acc : UseAcc) :
    List (Option Nat × Array Block) → UseAcc
  | [] => acc
  | (_, body) :: rest => usesColumns cx (usesBlocks cx acc body.toList) rest

end

/-- The body walk: every coloured use with the epoch it stood in, the
epoch boundaries, and the design sites each epoch ships, read off
`doc.body` once. One site, so the judge and the judged-pair census read
the same walk and not two copies of it. -/
private def docWalk (doc : Doc) : UseAcc :=
  usesBlocks { base := doc.page.fontSize, size := doc.page.fontSize }
    { pal := doc.palette } doc.body.toList

/-- Every use a document puts on a page: the body walk's, plus the page
furniture's. Page furniture is document state, not flow content — the
chrome footer's muted text and the running head and foot are judged
against epoch 0, whatever the body declared later. One site, read by the
per-use judge and by the judged-pair census. -/
private def docUses (doc : Doc) (walk : UseAcc) : UseAcc := Id.run do
  let base : UseCx := { base := doc.page.fontSize, size := doc.page.fontSize }
  let mut acc := { walk with pal := doc.palette }
  if doc.docClass.record.chrome && doc.chrome.hasFooter && doc.foot.isNone then
    if let some muted := doc.palette.find? "muted" then
      acc := acc.use base (some "muted") muted
  for run in [doc.head, doc.foot] do
    if let some content := run then
      acc := usesInlines base acc content.toList
  return acc

/-- The ink/page pair the shipped pages actually carry, declared or
defaulted: the resolved design's ink — `Design.ofDoc` is the one resolving
site, and `Layout.run` reads the same field for every uncoloured run — over
the declared page when there is one, the shipped light surface otherwise
(WCAG's contrast-ratio Note 3 assumes white when nothing is specified; the
shipped surface is the marginally darker of the two, so passing here passes
on the PDF's white page too). -/
def effectivePair (doc : Doc) : ColorPair :=
  let d := Design.ofDoc doc
  { fg := d.fg, bg := if d.bgDeclared then d.bg else light.surface }

/-- The effective ink judged against the effective page, first and
unconditionally — the straight-line half of `docDiags`, so
`defaulted_ink_cannot_escape` can range over every document. A declared
pair realizes first (N0022) and keeps W0315's spelling where realization
cannot reach, with the decorative escape before either; a defaulted ink on
a declared page is its own code (W0330), because its remedy is different:
declare the ink, not the intent. -/
def effectivePairJudged (doc : Doc) : Judged :=
  if doc.palette.decorative.contains "fg" then {}
  else
    let p := effectivePair doc
    let milli := contrastMilli p.fg p.bg
    if milli < aaText then
      if (Design.ofDoc doc).fgDeclared then
        -- A declared ink is a role: realize its lightness on its page
        -- (hue and chroma kept) before warning; only an unreachable pair
        -- keeps W0315, so poor contrast is never silent and never stands
        -- where the engine can meet the contract.
        match realize aaText p.bg p.fg with
        | some c' =>
          { diags := #[realizedNote "fg" p.bg none p.fg c' aaText]
            palWrites := #[{ pal := doc.palette, key := "fg", value := c' }] }
        | none =>
          { diags := #[Diag.of .W0315
              (s!"text coloured 'fg' ({hexOf p.fg}) reads at {ratioString milli} " ++
                s!"on the page ({hexOf p.bg}), below the {ratioString aaText} " ++
                "WCAG 2.2 asks of text (SC 1.4.3)")
              (help := some ("deliberate low contrast is declared, not defaulted: " ++
                "\\palette[decorative]{ " ++ s!"fg = {hexOf p.fg} " ++ "}"))] }
      else
        -- A defaulted ink was never declared: there is no hue to keep, so
        -- nothing realizes — the remedy is the declaration (W0330 stands).
        { diags := #[Diag.of .W0330
            (s!"declared page {hexOf p.bg} keeps the defaulted {hexOf p.fg} ink: " ++
              s!"{ratioString milli}, below the " ++
              s!"{ratioString aaText} WCAG 2.2 asks of text (SC 1.4.3)")
            (help := some ("a declared surface chooses its ink: declare " ++
              "\\palette{ fg = ... }" ++ " beside bg"))] }
    else {}

/-- Each body epoch's effective pair, judged as epoch 0's is
(`effectivePairDiags`): a `\palette` mid-document that leaves its ink
illegible on its page is the same defect wherever it is declared, and it
is judged against the state in force from that point — never the
document's final state. A pair already judged is silent.

The loop is a fold over a named step, so the plan it builds is a statement's
to read: `epochStep_no_pal_writes` is where "a passing pair is never
rewritten" is held, one epoch at a time. -/
private def epochStep (s : Judged × Array ColorPair) (pal : Palette) :
    Judged × Array ColorPair :=
  if pal.decorative.contains "fg" then s
  else
    let j := s.1
    let p : ColorPair := { fg := (pal.find? "fg").getD Color.black, bg := surfaceOf pal }
    -- The palette write lands per epoch even when the pair's diagnostic is
    -- already reported: two epochs declaring the same failing pair are two
    -- palettes to rewrite, one message to read.
    let dup := s.2.contains p
    let done := s.2.push p
    let milli := contrastMilli p.fg p.bg
    if milli < aaText then
      if (pal.find? "fg").isSome then
        match realize aaText p.bg p.fg with
        | some c' =>
          let j := { j with
            palWrites := j.palWrites.push { pal := pal, key := "fg", value := c' } }
          (if dup then j else
            { j with diags := j.diags.push (realizedNote "fg" p.bg none p.fg c' aaText) },
           done)
        | none =>
          (if dup then j else
            { j with diags := j.diags.push (Diag.of .W0315
              (s!"text coloured 'fg' ({hexOf p.fg}) reads at {ratioString milli} " ++
                s!"on the page ({hexOf p.bg}), below the {ratioString aaText} " ++
                "WCAG 2.2 asks of text (SC 1.4.3)")
              (help := some ("deliberate low contrast is declared, not defaulted: " ++
                "\\palette[decorative]{ " ++ s!"fg = {hexOf p.fg} " ++ "}"))) },
           done)
      else
        (if dup then j else
          { j with diags := j.diags.push (Diag.of .W0330
            (s!"declared page {hexOf p.bg} keeps the defaulted {hexOf p.fg} ink: " ++
              s!"{ratioString milli}, below the " ++
              s!"{ratioString aaText} WCAG 2.2 asks of text (SC 1.4.3)")
            (help := some ("a declared surface chooses its ink: declare " ++
              "\\palette{ fg = ... }" ++ " beside bg"))) },
         done)
    else (j, done)

private def epochPairJudged (doc : Doc) (epochs : Array Palette) : Judged :=
  (epochs.foldl epochStep
    ({}, #[{ fg := (Design.ofDoc doc).fg, bg := (effectivePair doc).bg }])).1

/-- The resolved design's own pairs, judged for the document that ships
them — the pairs `Design.ofDoc` creates out of declared and defaulted keys
together, which the per-use walk in `docDiags` cannot see because no body
text is coloured with them: the frame-title bar (its template sets
`\large\bfseries` — 12pt bold, under WCAG 2.2's large-scale sizes, so SC
1.4.3's 4.5:1), the standout frame (`\Large\bfseries`, 14.4pt bold, WCAG
large-scale, so 3:1), and the covering (SC 1.4.11's 3:1 between an active
and an inactive state, and quieter-than-active — `coveredContract`'s own
two bounds, judged from `Design.cover`, the one resolving site). Each is
judged only when the element ships, and against the palette in force
where it ships — the walk records which epochs carry a titled frame, a
standout frame, or pending overlay content, so a body `\palette` before a
frame is judged for that frame and a declaration after it is not. The
shipped bundles are proved (`builtin_designs_legible`,
`builtin_designs_covered`), so only a document's own override can fire
this; a failing pair realizes before it warns, and the decorative escape is the same one the per-use walk honours, on
the pair's ink key.

Each family is a fold over a named step, and the plan is assembled from the
three that write — so "a passing pair is never rewritten" is one lemma per
step (`blockTitleStep_no_pal_writes` and its siblings), and the cover
judge's write-freedom is structural rather than asserted: a covering is the
author's declaration to quiet, so `pendingCoverDiags` returns messages and
has no plan to add to. -/
private def blockTitleStep (s : Judged) (kp : TitledKind × Palette) : Judged :=
  -- The block title sets bold at the body size — under WCAG 2.2's
  -- large-scale sizes, so SC 1.4.3's 4.5:1 — on the bar when the
  -- palette declares one, on the page otherwise (`titledGround`, the one
  -- resolving site). A failing pair realizes before it warns.
  let kind := kp.1
  let pal := kp.2
  let look := titledLook pal kind
  let ground := titledGround pal kind
  let milli := contrastMilli look.fg ground
  if milli < aaText && !pal.decorative.contains s!"{kind.name}titlefg" then
    match realize aaText ground look.fg with
    | some c' =>
      { s with
        diags := s.diags.push (realizedNote s!"{kind.name}titlefg" ground
          (look.bar.map fun _ => "the block-title bar") look.fg c' aaText)
        palWrites := s.palWrites.push
          { pal := pal, key := s!"{kind.name}titlefg", value := c' } }
    | none =>
      { s with diags := s.diags.push (Diag.of .W0345
        (s!"the {kind.name} block title pairs {hexOf look.fg} on " ++
          s!"{hexOf ground} at {ratioString milli}, below the " ++
          s!"{ratioString aaText} WCAG 2.2 asks of text (SC 1.4.3)")
        (help := some ("deliberate low contrast is declared, not defaulted: " ++
          "\\palette[decorative]{ " ++ s!"{kind.name}titlefg = {hexOf look.fg} " ++ "}"))) }
  else s

private def frameTitleStep (doc : Doc) (s : Judged) (pal : Palette) : Judged :=
  match (Design.ofDoc { doc with palette := pal }).frametitle with
  | none => s
  | some p =>
    let milli := contrastMilli p.fg p.bg
    if milli < aaText && !pal.decorative.contains "frametitlefg" then
      match realize aaText p.bg p.fg with
      | some c' =>
        { s with
          diags := s.diags.push (realizedNote "frametitlefg" p.bg
            (some "the frame-title bar") p.fg c' aaText)
          palWrites := s.palWrites.push
            { pal := pal, key := "frametitlefg", value := c' } }
      | none =>
        { s with diags := s.diags.push (Diag.of .W0345
          (s!"the frame-title bar pairs {hexOf p.fg} on {hexOf p.bg} at " ++
            s!"{ratioString milli}, below the {ratioString aaText} " ++
            "WCAG 2.2 asks of text (SC 1.4.3)")
          (help := some ("deliberate low contrast is declared, not defaulted: " ++
            "\\palette[decorative]{ " ++ s!"frametitlefg = {hexOf p.fg} " ++ "}"))) }
    else s

private def standoutStep (doc : Doc) (s : Judged) (pal : Palette) : Judged :=
  let d := Design.ofDoc { doc with palette := pal }
  let milli := contrastMilli d.standout.fg d.standout.bg
  if milli < aaLargeText && !pal.decorative.contains "standoutfg" then
    match realize aaLargeText d.standout.bg d.standout.fg with
    | some c' =>
      { s with
        diags := s.diags.push (realizedNote "standoutfg" d.standout.bg
          (some "the standout frame") d.standout.fg c' aaLargeText)
        palWrites := s.palWrites.push
          { pal := pal, key := "standoutfg", value := c' } }
    | none =>
      { s with diags := s.diags.push (Diag.of .W0345
        (s!"the standout frame pairs {hexOf d.standout.fg} on " ++
          s!"{hexOf d.standout.bg} at {ratioString milli}, below the " ++
          s!"{ratioString aaLargeText} WCAG 2.2 asks of large-scale text (SC 1.4.3)")
        (help := some ("deliberate low contrast is declared, not defaulted: " ++
          "\\palette[decorative]{ " ++ s!"standoutfg = {hexOf d.standout.fg} " ++ "}"))) }
  else s

/-- The covering judged, per epoch that ships pending content: SC 1.4.11's
3:1 between an active and an inactive state, and quieter-than-active —
`coveredContract`'s own two bounds, read from `Design.cover`. Messages
only: the cover fraction is the author's declaration, so the remedy is
theirs to choose (lower it, or name a quieter colour), and no realization
can make a deliberately dim state legible without undoing the intent. -/
private def pendingCoverDiags (doc : Doc) (pending : Array Palette) :
    Array Diag := Id.run do
  let mut out : Array Diag := #[]
  for pal in pending do
    if pal.decorative.contains "covered" then continue
    let d := Design.ofDoc { doc with palette := pal }
    let cov := d.cover
    let coverHelp := some ("a cover is a declaration too: lower " ++
      "'covered = <n>%', or declare \\palette{ covered = ... } " ++
      "quieter than the ink it stands for")
    let judge (nm : String) (active covered : Color) : Array Diag :=
      if contrastMilli covered d.bg ≥ contrastMilli active d.bg then
        #[Diag.of .W0345
          (s!"covering '{nm}' does not quiet it: the covered form " ++
            "reads as loud on the page as the active one")
          (help := coverHelp)]
      else
        let milli := contrastMilli active covered
        if milli < aaNonText then
          #[Diag.of .W0345
            (s!"covered '{nm}' reads at {ratioString milli} against its " ++
              s!"active form, below the {ratioString aaNonText} " ++
              "WCAG 2.2 asks of a state change (SC 1.4.11)")
            (help := coverHelp)]
        else #[]
    out := out ++ judge "fg" d.fg (cov.of d.fg)
    -- A declared constant cover stands for the plain runs itself: judged
    -- under the key that declared it (undeclared, the plain cover IS the
    -- fg cover just judged).
    if d.covered.isSome then
      out := out ++ judge "covered" d.fg cov.plain
    for role in ["alert", "example"] do
      if let some c := pal.find? role then
        out := out ++ judge role c (cov.of c)
  return out

private def resolvedPairJudged (doc : Doc)
    (titled standout pending : Array Palette)
    (blocks : Array (TitledKind × Palette)) : Judged :=
  let jB := blocks.foldl blockTitleStep {}
  let jT := titled.foldl (frameTitleStep doc) {}
  let jS := standout.foldl (standoutStep doc) {}
  let coverDiags := pendingCoverDiags doc pending
  { diags := jB.diags ++ jT.diags ++ jS.diags ++ coverDiags
    palWrites := jB.palWrites ++ jT.palWrites ++ jS.palWrites }

/-- One pairing: an ink and the ground it stood on. -/
private structure PairKey where
  color : Color
  ground : Color
  deriving BEq

private instance : Hashable PairKey where
  hash k := hash (k.color.r, k.color.g, k.color.b, k.color.cmyk,
    k.ground.r, k.ground.g, k.ground.b, k.ground.cmyk)

/-- What a use is judged under: its pairing and the name it carried there.
The judge's verdict for a use is a function of this key and the document —
never of how many uses precede it — so the judge below answers every
membership question by key. Judging by scanning what came before instead
cost two full passes over the uses per use: 3,200 coloured runs put ~200 ms
of quadratic scanning into a 307 ms build (PLAN 2026-09-23). -/
private structure UseKey where
  name : Option String
  pair : PairKey
  deriving BEq

private instance : Hashable UseKey where
  hash k := hash (k.name, k.pair)

private def Use.key (u : Use) : UseKey :=
  { name := u.name, pair := { color := u.color, ground := u.surface } }

/-- The pairings a document's own colours create, judged: every colour the
document puts on text is paired with the page by the engine, so each is
checked against the page in force where it is used — the epoch's effective
page, and the effective ink first of all, whether or not the document
spelled it: a document that declares a dark page and leaves the ink
defaulted ships black-on-dark, and the contract judges what ships, never
only what was spelled. A pairing used only as large-scale text is held to
3:1, any other use to 4.5:1 (SC 1.4.3). `covered` is exempt by role —
dimmed overlay content is deliberately quiet — and so is anything the
palette in force at the use declared under `\palette[decorative]{...}`:
the warning names that spelling, so poor contrast is a choice a document
states, never a silent default.

The loop is a fold over `useStep`, whose state carries the dedup: the keys
already reported, the palette entries already written per key, and the
solver's answers. That the dedup cannot rewrite a *passing* pair is
`useStep_no_writes`, one use at a time — the dedup is where such a write
would arise, since it is the only state between a pair and its plan. -/
private def allLargeOf (uses : Array Use) : Std.HashMap UseKey Bool :=
  -- Whether a pairing stood as large-scale text *everywhere* it was used:
  -- one keyed fold over the uses, so the answer is the whole document's and
  -- the order the uses arrived in cannot change it.
  uses.foldl (fun m v => m.insert v.key (v.large && (m[v.key]?).getD true)) {}

private structure UseJudgeState where
  j : Judged := {}
  /-- The pairings already reported: the effective pair seeds it, since
  `effectivePairJudged` (and `epochPairJudged`) already spoke for it and a
  body use of the same pairing must not report it twice. -/
  done : Std.HashSet UseKey
  /-- The palette entries already written, per key. Within one key the only
  dimension left is the epoch's palette — a palette and a role fix the
  colour, the ground and so the realized value — and a document has few
  epochs, so this stays the dedup `j.palWrites.contains` was, without the
  scan over every write made so far. -/
  palSeen : Std.HashMap UseKey (Array Palette) := {}
  /-- `realize` is a pure search over the requirement, the ground and the
  colour, so a pairing that repeats is solved once: one pale role through a
  long document paid the Oklab lightness walk per *use* before this,
  1,101 ms of judging for 3,000 uses of one failing role. -/
  solved : Std.HashMap PairKey (Option Color) := {}

private def useStep (large : Std.HashMap UseKey Bool) (s : UseJudgeState) (u : Use) :
    UseJudgeState :=
  -- The exemption is judged before the dedup: an exempt use must not
  -- consume the key a later, non-exempt epoch's use of the same pairing
  -- would be judged under.
  if u.exempt then s
  else
    let key := u.key
    let dup := s.done.contains key
    let done := s.done.insert key
    let allLarge := (large[key]?).getD true
    let threshold := if allLarge then aaLargeText else aaText
    let milli := contrastMilli u.color u.surface
    if milli < threshold then
      -- A role-named use realizes: the hue is the declaration's, the
      -- lightness the ground's choice — normalised at the text threshold
      -- (4.5:1 covers the large-scale 3:1, and one value per (role,
      -- ground) pair is what both backends can agree on). A colour with
      -- no role name was written inline by the author and is never
      -- re-realized — only warned, as before.
      match u.name with
      | some role =>
        let cand := match s.solved[key.pair]? with
          | some c => c
          | none => realize aaText u.surface u.color
        let solved := s.solved.insert key.pair cand
        match cand with
        | some c' =>
          -- The entry rewrite follows the value: when the epoch's palette
          -- carries this role at this colour and the ground is its own
          -- page, the entry realizes too, so furniture and custom
          -- properties read the same value the runs ship. Per epoch, even
          -- when the note is already reported.
          let written := (s.palSeen[key]?).getD #[]
          let entryFollows := u.pal.find? role == some u.color
            && u.surface == surfaceOf u.pal && !written.contains u.pal
          let palSeen := if entryFollows then s.palSeen.insert key (written.push u.pal)
            else s.palSeen
          let w : PalWrite := { pal := u.pal, key := role, value := c' }
          let jw : Judged := if entryFollows then
              { s.j with palWrites := s.j.palWrites.push w } else s.j
          let rw : RunWrite :=
            { role := role, declared := u.color, ground := u.surface, value := c' }
          let jr : Judged := if dup then jw else
            { jw with
              runWrites := jw.runWrites.push rw
              diags := jw.diags.push
                (realizedNote role u.surface u.groundName u.color c' aaText) }
          { j := jr, done := done, palSeen := palSeen, solved := solved }
        | none =>
          let jd : Judged := if dup then s.j else
            { s.j with diags := s.j.diags.push (Diag.of .W0315
              (s!"text coloured '{role}' ({hexOf u.color}) reads at {ratioString milli} " ++
                s!"on {u.groundName.getD "the page"} ({hexOf u.surface}), " ++
                s!"below the {ratioString threshold} " ++
                s!"WCAG 2.2 asks of {if allLarge then "large-scale text" else "text"} (SC 1.4.3)")
              (help := some ("deliberate low contrast is declared, not defaulted: " ++
                "\\palette[decorative]{ " ++
                s!"{role} = {hexOf u.color} " ++ "}"))) }
          { j := jd, done := done, palSeen := s.palSeen, solved := solved }
      | none =>
        let jd : Judged := if dup then s.j else
          { s.j with diags := s.j.diags.push (Diag.of .W0315
            (s!"text coloured {hexOf u.color} reads at {ratioString milli} " ++
              s!"on {u.groundName.getD "the page"} ({hexOf u.surface}), " ++
              s!"below the {ratioString threshold} " ++
              s!"WCAG 2.2 asks of {if allLarge then "large-scale text" else "text"} (SC 1.4.3)")
            (help := some ("deliberate low contrast is declared, not defaulted: " ++
              "\\palette[decorative]{ " ++
              s!"quiet = {hexOf u.color} " ++ "}"))) }
        { s with j := jd, done := done }
    else { s with done := done }

private def declaredUseJudged (doc : Doc) (walk : UseAcc) : Judged :=
  let d := Design.ofDoc doc
  let uses := (docUses doc walk).uses
  (uses.foldl (useStep (allLargeOf uses))
    { done := ({} : Std.HashSet UseKey).insert
        { name := some "fg",
          pair := { color := d.fg, ground := (effectivePair doc).bg } } }).j

/-- The whole document-level contrast contract, one walk: the uses with
their epochs, the design sites per epoch, and the epoch boundaries are
read off `doc.body` once; then each half judges against the palette in
force where the pairing ships — realizing a failing role pair (N0022 +
the plan) before it warns, warning as before where realization cannot
reach or the colour has no role. -/
private def realizePlan (doc : Doc) : Judged :=
  let walk := docWalk doc
  let jE := effectivePairJudged doc
  let jP := epochPairJudged doc walk.epochs
  let jU := declaredUseJudged doc walk
  let jR := resolvedPairJudged doc walk.titledPals walk.standoutPals
    walk.pendingPals walk.blockPals
  { diags := jE.diags ++ jP.diags ++ jU.diags ++ jR.diags
    palWrites := jE.palWrites ++ jP.palWrites ++ jU.palWrites ++ jR.palWrites
    runWrites := jU.runWrites }

/-- The document-level contrast diagnostics: `realizePlan`'s message half. -/
def docDiags (doc : Doc) : Array Diag := (realizePlan doc).diags

/-- The realization pass: judge every (role, ground) pair the document
ships, realize the failing role pairs (`realize` — hue and chroma kept,
lightness chosen per ground), and rewrite the document so both backends
read the realized values — palette entries where the pair is the palette's
own (the frame-title bar, a titled bar, the standout inversion, `fg` and
the content colours on their page), role-named runs where a use sits on a
local ground. A document whose pairs all pass is returned untouched —
`realizeDoc_id`, stated over this function and proved through each judge's
own plan, not inferred from the single-pair `realize_id_of_passing` — so a
legible document's artifact cannot move. Diagnostics are the judges' own:
N0022 where a pair realized, the pairing warnings where none could. -/
def realizeDoc (doc : Doc) : Doc × Array Diag :=
  let j := realizePlan doc
  if j.palWrites.isEmpty && j.runWrites.isEmpty then (doc, j.diags)
  else
    let repal : Palette → Palette := fun p =>
      j.palWrites.foldl (fun q w => if w.pal == p then q.declare w.key w.value else q) p
    let recolor : RoleRecolor := fun pal ground nm c =>
      match nm with
      | some role =>
        let surface := ground.getD (surfaceOf pal)
        match j.runWrites.find? fun w =>
            w.role == role && w.declared == c && w.ground == surface with
        | some w => w.value
        | none => c
      | none => c
    ({ doc with
        palette := repal doc.palette
        head := doc.head.map fun xs =>
          recolorRolesInlines recolor doc.palette none #[] xs.toList
        foot := doc.foot.map fun xs =>
          recolorRolesInlines recolor doc.palette none #[] xs.toList
        body := recolorRoles repal recolor doc.palette doc.body },
      j.diags)

/-- The judged pair is the shipped pair: what `effectivePairDiags` judges is
the resolved design's own ink — the field `Layout.run` colours every
uncoloured run with — and, on a declared page, the resolved design's own
surface — the fill `Layout.run` paints the page with. Definitional by
construction (`effectivePair` reads `Design.ofDoc`, the one resolving
site), and stated so the construction cannot drift: a defaulted colour
cannot escape the contract by never being spelled. -/
theorem judged_pair_is_shipped (doc : Doc) :
    (effectivePair doc).fg = (Design.ofDoc doc).fg ∧
    ((Design.ofDoc doc).bgDeclared = true →
      (effectivePair doc).bg = (Design.ofDoc doc).bg) :=
  ⟨rfl, fun h => by simp [effectivePair, h]⟩

/-- The resolved-pair judge grounds a titled title where the per-use walk
records it: both resolve `(titledLook pal kind).bar` — the ground `Layout`
carries on the title run, `none` where no bar is declared — through
`surfaceOf`, the engine's one reading of an unpainted page. Two projections
of one palette, so the pair the judge weighs is the pair the reader sees.

Stated because the two drifted: the judge read an unbarred title's page as
`Color.white` while the walk read it as `surfaceOf` (`#FAFAF9`, the surface
`HtmlDoc.baseCss` ships under a `none` ground), and white is the lighter
ground — so a title between the two ratios was judged passing and shipped
failing, with no test, theorem or diagnostic to say so. -/
theorem titled_ground_agree (acc : UseAcc) (cx : UseCx) (kind : TitledKind)
    (nm : Option String) (c : Color) :
    ((acc.use { cx with ground := (titledLook acc.pal kind).bar } nm c).uses.back?).map
        Use.surface = some (titledGround acc.pal kind) := by
  simp [UseAcc.use, titledGround]

/-- The load-bearing form of F3, over every document: when the effective
pair fails the AA text threshold and the ink is not declared decorative,
`docDiags` reports — declared ink or defaulted, because
`effectivePairDiags` judges the pair before the declared-use walk runs.
The missing special case is now an impossibility, not a covered branch. -/
theorem defaulted_ink_cannot_escape (doc : Doc)
    (hdec : doc.palette.decorative.contains "fg" = false)
    (hfail : contrastMilli (effectivePair doc).fg (effectivePair doc).bg < aaText) :
    0 < (docDiags doc).size := by
  have h1 : 0 < (effectivePairJudged doc).diags.size := by
    unfold effectivePairJudged
    rw [hdec]
    simp only [Bool.false_eq_true, ite_false, hfail, ite_true]
    split
    · split <;> simp
    · simp
  simp only [docDiags, realizePlan, Array.size_append]
  omega

-- The built-in theme bundles, held to the same contract.

/-- Every pairing a resolved design ships is legible: body ink on the page
(SC 1.4.3, 4.5:1); `muted` — the chrome footer's small text — on the page,
under WCAG's large-scale sizes, so 4.5:1 as well (total: undeclared it is
the body ink, so the clause collapses into the first); the frame-title bar
pair when the design has one — `\large\bfseries` is 12pt bold, under WCAG's
large-scale sizes, so 4.5:1; and the standout pair — `\Large\bfseries`,
14.4pt bold, large-scale, so 3:1 — which resolution makes total, so a
defaulted inversion is checked, never assumed. The progress bar and
separator are not checked: supplementary position indicators the section
title already carries, outside SC 1.4.11's "required to understand the
content"; `covered` is exempt as inactive — a declared design decision,
pinned by this judge's own skip rather than by a theorem, and
`coveredContract` below holds it to visibly-covered. -/
def designContract (d : Design) : Bool :=
  contrastMilli d.fg d.bg ≥ aaText
    && contrastMilli d.muted d.bg ≥ aaText
    && (match d.frametitle with
        | some p => contrastMilli p.fg p.bg ≥ aaText
        | none => true)
    -- The titled block's pairs, total as the standout's: the title sets
    -- bold at the body size (under WCAG's large-scale sizes, so 4.5:1)
    -- on the bar when the design has one, on the page otherwise.
    && contrastMilli d.blockTitle.fg (d.blockTitle.bar.getD d.bg) ≥ aaText
    && contrastMilli d.alertTitle.fg (d.alertTitle.bar.getD d.bg) ≥ aaText
    && contrastMilli d.exampleTitle.fg (d.exampleTitle.bar.getD d.bg) ≥ aaText
    && contrastMilli d.standout.fg d.standout.bg ≥ aaLargeText

/-- A palette's whole contract: `alert` and `example` colour body text on
`bg` (4.5:1, SC 1.4.3) — content colours the design record does not carry —
and every semantic pairing (`muted` included) is the resolved design's,
judged with its defaults applied rather than passed vacuously when a key is
absent. -/
def paletteContract (pal : Palette) : Bool :=
  let bg := (pal.find? "bg").getD Color.white
  let text (k : String) : Bool :=
    match pal.find? k with
    | some c => contrastMilli c bg ≥ aaText
    | none => true
  text "alert" && text "example"
    && designContract (Design.ofDoc { palette := pal })

def Theme.contractHolds (th : LeanTex.Core.Theme.Theme) : Bool :=
  paletteContract th.palette

-- The theorems range over the bundles the engine installs: `Theme.builtin`
-- carries each palette as values (mixes evaluated at definition time), so
-- the kernel walks the same entries `\theme` declares — no transcription
-- stands between the statement and the engine. Each contract quantifies
-- over the shipped list itself, so a third bundle enters every contract by
-- being added, not by someone remembering three theorems; only the default
-- surface (`{}` is not in `builtin`) keeps its own statements.

/-- No shipped bundle's pairing is illegible: every built-in palette — the
content colours (`alert`, `example`) and the resolved design's semantic
pairings, defaults applied — clears its WCAG 2.2 threshold. Moloch's alert
is the corrected one: the lineage's own #EB811B read at 2.61:1 on this
page, under SC 1.4.3. -/
theorem builtin_palettes_contract :
    Theme.builtin.all (fun th => paletteContract th.palette) = true := by decide +kernel

/-- Covered reads as covered on the design's own page, per colour — the
contract ranges over the cover of every colour the bundle puts on text
(`fg`, `alert`, `example`), never over `fg` alone: one global fraction
that works for the ink can fail a chromatic role (at 38% moloch's alert
reaches only 2.89:1 against its active form), and a cover the reader
cannot see is a covering defect wherever it happens. Each colour must be
quieter than its active form against the page (SC 1.4.3 exempts inactive
text, so no minimum binds the covered text itself), and each active/
covered pair must differ by at least 3:1 — the ratio WCAG 2.2 SC 1.4.11
asks of visual information that identifies a state. The plain cover
(runs with no colour of their own) is held to the same two bounds
against `fg`. Judged from `Design.cover`, the one resolving site. If a
bundle needs a smaller fraction to close, that is a finding about the
bundle — moloch's 31% — never a reason to weaken this contract. -/
def coveredContract (pal : Palette) : Bool :=
  let d := Design.ofDoc { palette := pal }
  let cov := d.cover
  let visiblyCovered (c : Color) : Bool :=
    contrastMilli (cov.of c) d.bg < contrastMilli c d.bg
      && contrastMilli c (cov.of c) ≥ aaNonText
  visiblyCovered d.fg
    && (match pal.find? "alert" with | some c => visiblyCovered c | none => true)
    && (match pal.find? "example" with | some c => visiblyCovered c | none => true)
    && contrastMilli cov.plain d.bg < contrastMilli d.fg d.bg
    && contrastMilli d.fg cov.plain ≥ aaNonText

/-- Covering twice quiets further: the cover of a covered colour reads
quieter against the page than the cover itself, for every text role the
bundle ships — the monotonicity that makes "more covered" mean what it
says. The general integer statement needs luminance monotonicity through
the whole pipeline (a refactor, tracked in PLAN, not claimed here); this
is its per-bundle kernel check, with a property test over random colours
in `Tests.lean` beside it. -/
def coverMonotone (pal : Palette) : Bool :=
  let d := Design.ofDoc { palette := pal }
  let cov := d.cover
  let quieter (c : Color) : Bool :=
    contrastMilli (cov.of (cov.of c)) d.bg < contrastMilli (cov.of c) d.bg
  quieter d.fg
    && (match pal.find? "alert" with | some c => quieter c | none => true)
    && (match pal.find? "example" with | some c => quieter c | none => true)

/-- The default surface: black ink, white page, covered at
`coveredFractionDefault` — 38% of the ink over the page, mixed in Oklab
(the Material disabled-state opacity, applied as the opacity it is). `{}`
is not in `Theme.builtin`, so the default keeps its own statement. -/
theorem default_covered : coveredContract {} = true := by decide +kernel

theorem default_cover_monotone : coverMonotone {} = true := by decide +kernel

/-- Cover monotonicity, quantified over the shipped list: covering twice
quiets further for every built-in bundle's text roles. -/
theorem builtin_covers_monotone :
    Theme.builtin.all (fun th => coverMonotone th.palette) = true := by decide +kernel

/-- Quantified over the shipped list itself, so a third bundle enters the
contract by being added, not by someone remembering a theorem: every
built-in bundle's resolved design — the values `\theme` installs, with
every default applied — satisfies the contrast contract. -/
theorem builtin_designs_legible :
    Theme.builtin.all (fun th =>
      designContract (Design.ofDoc { palette := th.palette
                                     tokens := th.tokens
                                     styles := th.styles })) = true := by decide +kernel

/-- The covered contract, quantified the same way: every built-in
bundle's palette is visibly covered when dimmed, per colour. -/
theorem builtin_designs_covered :
    Theme.builtin.all (fun th => coveredContract th.palette) = true := by decide +kernel

/-- Both contracts over what `\theme` installs, for every shipped bundle
(arch-provable I2): stated over `Theme.apply t {}` — the exact function
`Elab` runs at the `\theme` site (values in, values out), on a document
that has declared nothing — never a transcription of the install. The
remaining link, that `\theme` reaches this install through `Elab.run`,
is the per-bundle "`\theme` installs the bundle's own values" pin in
`Tests.lean`: `Elab.run`'s tracked non-total functions keep the
elaborator itself outside the kernel's reach. -/
theorem builtin_palette_contract_engine :
    (Theme.builtin.all fun t =>
      paletteContract (Theme.apply t {}).palette &&
      coveredContract (Theme.apply t {}).palette) = true := by
  decide +kernel

/-- The (ink, ground) pairs the document-level contrast judge enumerates,
as data: the effective pair, each body epoch's effective pair, every
coloured use on the surface it stood on (the running head and foot and
the chrome footer's muted key included, exactly as `docDiags`' walk reads
them), and the resolved design-site pairs per epoch that ships one — the
frame-title bar, the standout inversion, the titled blocks.
`contrast_judged_complete` (Obligations) ranges over this projection: a
shipped glyph run whose (colour, ground) pair falls outside this set
would be a run the judge never saw, and the obligation is that no such
run exists.

One family per operand, each the same array the matching judge iterates
(`docWalk`, `docUses`, the one resolving sites) — declarative rather than
accumulated so a statement can read a family's membership off it, which is
what `realizeDoc_id` needs to carry a passing pair into each judge. -/
def judgedPairs (doc : Doc) : Array (Color × Color) :=
  let walk := docWalk doc
  let d0 := Design.ofDoc doc
  let bg0 := (effectivePair doc).bg
  #[((effectivePair doc).fg, bg0), (d0.fg, bg0), (d0.muted, bg0)]
    ++ (walk.epochs.map fun pal => ((pal.find? "fg").getD Color.black, surfaceOf pal))
    ++ ((docUses doc walk).uses.map fun u => (u.color, u.surface))
    ++ (walk.blockPals.map fun kp => ((titledLook kp.2 kp.1).fg, titledGround kp.2 kp.1))
    ++ (walk.titledPals.filterMap fun pal =>
        (Design.ofDoc { doc with palette := pal }).frametitle.map fun p => (p.fg, p.bg))
    ++ (walk.standoutPals.map fun pal =>
        ((Design.ofDoc { doc with palette := pal }).standout.fg,
         (Design.ofDoc { doc with palette := pal }).standout.bg))

/-- Every (role, ground) pair a shipped bundle's resolved design creates
realizes to itself: the pairs already meet their WCAG 2.2 requirement, so
realization is the identity on them (`realize_id_of_passing` is the
general statement; this is its kernel check over the shipped values, the
census half of the realization rule). Quantified over `Theme.builtin` and
over the design's own grounds — the page under the content colours and
`muted`, the frame-title bar under its ink, each titled bar under its
title, the standout ground under its ink — so adding a bundle is entering
the contract. The cross-ground pairs a document's own content creates
(a content colour inside a frame title or a standout frame) realize at
their use sites and are pinned executably in Tests.lean
(realizedCrossChecks): the search there is not the identity, and the
kernel does not evaluate it cheaply. -/
theorem realized_builtin_contract :
    (Theme.builtin.all fun th =>
      let pal := th.palette
      let d := Design.ofDoc { palette := pal }
      let ok (req : Nat) (ground c : Color) : Bool := realize req ground c == some c
      ok aaText d.bg d.fg && ok aaText d.bg d.muted
        && (match pal.find? "alert" with | some c => ok aaText d.bg c | none => true)
        && (match pal.find? "example" with | some c => ok aaText d.bg c | none => true)
        && (match d.frametitle with | some p => ok aaText p.bg p.fg | none => true)
        && ok aaText (d.blockTitle.bar.getD d.bg) d.blockTitle.fg
        && ok aaText (d.alertTitle.bar.getD d.bg) d.alertTitle.fg
        && ok aaText (d.exampleTitle.bar.getD d.bg) d.exampleTitle.fg
        && ok aaLargeText d.standout.bg d.standout.fg) = true := by
  decide +kernel

/-- A fold's invariant, as an induction the judges' no-write lemmas below
instantiate: a property held by the seed and by every step over the list's
own elements is held by the result. -/
private theorem foldlList_invariant {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (xs : List α) (init : β), P init →
      (∀ b a, a ∈ xs → P b → P (f b a)) → P (xs.foldl f init)
  | [], _, hi, _ => hi
  | a :: as, init, hi, hs =>
    foldlList_invariant P f as (f init a) (hs init a (List.mem_cons_self ..) hi)
      (fun b x hx hb => hs b x (List.mem_cons_of_mem a hx) hb)

private theorem epochStep_no_pal_writes (s : Judged × Array ColorPair) (pal : Palette)
    (hpass : aaText ≤ contrastMilli ((pal.find? "fg").getD Color.black) (surfaceOf pal))
    (h : s.1.palWrites = #[]) : (epochStep s pal).1.palWrites = #[] := by
  unfold epochStep
  split
  · exact h
  · simpa [Nat.not_lt.mpr hpass] using h

private theorem epochPairJudged_no_pal_writes (doc : Doc) (epochs : Array Palette)
    (h : ∀ pal ∈ epochs,
      aaText ≤ contrastMilli ((pal.find? "fg").getD Color.black) (surfaceOf pal)) :
    (epochPairJudged doc epochs).palWrites = #[] := by
  unfold epochPairJudged
  rw [← Array.foldl_toList]
  exact foldlList_invariant (fun s => s.1.palWrites = #[]) epochStep epochs.toList
    ({}, #[{ fg := (Design.ofDoc doc).fg, bg := (effectivePair doc).bg }]) rfl
    fun s pal hmem hs =>
      epochStep_no_pal_writes s pal (h pal (Array.mem_toList_iff.mp hmem)) hs

private theorem effectivePairJudged_no_pal_writes (doc : Doc)
    (hpass : aaText ≤ contrastMilli (effectivePair doc).fg (effectivePair doc).bg) :
    (effectivePairJudged doc).palWrites = #[] := by
  unfold effectivePairJudged
  split
  · rfl
  · simp [Nat.not_lt.mpr hpass]

private theorem blockTitleStep_no_pal_writes (s : Judged) (kp : TitledKind × Palette)
    (hpass : aaText ≤ contrastMilli (titledLook kp.2 kp.1).fg (titledGround kp.2 kp.1))
    (h : s.palWrites = #[]) : (blockTitleStep s kp).palWrites = #[] := by
  simpa [blockTitleStep, Nat.not_lt.mpr hpass] using h

private theorem frameTitleStep_no_pal_writes (doc : Doc) (s : Judged) (pal : Palette)
    (hpass : ∀ p : ColorPair, (Design.ofDoc { doc with palette := pal }).frametitle = some p →
      aaText ≤ contrastMilli p.fg p.bg)
    (h : s.palWrites = #[]) : (frameTitleStep doc s pal).palWrites = #[] := by
  unfold frameTitleStep
  split
  · exact h
  · next p hp => simpa [Nat.not_lt.mpr (hpass p hp)] using h

private theorem standoutStep_no_pal_writes (doc : Doc) (s : Judged) (pal : Palette)
    (hpass : aaLargeText ≤ contrastMilli
      (Design.ofDoc { doc with palette := pal }).standout.fg
      (Design.ofDoc { doc with palette := pal }).standout.bg)
    (h : s.palWrites = #[]) : (standoutStep doc s pal).palWrites = #[] := by
  simpa [standoutStep, Nat.not_lt.mpr hpass] using h

private theorem resolvedPairJudged_no_pal_writes (doc : Doc)
    (titled standout pending : Array Palette) (blocks : Array (TitledKind × Palette))
    (hb : ∀ kp ∈ blocks,
      aaText ≤ contrastMilli (titledLook kp.2 kp.1).fg (titledGround kp.2 kp.1))
    (ht : ∀ pal ∈ titled, ∀ p : ColorPair,
      (Design.ofDoc { doc with palette := pal }).frametitle = some p →
      aaText ≤ contrastMilli p.fg p.bg)
    (hs : ∀ pal ∈ standout, aaLargeText ≤ contrastMilli
      (Design.ofDoc { doc with palette := pal }).standout.fg
      (Design.ofDoc { doc with palette := pal }).standout.bg) :
    (resolvedPairJudged doc titled standout pending blocks).palWrites = #[] := by
  have eB : (blocks.foldl blockTitleStep {}).palWrites = #[] := by
    rw [← Array.foldl_toList]
    exact foldlList_invariant (fun j => j.palWrites = #[]) blockTitleStep blocks.toList
      {} rfl fun j kp hmem hj =>
        blockTitleStep_no_pal_writes j kp (hb kp (Array.mem_toList_iff.mp hmem)) hj
  have eT : (titled.foldl (frameTitleStep doc) {}).palWrites = #[] := by
    rw [← Array.foldl_toList]
    exact foldlList_invariant (fun j => j.palWrites = #[]) (frameTitleStep doc) titled.toList
      {} rfl fun j pal hmem hj =>
        frameTitleStep_no_pal_writes doc j pal (ht pal (Array.mem_toList_iff.mp hmem)) hj
  have eS : (standout.foldl (standoutStep doc) {}).palWrites = #[] := by
    rw [← Array.foldl_toList]
    exact foldlList_invariant (fun j => j.palWrites = #[]) (standoutStep doc) standout.toList
      {} rfl fun j pal hmem hj =>
        standoutStep_no_pal_writes doc j pal (hs pal (Array.mem_toList_iff.mp hmem)) hj
  simp [resolvedPairJudged, eB, eT, eS]

/-- The large-scale threshold is the weaker of the two: a pair that clears
the text requirement clears it wherever the judge asks for 3:1. -/
private theorem aaLargeText_le_aaText : aaLargeText ≤ aaText := by
  unfold aaLargeText aaText
  omega

private theorem useStep_no_writes (large : Std.HashMap UseKey Bool)
    (s : UseJudgeState) (u : Use)
    (hpass : aaText ≤ contrastMilli u.color u.surface)
    (h : s.j.palWrites = #[] ∧ s.j.runWrites = #[]) :
    (useStep large s u).j.palWrites = #[] ∧ (useStep large s u).j.runWrites = #[] := by
  have hthr : ¬ (contrastMilli u.color u.surface <
      (if (large[u.key]?).getD true then aaLargeText else aaText)) := by
    refine Nat.not_lt.mpr ?_
    split
    · exact Nat.le_trans aaLargeText_le_aaText hpass
    · exact hpass
  unfold useStep
  split
  · exact h
  · simpa [hthr] using h

private theorem declaredUseJudged_no_writes (doc : Doc) (walk : UseAcc)
    (h : ∀ u ∈ (docUses doc walk).uses, aaText ≤ contrastMilli u.color u.surface) :
    (declaredUseJudged doc walk).palWrites = #[] ∧
      (declaredUseJudged doc walk).runWrites = #[] := by
  simpa [declaredUseJudged] using
    foldlList_invariant (fun s => s.j.palWrites = #[] ∧ s.j.runWrites = #[])
      (useStep (allLargeOf (docUses doc walk).uses)) (docUses doc walk).uses.toList
      { done := ({} : Std.HashSet UseKey).insert
          { name := some "fg",
            pair := { color := (Design.ofDoc doc).fg, ground := (effectivePair doc).bg } } }
      ⟨rfl, rfl⟩
      fun s u hmem hs =>
        useStep_no_writes _ s u (h u (Array.mem_toList_iff.mp hmem)) hs

/-- A legible document's artifact cannot move: when every pair the judge
enumerates (`judgedPairs` — the effective pair, each epoch's, every
coloured use on the ground it stood on, and each design site that ships)
already meets the text threshold, `realizeDoc` returns the document
itself, not a copy.

`realize_id_of_passing` is the single-pair fact; this is the document-level
one, and the two are not the same claim — a plan that emitted a write for a
*passing* pair would shift a legible document's colours while every
single-pair statement stayed true. The proof is one no-write lemma per
judge, each a fold invariant over that judge's own step, so the dedup state
the plan is built through (`useStep`'s `done`/`palSeen`/`solved`) cannot
manufacture a write the pair did not ask for. The large-scale pairs are
covered by the text threshold, which is the stricter of the two. -/
theorem realizeDoc_id (doc : Doc)
    (h : ∀ p ∈ judgedPairs doc, aaText ≤ contrastMilli p.1 p.2) :
    (realizeDoc doc).1 = doc := by
  have hE : aaText ≤ contrastMilli (effectivePair doc).fg (effectivePair doc).bg := by
    refine h ((effectivePair doc).fg, (effectivePair doc).bg) ?_
    simp only [judgedPairs]
    exact Array.mem_append_left _ (Array.mem_append_left _ (Array.mem_append_left _
      (Array.mem_append_left _ (Array.mem_append_left _ (by simp)))))
  have hP : ∀ pal ∈ (docWalk doc).epochs,
      aaText ≤ contrastMilli ((pal.find? "fg").getD Color.black) (surfaceOf pal) := by
    intro pal hp
    refine h ((pal.find? "fg").getD Color.black, surfaceOf pal) ?_
    simp only [judgedPairs]
    exact Array.mem_append_left _ (Array.mem_append_left _ (Array.mem_append_left _
      (Array.mem_append_left _ (Array.mem_append_right _ (Array.mem_map.mpr ⟨pal, hp, rfl⟩)))))
  have hU : ∀ u ∈ (docUses doc (docWalk doc)).uses,
      aaText ≤ contrastMilli u.color u.surface := by
    intro u hu
    refine h (u.color, u.surface) ?_
    simp only [judgedPairs]
    exact Array.mem_append_left _ (Array.mem_append_left _ (Array.mem_append_left _
      (Array.mem_append_right _ (Array.mem_map.mpr ⟨u, hu, rfl⟩))))
  have hB : ∀ kp ∈ (docWalk doc).blockPals,
      aaText ≤ contrastMilli (titledLook kp.2 kp.1).fg (titledGround kp.2 kp.1) := by
    intro kp hkp
    refine h ((titledLook kp.2 kp.1).fg, titledGround kp.2 kp.1) ?_
    simp only [judgedPairs]
    exact Array.mem_append_left _ (Array.mem_append_left _
      (Array.mem_append_right _ (Array.mem_map.mpr ⟨kp, hkp, rfl⟩)))
  have hT : ∀ pal ∈ (docWalk doc).titledPals, ∀ p : ColorPair,
      (Design.ofDoc { doc with palette := pal }).frametitle = some p →
      aaText ≤ contrastMilli p.fg p.bg := by
    intro pal hpal p hp
    refine h (p.fg, p.bg) ?_
    simp only [judgedPairs]
    exact Array.mem_append_left _ (Array.mem_append_right _
      (Array.mem_filterMap.mpr ⟨pal, hpal, by rw [hp]; rfl⟩))
  have hS : ∀ pal ∈ (docWalk doc).standoutPals, aaLargeText ≤ contrastMilli
      (Design.ofDoc { doc with palette := pal }).standout.fg
      (Design.ofDoc { doc with palette := pal }).standout.bg := by
    intro pal hpal
    refine Nat.le_trans aaLargeText_le_aaText
      (h ((Design.ofDoc { doc with palette := pal }).standout.fg,
          (Design.ofDoc { doc with palette := pal }).standout.bg) ?_)
    simp only [judgedPairs]
    exact Array.mem_append_right _ (Array.mem_map.mpr ⟨pal, hpal, rfl⟩)
  have hu := declaredUseJudged_no_writes doc (docWalk doc) hU
  simp [realizeDoc, realizePlan,
    effectivePairJudged_no_pal_writes doc hE,
    epochPairJudged_no_pal_writes doc (docWalk doc).epochs hP,
    resolvedPairJudged_no_pal_writes doc (docWalk doc).titledPals
      (docWalk doc).standoutPals (docWalk doc).pendingPals (docWalk doc).blockPals hB hT hS,
    hu.1, hu.2]

end LeanTex.Core.Contrast
