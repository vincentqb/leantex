import LeanTex.Core.Oklab
import LeanTex.Core.Theme

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
/-- SC 1.4.6 (AAA), normal text: 7:1. Not enforced; readable in reports. -/
def aaaText : Nat := 7000

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

-- `decide` below walks the 256-entry table; that needs more elaborator
-- stack than the default allows. The limit raised is depth, not trust.
set_option maxRecDepth 8192

/-- No shipped light bundle regresses into an illegible pair. -/
theorem light_contract : light.contractHolds = true := by decide

/-- The dark variant is held to the same contract, not assumed from the
light one. -/
theorem dark_contract : dark.contractHolds = true := by decide

/-- The PDF default — black ink on the unpainted (white) page — clears the
AA text threshold; 21:1 is the definition's own maximum. -/
theorem pdf_default_text : contrastMilli Color.black Color.white ≥ aaText := by
  decide

-- The document-level check: the pairings a document's own colours create.

private def hexOf (c : Color) : String :=
  let h (v : UInt8) : String :=
    let d := "0123456789ABCDEF".toList
    String.ofList [d.getD (v.toNat / 16) '0', d.getD (v.toNat % 16) '0']
  s!"#{h c.r}{h c.g}{h c.b}"

/-- One coloured text occurrence: the name it was used under when it had
one, the colour, and whether it stood as large-scale text (≥ 18pt, or bold
≥ 14pt — the WCAG 2.2 glossary sizes, against the document's own resolved
base size). -/
private structure Use where
  name : Option String
  color : Color
  large : Bool
  deriving BEq

/-- The text-size context of the walk below. `size` follows the layout
semantics: a size declaration sets a factor over the document base (`base`
here, so `\normalfont` can restore it), it does not compound. -/
private structure UseCx where
  base : Sp
  size : Sp
  bold : Bool := false
  cur : Option (Option String × Color) := none

private def UseCx.large (cx : UseCx) : Bool :=
  cx.size ≥ Dim.pt 18 || (cx.bold && cx.size ≥ Dim.pt 14)

private def UseCx.style (cx : UseCx) : Style → UseCx
  | .bold => { cx with bold := true }
  | .normal => { cx with size := cx.base, bold := false }
  | .size n => match sizeScale.lookup n with
    | some k => { cx with size := cx.base * k / 1000 }
    | none => cx
  | _ => cx

/-- The context a heading's title sets: layout's per-level sizes (14pt and
12pt are absolute, level 3 the base; the level-0 title takes the scale's
LARGE step), bold — 14pt bold is what the WCAG glossary counts as
large-scale. -/
private def headingCx (base : Sp) : Nat → UseCx
  | 0 => { base, size := base * ((sizeScale.lookup "LARGE").getD 1000) / 1000
           bold := true }
  | 1 => { base, size := Dim.pt 14, bold := true }
  | 2 => { base, size := Dim.pt 12, bold := true }
  | _ => { base, size := base, bold := true }

mutual

private def usesInlines (cx : UseCx) (out : Array Use) (xs : List Inline) :
    Array Use :=
  match xs with
  | [] => out
  | x :: rest => usesInlines cx (usesInline cx out x) rest

private def usesInline (cx : UseCx) (out : Array Use) : Inline → Array Use
  | .text s =>
    match cx.cur with
    | some (nm, c) =>
      if s.toList.any (fun ch => !ch.isWhitespace) then
        out.push { name := nm, color := c, large := cx.large }
      else out
    | none => out
  | .math _ _ | .formula _ _ _ | .pageNumber | .pageCount =>
    match cx.cur with
    | some (nm, c) => out.push { name := nm, color := c, large := cx.large }
    | none => out
  | .styled st body => usesInlines (cx.style st) out body.toList
  | .colored c nm body => usesInlines { cx with cur := some (nm, c) } out body.toList
  | .link _ body => usesInlines cx out body.toList
  | .underline body => usesInlines cx out body.toList
  | .step _ _ body => usesInlines cx out body.toList
  | .fill | .linebreak _ => out
  -- An image carries no text; its alt is read by a screen reader, not set
  -- in a colour.
  | .image _ _ _ => out

private def usesBlocks (cx : UseCx) (out : Array Use) (xs : List Block) :
    Array Use :=
  match xs with
  | [] => out
  | b :: rest => usesBlocks cx (usesBlock cx out b) rest

private def usesBlock (cx : UseCx) (out : Array Use) : Block → Array Use
  | .para content => usesInlines cx out content.toList
  | .section level _ title =>
    usesInlines { headingCx cx.base level with cur := cx.cur } out title.toList
  | .list _ items => usesItems cx out items.toList
  | .center body => usesBlocks cx out body.toList
  | .quote body => usesBlocks cx out body.toList
  | .spaced _ body => usesBlocks cx out body.toList
  | .columns cols => usesColumns cx out cols.toList
  | .step _ _ body => usesBlocks cx out body.toList
  -- Conditional content is judged whichever backend carries it: a colour
  -- pairing is wrong on the surface that shows it, so no target set
  -- exempts it. A nav's links are page text like any other.
  | .only _ body => usesBlocks cx out body.toList
  | .nav body => usesBlocks cx out body.toList
  | .frame title _ _ body =>
    -- A frame title sets at `\large\bfseries`: 1.2 of the base, bold.
    let titleCx := { cx with size := cx.base * 1200 / 1000, bold := true }
    usesBlocks cx (usesInlines titleCx out title.toList) body.toList
  -- A framefoot note lands as footer text on the page: its own declared
  -- colours are judged; its default colour is the muted key, judged once
  -- at the palette level.
  | .framefoot content => usesInlines cx out content.toList
  -- A note is a side channel, never page text; verbatim carries no
  -- colour; a rule is decorative ink, not text, so the text-contrast
  -- contract does not judge it; a logo declaration is furniture, not
  -- page text. A picture's labels sit on the picture's own fills, not on
  -- the page, so judging them against the page surface would be judging
  -- the wrong pairing; the label-on-fill contract is still owed (recorded
  -- in the slice report).
  | .note _ | .verbatim _ _ | .rule _ _ _ | .logo _ | .picture _ => out

private def usesItems (cx : UseCx) (out : Array Use) :
    List (Array Block) → Array Use
  | [] => out
  | item :: rest => usesItems cx (usesBlocks cx out item.toList) rest

private def usesColumns (cx : UseCx) (out : Array Use) :
    List (Option Nat × Array Block) → Array Use
  | [] => out
  | (_, body) :: rest => usesColumns cx (usesBlocks cx out body.toList) rest

end

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
pair keeps W0315's spelling and its decorative escape; a defaulted ink on
a declared page is its own code (W0330), because its remedy is different:
declare the ink, not the intent. -/
def effectivePairDiags (doc : Doc) : Array Diag :=
  if doc.palette.decorative.contains "fg" then #[]
  else
    let p := effectivePair doc
    let milli := contrastMilli p.fg p.bg
    if milli < aaText then
      if (Design.ofDoc doc).fgDeclared then
        #[Diag.of .W0315
          (s!"text coloured 'fg' ({hexOf p.fg}) reads at {ratioString milli} " ++
            s!"on the page ({hexOf p.bg}), below the {ratioString aaText} " ++
            "WCAG 2.2 asks of text (SC 1.4.3)")
          (help := some ("deliberate low contrast is declared, not defaulted: " ++
            "\\palette[decorative]{ " ++ s!"fg = {hexOf p.fg} " ++ "}"))]
      else
        #[Diag.of .W0330
          (s!"declared page {hexOf p.bg} keeps the defaulted {hexOf p.fg} ink: " ++
            s!"{ratioString milli}, below the " ++
            s!"{ratioString aaText} WCAG 2.2 asks of text (SC 1.4.3)")
          (help := some ("a declared surface chooses its ink: declare " ++
            "\\palette{ fg = ... }" ++ " beside bg"))]
    else #[]

/-- The pairings a document's own colours create, judged: every colour the
document puts on text is paired with the page by the engine, so each is
checked against the page — the effective page (`effectivePair`), and the
effective ink first of all, whether or not the document spelled it: a
document that declares a dark page and leaves the ink defaulted ships
black-on-dark, and the contract judges what ships, never only what was
spelled. A pairing used only as large-scale text is held to 3:1, any
other use to 4.5:1 (SC 1.4.3). `covered` is exempt by role — dimmed overlay
content is deliberately quiet — and so is anything the document declared
under `\palette[decorative]{...}`: the warning names that spelling, so poor
contrast is a choice a document states, never a silent default. -/
def docDiags (doc : Doc) : Array Diag :=
  -- A one-off append, not a walk: the declared-use half is bound to a name
  -- so the join reads as the two-part contract it is.
  let declared := declaredUseDiags doc
  effectivePairDiags doc ++ declared
where
  declaredUseDiags (doc : Doc) : Array Diag := Id.run do
    let d := Design.ofDoc doc
    let surface := (effectivePair doc).bg
    let base : UseCx := { base := doc.page.fontSize, size := doc.page.fontSize }
    let mut uses := usesBlocks base #[] doc.body.toList
    -- The chrome footer draws small text in `muted` on the page: a document
    -- that overrides the key is judged on the pairing it creates, exactly as
    -- the effective ink is (the shipped bundles are covered by the palette
    -- contract theorems below). Declaredness gates the check — the resolved
    -- design's `muted` is total, but an undeclared key creates no pairing of
    -- its own beyond the effective pair already judged.
    if doc.docClass == "slides" && doc.chrome.hasFooter && doc.foot.isNone then
      if let some muted := doc.palette.find? "muted" then
        uses := uses.push { name := some "muted", color := muted, large := false }
    for run in [doc.head, doc.foot] do
      if let some content := run then
        uses := usesInlines base uses content.toList
    let mut out : Array Diag := #[]
    -- The effective pair is judged in `effectivePairDiags`; a body use of
    -- the same pairing must not report it twice.
    let mut done : Array (Option String × Color) := #[(some "fg", d.fg)]
    for u in uses do
      let key := (u.name, u.color)
      if done.contains key then continue
      done := done.push key
      if let some n := u.name then
        if n == "covered" || doc.palette.decorative.contains n then continue
      let allLarge := uses.all fun v => (v.name, v.color) != key || v.large
      let threshold := if allLarge then aaLargeText else aaText
      let milli := contrastMilli u.color surface
      if milli < threshold then
        let label := match u.name with
          | some n => s!"'{n}' ({hexOf u.color})"
          | none => hexOf u.color
        out := out.push (Diag.of .W0315
          (s!"text coloured {label} reads at {ratioString milli} " ++
            s!"on the page ({hexOf surface}), below the {ratioString threshold} " ++
            s!"WCAG 2.2 asks of {if allLarge then "large-scale text" else "text"} (SC 1.4.3)")
          (help := some ("deliberate low contrast is declared, not defaulted: " ++
            "\\palette[decorative]{ " ++
            s!"{(u.name.getD "quiet")} = {hexOf u.color} " ++ "}")))
    return out

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

/-- The load-bearing form of F3, over every document: when the effective
pair fails the AA text threshold and the ink is not declared decorative,
`docDiags` reports — declared ink or defaulted, because
`effectivePairDiags` judges the pair before the declared-use walk runs.
The missing special case is now an impossibility, not a covered branch. -/
theorem defaulted_ink_cannot_escape (doc : Doc)
    (hdec : doc.palette.decorative.contains "fg" = false)
    (hfail : contrastMilli (effectivePair doc).fg (effectivePair doc).bg < aaText) :
    0 < (docDiags doc).size := by
  have h1 : 0 < (effectivePairDiags doc).size := by
    unfold effectivePairDiags
    rw [hdec]
    simp only [Bool.false_eq_true, ite_false, hfail, ite_true]
    split <;> simp
  simp only [docDiags, Array.size_append]
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
content"; `covered` is exempt as inactive (`covered_is_deliberately_dim`
pins the decision; `coveredContract` below holds it to visibly-covered). -/
def designContract (d : Design) : Bool :=
  contrastMilli d.fg d.bg ≥ aaText
    && contrastMilli d.muted d.bg ≥ aaText
    && (match d.frametitle with
        | some p => contrastMilli p.fg p.bg ≥ aaText
        | none => true)
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

-- The theorems range over the bundles the engine installs: `Theme.moloch`
-- carries its palette as values (mixes evaluated at definition time), so
-- the kernel walks the same entries `\theme` declares — no transcription
-- stands between the statement and the engine.

/-- No shipped moloch pairing is illegible — with the alert corrected: the
lineage's own #EB811B read at 2.61:1 on this page, under SC 1.4.3. -/
theorem moloch_contract : paletteContract Theme.moloch.palette = true := by decide

theorem plain_contract : paletteContract Theme.plain.palette = true := by decide

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
(the Material disabled-state opacity, applied as the opacity it is). -/
theorem default_covered : coveredContract {} = true := by decide

/-- At the bundle's own 31%: at Material's 38% the alert and example
reach only 2.89:1 and 2.75:1 against their active forms, so the fraction
is the finding, not the contract. -/
theorem moloch_covered : coveredContract Theme.moloch.palette = true := by decide

theorem plain_covered : coveredContract Theme.plain.palette = true := by decide

theorem default_cover_monotone : coverMonotone {} = true := by decide

theorem moloch_cover_monotone : coverMonotone Theme.moloch.palette = true := by decide

theorem plain_cover_monotone : coverMonotone Theme.plain.palette = true := by decide

/-- Quantified over the shipped list itself, so a third bundle enters the
contract by being added, not by someone remembering a theorem: every
built-in bundle's resolved design — the values `\theme` installs, with
every default applied — satisfies the contrast contract. -/
theorem builtin_designs_legible :
    Theme.builtin.all (fun th =>
      designContract (Design.ofDoc { palette := th.palette
                                     tokens := th.tokens
                                     styles := th.styles })) = true := by decide

/-- The covered contract, quantified the same way: every built-in
bundle's palette is visibly covered when dimmed, per colour. -/
theorem builtin_designs_covered :
    Theme.builtin.all (fun th => coveredContract th.palette) = true := by decide

end LeanTex.Core.Contrast
