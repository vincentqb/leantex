import LeanTex.Core.Ir
import LeanTex.Core.Theme
import LeanTex.Core.Decl

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

open LeanTex.Core.Ir

/-- The WCAG channel linearisation, tabulated: entry `c` is the linearised
value of channel `c` scaled by 10⁷ and rounded to nearest. A table rather
than a `Float` formula so contrast is total integer arithmetic the kernel
can evaluate inside a theorem; `Tests.lean` pins every entry to the spec
formula evaluated in `Float`. Entries 0–10 take the `c'/12.92` branch
(10/255 ≈ 0.0392 ≤ 0.04045), the rest the `((c'+0.055)/1.055)^2.4` branch. -/
def channelLinear : Array Nat := #[
  0, 3035, 6071, 9106, 12141, 15176, 18212, 21247, 24282, 27317,
  30353, 33465, 36765, 40247, 43914, 47770, 51815, 56054, 60488, 65121,
  69954, 74990, 80232, 85681, 91341, 97212, 103298, 109601, 116122, 122865,
  129830, 137021, 144438, 152085, 159963, 168074, 176420, 185002, 193824, 202886,
  212190, 221739, 231534, 241576, 251869, 262412, 273209, 284260, 295568, 307134,
  318960, 331048, 343398, 356013, 368895, 382044, 395462, 409152, 423114, 437350,
  451862, 466651, 481718, 497066, 512695, 528606, 544803, 561285, 578054, 595112,
  612461, 630100, 648033, 666259, 684782, 703601, 722719, 742136, 761854, 781874,
  802198, 822827, 843762, 865005, 886556, 908417, 930590, 953075, 975873, 998987,
  1022417, 1046165, 1070231, 1094617, 1119324, 1144354, 1169707, 1195384, 1221388, 1247718,
  1274377, 1301365, 1328683, 1356333, 1384316, 1412633, 1441285, 1470273, 1499598, 1529262,
  1559265, 1589608, 1620294, 1651322, 1682694, 1714411, 1746474, 1778884, 1811642, 1844750,
  1878208, 1912017, 1946178, 1980693, 2015563, 2050787, 2086369, 2122308, 2158605, 2195262,
  2232280, 2269659, 2307400, 2345506, 2383976, 2422811, 2462013, 2501583, 2541521, 2581829,
  2622507, 2663556, 2704978, 2746773, 2788943, 2831487, 2874408, 2917706, 2961383, 3005438,
  3049873, 3094689, 3139887, 3185468, 3231432, 3277781, 3324515, 3371636, 3419144, 3467041,
  3515326, 3564001, 3613068, 3662526, 3712377, 3762621, 3813260, 3864294, 3915725, 3967552,
  4019778, 4072402, 4125426, 4178851, 4232677, 4286905, 4341536, 4396572, 4452012, 4507858,
  4564110, 4620770, 4677838, 4735315, 4793202, 4851499, 4910208, 4969330, 5028865, 5088813,
  5149177, 5209956, 5271151, 5332764, 5394795, 5457245, 5520114, 5583404, 5647115, 5711248,
  5775804, 5840784, 5906188, 5972018, 6038273, 6104956, 6172066, 6239604, 6307571, 6375969,
  6444797, 6514056, 6583748, 6653873, 6724432, 6795425, 6866853, 6938718, 7011019, 7083758,
  7156935, 7230551, 7304607, 7379104, 7454042, 7529422, 7605245, 7681511, 7758222, 7835378,
  7912979, 7991027, 8069523, 8148466, 8227858, 8307699, 8387990, 8468732, 8549926, 8631572,
  8713671, 8796224, 8879231, 8962694, 9046612, 9130987, 9215819, 9301109, 9386857, 9473065,
  9559734, 9646862, 9734453, 9822506, 9911021, 10000000]

/-- WCAG relative luminance in units of 10⁻⁷ (0 = black, 10⁷ = white):
0.2126·R + 0.7152·G + 0.0722·B over the linearised channels. The division
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
set_option maxRecDepth 4096

/-- No shipped light bundle regresses into an illegible pair. -/
theorem light_contract : light.contractHolds = true := by decide

/-- The dark variant is held to the same contract, not assumed from the
light one. -/
theorem dark_contract : dark.contractHolds = true := by decide

/-- The PDF default — black ink on the unpainted (white) page — clears the
AA text threshold; 21:1 is the definition's own maximum. -/
theorem pdf_default_text : contrastMilli Color.black Color.white ≥ aaText := by
  decide

/-- `coveredDefault` — pending overlay content, dimmed — reads at 2.56:1 on
the PDF page. Deliberate and exempt: SC 1.4.3 places no contrast requirement
on text in an inactive state, and covered content exists to read as not yet
active. Pinned so the exemption is a recorded decision, not an oversight. -/
theorem covered_is_deliberately_dim :
    contrastMilli coveredDefault Color.white < aaLargeText := by decide

-- The document-level check: the pairings a document's own colours create.

private def hexOf (c : Color) : String :=
  let h (v : UInt8) : String :=
    let d := "0123456789ABCDEF".toList
    String.ofList [d.getD (v.toNat / 16) '0', d.getD (v.toNat % 16) '0']
  s!"#{h c.r}{h c.g}{h c.b}"

/-- One coloured text occurrence: the name it was used under when it had
one, the colour, and whether it stood as large-scale text (≥ 18pt, or bold
≥ 14pt — the WCAG 2.2 glossary sizes, against the 10pt body base). -/
private structure Use where
  name : Option String
  color : Color
  large : Bool
  deriving BEq

/-- The text-size context of the walk below. `scale` follows the layout
semantics: a size declaration sets the per-mille factor over the base, it
does not compound. -/
private structure UseCx where
  scale : Nat := 1000
  bold : Bool := false
  cur : Option (Option String × Color) := none

private def UseCx.large (cx : UseCx) : Bool :=
  cx.scale ≥ 1800 || (cx.bold && cx.scale ≥ 1400)

private def UseCx.style (cx : UseCx) : Style → UseCx
  | .bold => { cx with bold := true }
  | .normal => { cx with scale := 1000, bold := false }
  | .size n => match sizeScale.lookup n with
    | some k => { cx with scale := k }
    | none => cx
  | _ => cx

/-- The context a heading's title sets: layout's defaults per level, bold at
14pt for level 1 — which the WCAG glossary counts as large-scale. -/
private def headingCx : Nat → UseCx
  | 1 => { scale := 1400, bold := true }
  | 2 => { scale := 1200, bold := true }
  | _ => { scale := 1000, bold := true }

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
  | .math _ _ | .pageNumber | .pageCount =>
    match cx.cur with
    | some (nm, c) => out.push { name := nm, color := c, large := cx.large }
    | none => out
  | .styled st body => usesInlines (cx.style st) out body.toList
  | .colored c nm body => usesInlines { cx with cur := some (nm, c) } out body.toList
  | .link _ body => usesInlines cx out body.toList
  | .underline body => usesInlines cx out body.toList
  | .step _ body => usesInlines cx out body.toList
  | .fill | .linebreak _ => out

private def usesBlocks (cx : UseCx) (out : Array Use) (xs : List Block) :
    Array Use :=
  match xs with
  | [] => out
  | b :: rest => usesBlocks cx (usesBlock cx out b) rest

private def usesBlock (cx : UseCx) (out : Array Use) : Block → Array Use
  | .para content => usesInlines cx out content.toList
  | .section level _ title =>
    usesInlines { headingCx level with cur := cx.cur } out title.toList
  | .list _ items => usesItems cx out items.toList
  | .center body => usesBlocks cx out body.toList
  | .spaced _ body => usesBlocks cx out body.toList
  | .columns cols => usesColumns cx out cols.toList
  | .step _ body => usesBlocks cx out body.toList
  | .frame title _ body =>
    usesBlocks cx (usesInlines { headingCx 1 with cur := cx.cur } out title.toList)
      body.toList
  -- A note is a side channel, never page text; verbatim carries no colour.
  | .note _ | .verbatim _ => out

private def usesItems (cx : UseCx) (out : Array Use) :
    List (Array Block) → Array Use
  | [] => out
  | item :: rest => usesItems cx (usesBlocks cx out item.toList) rest

private def usesColumns (cx : UseCx) (out : Array Use) :
    List (Option Nat × Array Block) → Array Use
  | [] => out
  | (_, body) :: rest => usesColumns cx (usesBlocks cx out body.toList) rest

end

/-- The pairings a document's own colours create, judged: every colour the
document puts on text is paired with the page by the engine, so each is
checked against the page — the palette's own `bg` entry when it
declares one (the semantic key themes set), the shipped light surface
otherwise (WCAG's contrast-ratio
Note 3 assumes white when nothing is specified; the shipped surface is the
marginally darker of the two, so passing here passes on the PDF's white
page too). A pairing used only as large-scale text is held to 3:1, any
other use to 4.5:1 (SC 1.4.3). `covered` is exempt by role — dimmed overlay
content is deliberately quiet — and so is anything the document declared
under `\palette[decorative]{...}`: the warning names that spelling, so poor
contrast is a choice a document states, never a silent default. -/
def docDiags (doc : Doc) : Array Diag := Id.run do
  let surface := (doc.palette.find? "bg").getD light.surface
  let mut uses := usesBlocks {} #[] doc.body.toList
  -- `fg` colours every uncoloured run through the backends, never through
  -- `.colored`, so the declared pair is judged directly.
  if let some fg := doc.palette.find? "fg" then
    uses := uses.push { name := some "fg", color := fg, large := false }
  for run in [doc.head, doc.foot] do
    if let some content := run then
      uses := usesInlines {} uses content.toList
  let mut out : Array Diag := #[]
  let mut done : Array (Option String × Color) := #[]
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
      out := out.push {
        severity := .warning
        code := "W0315"
        message := s!"text coloured {label} reads at {ratioString milli} " ++
          s!"on the page ({hexOf surface}), below the {ratioString threshold} " ++
          s!"WCAG 2.2 asks of {if allLarge then "large-scale text" else "text"} (SC 1.4.3)"
        help := some ("deliberate low contrast is declared, not defaulted: " ++
          "\\palette[decorative]{ " ++
          s!"{(u.name.getD "quiet")} = {hexOf u.color} " ++ "}") }
  return out

-- The built-in theme bundles, held to the same contract.

/-- A theme bundle's palette, resolved the way `\theme` resolves it: entries
in order, a redeclared name replacing the earlier one, a value either a
`#RRGGBB` literal or a mix expression over what is declared so far. A pure
mirror of the elaborator's value semantics — `Tests.lean` pins the two to
each other on every built-in bundle, so this cannot drift into checking
colours the engine does not ship. -/
def bundlePalette (th : Theme.Theme) : Palette := Id.run do
  let mut pal : Palette := {}
  for entry in Decl.splitEntries th.palette do
    if let some (key, valueSrc) := Decl.splitEntry entry then
      let put (c : Color) : Palette :=
        { entries := (pal.entries.filter (·.1 != key)).push (key, c) }
      match Decl.parseValue valueSrc with
      | some (.color r g b) => pal := put ⟨r, g, b⟩
      | _ =>
        if let some c := pal.resolve valueSrc then
          pal := put c
  return pal

/-- Every text pairing a theme bundle itself creates clears its threshold:
`fg`, `alert`, and `example` colour body text on `bg` (4.5:1, SC 1.4.3);
the frame title sets `frametitlefg` on its `frametitlebg` bar at
`\large\bfseries` — 12pt bold, under the large-scale sizes, so 4.5:1 too;
a standout frame sets `standoutfg` on `standoutbg` at `\Large\bfseries` —
14.4pt bold, large-scale — so 3:1. The progress bar and separator are not
checked: supplementary position indicators the section title already
carries, outside SC 1.4.11's "required to understand the content". A key a
bundle does not declare creates no pairing and passes vacuously. -/
def paletteContract (pal : Palette) : Bool :=
  let bg := (pal.find? "bg").getD Color.white
  let text (k : String) : Bool :=
    match pal.find? k with
    | some c => contrastMilli c bg ≥ aaText
    | none => true
  let pair (f b : String) (threshold : Nat) : Bool :=
    match pal.find? f, pal.find? b with
    | some cf, some cb => contrastMilli cf cb ≥ threshold
    | _, _ => true
  text "fg" && text "alert" && text "example"
    && pair "frametitlefg" "frametitlebg" aaText
    && pair "standoutfg" "standoutbg" aaLargeText

def Theme.contractHolds (th : LeanTex.Core.Theme.Theme) : Bool :=
  paletteContract (bundlePalette th)

/-- `moloch`'s palette as `\theme` resolves it, mixes included; the kernel
cannot evaluate the string parse inside `decide`, so the theorems hold over
these values and `Tests.lean` pins them to `bundlePalette Theme.moloch`,
which in turn is pinned to the elaborator's own resolution. -/
def molochResolved : Palette := { entries := #[
  ("fg", ⟨0x23, 0x37, 0x3B⟩),
  ("bg", ⟨0xFA, 0xFA, 0xFA⟩),
  ("alert", ⟨0xA5, 0x5A, 0x13⟩),
  ("example", ⟨0x00, 0x80, 0x80⟩),
  ("frametitlefg", ⟨0xFA, 0xFA, 0xFA⟩),
  ("frametitlebg", ⟨0x23, 0x37, 0x3B⟩),
  ("progressfg", ⟨0xA5, 0x5A, 0x13⟩),
  ("progressbg", ⟨0xCB, 0xC0, 0xB6⟩),
  ("separator", ⟨0xA5, 0x5A, 0x13⟩),
  ("standoutfg", ⟨0xFA, 0xFA, 0xFA⟩),
  ("standoutbg", ⟨0x23, 0x37, 0x3B⟩)] }

/-- `plain`'s palette as `\theme` resolves it; same pinning as `moloch`'s. -/
def plainResolved : Palette := { entries := #[
  ("fg", ⟨0x1B, 0x1B, 0x1F⟩),
  ("bg", ⟨0xFF, 0xFF, 0xFF⟩),
  ("alert", ⟨0xB3, 0x26, 0x1E⟩),
  ("example", ⟨0x20, 0x5E, 0x3B⟩),
  ("progressfg", ⟨0x76, 0x76, 0x79⟩),
  ("progressbg", ⟨0xDD, 0xDD, 0xDD⟩),
  ("separator", ⟨0xA4, 0xA4, 0xA5⟩),
  ("standoutfg", ⟨0xFF, 0xFF, 0xFF⟩),
  ("standoutbg", ⟨0x1B, 0x1B, 0x1F⟩)] }

/-- No shipped moloch pairing is illegible — with the alert corrected: the
lineage's own #EB811B read at 2.61:1 on this page, under SC 1.4.3. -/
theorem moloch_contract : paletteContract molochResolved = true := by decide

theorem plain_contract : paletteContract plainResolved = true := by decide

end LeanTex.Core.Contrast
