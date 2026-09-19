import LeanTex.Core.Oklab
import LeanTex.Core.Theme
import LeanTex.Core.Layout

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
AA text threshold; 21:1 is the definition's own maximum. -/
theorem pdf_default_text : contrastMilli Color.black Color.white ≥ aaText := by
  decide +kernel

-- The document-level check: the pairings a document's own colours create.

private def hexOf (c : Color) : String :=
  s!"#{Color.hexByte c.r}{Color.hexByte c.g}{Color.hexByte c.b}"

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
  standoutPals : Array Palette := #[]
  pendingPals : Array Palette := #[]

private def pushUnique (xs : Array Palette) (p : Palette) : Array Palette :=
  if xs.contains p then xs else xs.push p

/-- The effective page of a palette: its `bg`, else the shipped light
surface (the same rule `effectivePair` applies to epoch 0). -/
private def surfaceOf (pal : Palette) : Color :=
  (pal.find? "bg").getD light.surface

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
                   exempt := exempt }
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
  | 0 => { base, size := base * ((sizeScale.lookup "LARGE").getD 1000) / 1000
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
  | .quote body => usesBlocks cx acc body.toList
  | .abstract body => usesBlocks cx acc body.toList
  | .role _ body => usesBlocks cx acc body.toList
  | .spaced _ body => usesBlocks cx acc body.toList
  | .columns cols => usesColumns cx acc cols.toList
  | .step n last body => usesBlocks cx (acc.step n last) body.toList
  -- Conditional content is judged whichever backend carries it: a colour
  -- pairing is wrong on the surface that shows it, so no target set
  -- exempts it. A nav's links are page text like any other.
  | .only _ body => usesBlocks cx acc body.toList
  | .nav _ body => usesBlocks cx acc body.toList
  | .frame title standout _ body =>
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
  | .note _ | .verbatim _ _ | .rule _ _ _ | .logo _ | .picture _
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

/-- Each body epoch's effective pair, judged as epoch 0's is
(`effectivePairDiags`): a `\palette` mid-document that leaves its ink
illegible on its page is the same defect wherever it is declared, and it
is judged against the state in force from that point — never the
document's final state. A pair already judged is silent. -/
private def epochPairDiags (doc : Doc) (epochs : Array Palette) : Array Diag := Id.run do
  let d0 := Design.ofDoc doc
  let mut out : Array Diag := #[]
  let mut done : Array ColorPair := #[{ fg := d0.fg, bg := (effectivePair doc).bg }]
  for pal in epochs do
    if pal.decorative.contains "fg" then continue
    let p : ColorPair := { fg := (pal.find? "fg").getD Color.black, bg := surfaceOf pal }
    if done.contains p then continue
    done := done.push p
    let milli := contrastMilli p.fg p.bg
    if milli < aaText then
      if (pal.find? "fg").isSome then
        out := out.push (Diag.of .W0315
          (s!"text coloured 'fg' ({hexOf p.fg}) reads at {ratioString milli} " ++
            s!"on the page ({hexOf p.bg}), below the {ratioString aaText} " ++
            "WCAG 2.2 asks of text (SC 1.4.3)")
          (help := some ("deliberate low contrast is declared, not defaulted: " ++
            "\\palette[decorative]{ " ++ s!"fg = {hexOf p.fg} " ++ "}")))
      else
        out := out.push (Diag.of .W0330
          (s!"declared page {hexOf p.bg} keeps the defaulted {hexOf p.fg} ink: " ++
            s!"{ratioString milli}, below the " ++
            s!"{ratioString aaText} WCAG 2.2 asks of text (SC 1.4.3)")
          (help := some ("a declared surface chooses its ink: declare " ++
            "\\palette{ fg = ... }" ++ " beside bg")))
  return out

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
this; the decorative escape is the same one the per-use walk honours, on
the pair's ink key. -/
private def resolvedPairDiagsAt (doc : Doc)
    (titled standout pending : Array Palette) : Array Diag := Id.run do
  let mut out : Array Diag := #[]
  for pal in titled do
    let d := Design.ofDoc { doc with palette := pal }
    if let some p := d.frametitle then
      let milli := contrastMilli p.fg p.bg
      if milli < aaText && !pal.decorative.contains "frametitlefg" then
        out := out.push (Diag.of .W0345
          (s!"the frame-title bar pairs {hexOf p.fg} on {hexOf p.bg} at " ++
            s!"{ratioString milli}, below the {ratioString aaText} " ++
            "WCAG 2.2 asks of text (SC 1.4.3)")
          (help := some ("deliberate low contrast is declared, not defaulted: " ++
            "\\palette[decorative]{ " ++ s!"frametitlefg = {hexOf p.fg} " ++ "}")))
  for pal in standout do
    let d := Design.ofDoc { doc with palette := pal }
    let milli := contrastMilli d.standout.fg d.standout.bg
    if milli < aaLargeText && !pal.decorative.contains "standoutfg" then
      out := out.push (Diag.of .W0345
        (s!"the standout frame pairs {hexOf d.standout.fg} on " ++
          s!"{hexOf d.standout.bg} at {ratioString milli}, below the " ++
          s!"{ratioString aaLargeText} WCAG 2.2 asks of large-scale text (SC 1.4.3)")
        (help := some ("deliberate low contrast is declared, not defaulted: " ++
          "\\palette[decorative]{ " ++ s!"standoutfg = {hexOf d.standout.fg} " ++ "}")))
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
states, never a silent default. -/
private def declaredUseDiags (doc : Doc) (walk : UseAcc) : Array Diag := Id.run do
  let d := Design.ofDoc doc
  let base : UseCx := { base := doc.page.fontSize, size := doc.page.fontSize }
  -- Page furniture is document state, not flow content: the chrome
  -- footer's muted text and the running head/foot are judged against
  -- epoch 0, whatever the body declared later.
  let mut acc := { walk with pal := doc.palette }
  if doc.docClass.record.chrome && doc.chrome.hasFooter && doc.foot.isNone then
    if let some muted := doc.palette.find? "muted" then
      acc := acc.use base (some "muted") muted
  for run in [doc.head, doc.foot] do
    if let some content := run then
      acc := usesInlines base acc content.toList
  let mut out : Array Diag := #[]
  -- The effective pair is judged in `effectivePairDiags` (and per epoch in
  -- `epochPairDiags`); a body use of the same pairing must not report it
  -- twice.
  let mut done : Array (Option String × Color × Color) :=
    #[(some "fg", d.fg, (effectivePair doc).bg)]
  for u in acc.uses do
    -- The exemption is judged before the dedup: an exempt use must not
    -- consume the key a later, non-exempt epoch's use of the same pairing
    -- would be judged under.
    if u.exempt then continue
    let key := (u.name, u.color, u.surface)
    if done.contains key then continue
    done := done.push key
    let allLarge := acc.uses.all fun v => (v.name, v.color, v.surface) != key || v.large
    let threshold := if allLarge then aaLargeText else aaText
    let milli := contrastMilli u.color u.surface
    if milli < threshold then
      let label := match u.name with
        | some n => s!"'{n}' ({hexOf u.color})"
        | none => hexOf u.color
      out := out.push (Diag.of .W0315
        (s!"text coloured {label} reads at {ratioString milli} " ++
          s!"on {u.groundName.getD "the page"} ({hexOf u.surface}), " ++
          s!"below the {ratioString threshold} " ++
          s!"WCAG 2.2 asks of {if allLarge then "large-scale text" else "text"} (SC 1.4.3)")
        (help := some ("deliberate low contrast is declared, not defaulted: " ++
          "\\palette[decorative]{ " ++
          s!"{(u.name.getD "quiet")} = {hexOf u.color} " ++ "}")))
  return out

/-- The whole document-level contrast contract, one walk: the uses with
their epochs, the design sites per epoch, and the epoch boundaries are
read off `doc.body` once; then each half judges against the palette in
force where the pairing ships. -/
def docDiags (doc : Doc) : Array Diag :=
  let base : UseCx := { base := doc.page.fontSize, size := doc.page.fontSize }
  let walk := usesBlocks base { pal := doc.palette } doc.body.toList
  let declared := declaredUseDiags doc walk
  let resolved := resolvedPairDiagsAt doc walk.titledPals walk.standoutPals
    walk.pendingPals
  effectivePairDiags doc ++ epochPairDiags doc walk.epochs ++ declared ++ resolved

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

end LeanTex.Core.Contrast
