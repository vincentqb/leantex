module

public import LeanTex.Core.ContrastRatio
public import LeanTex.Core.Theme
import LeanTex.Core.Listing
import LeanTex.Core.Oklab
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

/-- The authored expression and span of a color use or declaration,
matched by its palette, role and source value. -/
public abbrev ColorSite := Palette → Option String → Color → Option (String × Span)

/-- `4.62:1` from 4627: the human spelling of a milli ratio, for messages. -/
public def ratioString (milli : Nat) : String :=
  let frac := (milli % 1000) / 10
  s!"{milli / 1000}.{if frac < 10 then "0" else ""}{frac}:1"

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
  name : Option ColorRef
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
  /-- The palette in force at the use: what its decorative exemption and its
  authored site are read under. -/
  pal : Palette
  /-- The coloured run the use stands in (one per `.colored` inline and per
  furniture use): what a pairing's site count counts. -/
  site : Nat := 0
  /-- The highlighting style a listing token's colour is the style's own
  under — a code role the palette leaves undeclared, which the style
  states: what the report names it by, since the document wrote no key. -/
  styleName : Option String := none
  deriving BEq

/-- The walk's fold state: the palette in force (epoch), the uses with
their epochs resolved, and the design sites the per-epoch site judge needs
— which epochs shipped a titled frame, a standout frame, or pending overlay
content. Palettes dedup on push: a document has few epochs, and each is
judged once. -/
private structure UseAcc where
  pal : Palette
  uses : Array Use := #[]
  /-- Every `.setPalette` snapshot met, in flow order: the epochs whose
  effective ink/page pair is judged beside epoch 0's. -/
  epochs : Array Palette := #[]
  titledPals : Array Palette := #[]
  /-- Epochs of numbered frames whose chrome footer actually ships. -/
  footPals : Array Palette := #[]
  /-- Epochs that shipped a titled block, per kind: the kind's resolved
  title pair is judged against the palette in force at the block. -/
  blockPals : Array (TitledKind × Palette) := #[]
  standoutPals : Array Palette := #[]
  /-- Epochs that shipped a title page with a declared ground of its own:
  the site the judge reads there, against the palette in force. -/
  titlePagePals : Array Palette := #[]
  /-- Epochs that shipped a link: where the HTML page draws a focus ring. -/
  linkPals : Array Palette := #[]
  pendingPals : Array Palette := #[]
  /-- The colours some handout page covers, each beside the epoch it stands
  in: the covered judgement reads a colour's cover where one is shown. -/
  coveredNames : Array (Palette × ColorRef) := #[]
  /-- The coloured runs met so far: the next run's site number. -/
  runs : Nat := 0

private def pushUnique [BEq α] (xs : Array α) (p : α) : Array α :=
  if xs.contains p then xs else xs.push p

/-- The effective page of a palette: its `bg`, else the screen's own light
page (the same rule `effectivePair` applies to epoch 0). -/
private def surfaceOf (pal : Palette) : Color :=
  (Design.at pal .light .page).getD Color.white

/-- The text-size context of the walk below. `size` follows the layout
semantics: a size declaration sets a factor over the document base (`base`
here, so `\normalfont` can restore it), it does not compound. -/
private structure UseCx where
  base : Sp
  size : Sp
  /-- Inside overlay content some handout page covers (`UseAcc.step`). -/
  covering : Bool := false
  slides : Bool := false
  chromeFoot : Bool := false
  bold : Bool := false
  cur : Option (Option ColorRef × Color × Nat) := none
  /-- The local ground under this content, when it is not the page: the
  frame-title bar, the standout inversion. A pairing is judged against
  the surface it actually sits on — the same colour can pass on the page
  and fail on the bar (per-pair resolution, not per-token). -/
  ground : Option Color := none
  /-- What the diagnostic calls the ground ("the frame-title bar"); `none`
  reads "the page". -/
  groundName : Option String := none
  /-- A frame-entry ground lasts only until the next palette declaration,
  even when that declaration repeats the same palette. -/
  groundEpoch : Option Nat := none
  /-- A body's default ink follows a palette declaration, while its
  physical fill remains the enclosing surface. -/
  inkEpoch : Option Nat := none
  /-- Frame default for a nested surface; the frame's own default pair is
  already judged by its design-site contract. -/
  inheritedInk : Option (ColorRef × Color) := none
  /-- The highlighting style of the listing this content is a token of. -/
  codeStyle : Option String := none

private def UseCx.atEpoch (cx : UseCx) (pal : Palette) (epoch : Nat) : UseCx :=
  let cx := if cx.inkEpoch.any (· != epoch) then
    { cx with cur := some (some (.role .ink), Design.printInk pal,
        (cx.cur.map (·.2.2)).getD 0), inkEpoch := some epoch }
    else cx
  -- premise: listingPaletteAuditChecks — a body declaration replaces the
  -- entry ground; its colour equality cannot stand in for the boundary.
  if cx.groundEpoch.any (· != epoch) then
    { cx with ground := none, groundName := none, groundEpoch := none, inheritedInk := none }
  else cx

/-- Whether a use stands as large-scale text at the size its medium shows it.
A deck's stage is shown at the size of the screen it is projected on — a
4:3 stage 96 mm tall on a 1080-pixel display sets its 11pt body near 33pt,
past WCAG 2.2's 18pt large-scale threshold — so every slide text is
large-scale; elsewhere the glossary sizes at the document's own base. -/
private def UseCx.large (cx : UseCx) : Bool :=
  cx.slides || largeText cx.size cx.bold

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
  | .fontSize size _ =>
    -- The contrast walk has no measured box or font face. An unresolved
    -- relative size cannot inherit a preceding large-text exemption.
    -- premise: contrastChecks — absolute sizes replace the named scale;
    -- a font-relative size keeps the ordinary text threshold.
    match size.resolve (fun _ => none) with
    | .ok g =>
      { cx with size := if g.width.em == 0 && g.width.ex == 0 then g.width.sp else 0 }
    | .error _ => { cx with size := 0 }
  | _ => cx

private def UseAcc.use (acc : UseAcc) (cx : UseCx) (nm : Option ColorRef)
    (c : Color) : UseAcc :=
  let exempt := match nm with
    | some n => n == .role .covered || acc.pal.decorative.contains n
    | none => acc.pal.decorative.any (fun n => acc.pal.lookup n == some c)
  let styleName := match nm with
    | some (.role r) =>
      if r.code?.isSome && (Design.declared? acc.pal r).isNone then cx.codeStyle else none
    | _ => none
  let u : Use := { name := nm
                   color := c
                   large := cx.large
                   surface := cx.ground.getD (surfaceOf acc.pal)
                   groundName := cx.groundName
                   exempt := exempt
                   pal := acc.pal
                   site := match cx.cur with
                     | some (_, _, k) => k
                     | none => acc.runs
                   styleName }
  let coveredNames := match nm with
    | some n => if cx.covering then pushUnique acc.coveredNames (acc.pal, n) else acc.coveredNames
    | none => acc.coveredNames
  { acc with uses := acc.uses.push u, coveredNames }

/-- Pending overlay content: a step whose range starts (or ends) past the
first step covers on some handout page — the fact that gates the covered
judgement, recorded against the epoch it happens in. -/
private def UseAcc.step (acc : UseAcc) (spec : Ir.OverlaySpec) : UseAcc :=
  if spec.maxStep ≥ 2 then
    { acc with pendingPals := pushUnique acc.pendingPals acc.pal }
  else acc

/-- The context a heading's title sets: the type scale's per-level sizes —
`Ir.headingSize`, the one function the page sets titles with
(`Layout.sectionSize`) — in bold. The level-0 title takes the scale's LARGE
step, the elaborator's `\maketitle` size, which `headingSize` does not
serve here. Judging at the size the page
ships is what makes the large-scale call (WCAG 2.2 glossary: ≥ 18pt, or
bold ≥ 14pt) the page's own: a re-spelled absolute here once judged a
phantom 14 pt bold while a 9 pt base set its sections at 12.96 pt. -/
private def headingCx (base : Sp) : Ir.HeadingLevel → UseCx
  | 0 => { base, size := scaleStep base "LARGE"
           bold := true }
  | l => { base, size := Ir.headingSize base l, bold := true }

/-- The judge and the page agree on heading sizes by construction: for the
sectioning levels, `headingCx` reads `Ir.headingSize` — the function the
layout sets titles with (`Layout.sectionSize`) — so the WCAG large-scale
judgement is made at the size the page ships, never at a re-spelled
absolute. Stated so the
derivation cannot drift back: the old 14 pt / 12 pt absolutes passed a
9 pt-base section (12.96 pt on the page, not large-scale) as a phantom
14 pt bold, which is — the judge passing text the page fails, the exact
defect class it exists to catch. -/
private theorem contrast_judges_what_layout_sets (base : Sp) :
    ∀ l : Ir.HeadingLevel, l ≠ .title →
      (headingCx base l).size = Ir.headingSize base l
  | .title, h => absurd rfl h
  | .h1, _ | .h2, _ | .h3, _ | .h4, _ | .h5, _ | .h6, _ => rfl

mutual

private def usesInlines (cx : UseCx) (acc : UseAcc) (xs : List Inline) :
    UseAcc :=
  match xs with
  | [] => acc
  | x :: rest => usesInlines cx (usesInline cx acc x) rest

private def usesInline (cx : UseCx) (acc : UseAcc) : Inline → UseAcc
  | .text s =>
    match cx.cur with
    | some (nm, c, _) =>
      if s.toList.any (fun ch => !ch.isWhitespace) then
        acc.use cx nm c
      else acc
    | none => acc
  | .math _ _ | .pageNumber | .pageCount =>
    match cx.cur with
    | some (nm, c, _) => acc.use cx nm c
    | none => acc
  -- A resolved reference is ink in the current colour, like a number, and a
  -- link on the HTML page, which draws the focus ring around it.
  | .ref _ _ _ _ =>
    let acc := { acc with linkPals := pushUnique acc.linkPals acc.pal }
    match cx.cur with
    | some (nm, c, _) => acc.use cx nm c
    | none => acc
  -- Judge only ink used by the formula; an inner switch may replace all
  -- uses of its inherited colour.
  | .formula _ _ body =>
    let ink := cx.cur.map fun (nm, c, _) => (c, nm)
    (Math.MList.inks ink #[] body).foldl (fun a (c, nm) =>
      { a.use { cx with cur := some (nm, c, a.runs) } nm c with runs := a.runs + 1 }) acc
  -- an anchor ships no ink
  | .label _ => acc
  | .styled st body => usesInlines (cx.style st) acc body.toList
  | .colored c nm body =>
    usesInlines { cx with cur := some (nm, c, acc.runs) } { acc with runs := acc.runs + 1 }
      body.toList
  -- a role names its content; the ink inside keeps the current colour
  | .located _ body => usesInlines cx acc body.toList
  | .role _ body => usesInlines cx acc body.toList
  | .link _ body =>
    usesInlines cx { acc with linkPals := pushUnique acc.linkPals acc.pal } body.toList
  | .decorated _ body => usesInlines cx acc body.toList
  | .onSteps spec body =>
    usesInlines { cx with covering := cx.covering || spec.maxStep ≥ 2 } (acc.step spec) body.toList
  -- An alternative is never covered: it is inked at full colour or not
  -- inked at all, so no alt range makes a palette pending.
  | .altSteps _ active otherwise =>
    usesInlines cx (usesInlines cx acc active.toList) otherwise.toList
  -- a note's body is ink like any other; it holds the contrast contract
  | .footnote _ body =>
    usesInlines cx { acc with linkPals := pushUnique acc.linkPals acc.pal } body.toList
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .linebreak _ => acc
  -- An image carries no text; its alt is read by a screen reader, not set
  -- in a colour.
  | .image _ _ _ => acc
  -- An icon is ink in the current colour: it holds the contrast contract
  -- like a glyph of text, because it is one.
  | .icon _ _ =>
    match cx.cur with
    | some (nm, c, _) => acc.use cx nm c
    | none => acc
  -- An unresolved citation's marks are ink in the current colour, as text.
  | .cite _ _ =>
    match cx.cur with
    | some (nm, c, _) => acc.use cx nm c
    | none => acc

private def usesBlocks (cx : UseCx) (acc : UseAcc) (xs : List Block) :
    UseAcc :=
  match xs with
  | [] => acc
  | b :: rest =>
    let cx := cx.atEpoch acc.pal acc.epochs.size
    usesBlocks cx (usesBlock cx acc b) rest

private def usesBlock (cx : UseCx) (acc : UseAcc) : Block → UseAcc
  | .para content => usesInlines cx acc content.toList
  | .equation number content =>
    usesInlines cx (usesInlines cx acc content.toList) number.toList
  | .section level _ _ title =>
    let hc := { headingCx cx.base level with cur := cx.cur }
    let (hc, acc) := if cx.slides && level == 1 then
      match Design.declared? acc.pal .sectionTitleInk with
      | some c => ({ hc with cur := some (some (.role .sectionTitleInk), c, acc.runs) },
          { acc with runs := acc.runs + 1 })
      | none => (hc, acc)
      else (hc, acc)
    usesInlines hc acc title.toList
  | .list _ items => usesItems cx acc items.toList
  | .center body => usesBlocks cx acc body.toList
  | .ragged _ body => usesBlocks cx acc body.toList
  | .quote body => usesBlocks cx acc body.toList
  | .abstract body => usesBlocks cx acc body.toList
  | .titled kind title body =>
    let acc := if title.isEmpty then acc else
      { acc with blockPals := pushUnique acc.blockPals (kind, acc.pal) }
    let look := titledLook acc.pal kind
    let titleCx := { cx with
      bold := true
      cur := some (some (.role (Role.titleInk kind)), look.fg, acc.runs)
      ground := look.bar.or cx.ground
      groundName := (look.bar.map (fun _ => "the block-title bar")).or cx.groundName }
    let d := Design.ofPalette acc.pal
    let bodyLook := d.titledBody kind
    let defaultInk := cx.inheritedInk.getD (.role .ink, d.fg)
    let inherited := cx.cur.getD (some defaultInk.1, defaultInk.2, acc.runs + 1)
    let parent : ColorPair := { fg := inherited.2.1, bg := cx.ground.getD (surfaceOf acc.pal) }
    let bodyCx := { cx with
      cur := some (if bodyLook.fg.isSome then some (.role (Role.bodyInk kind)) else inherited.1,
        (bodyLook.resolve parent).fg, acc.runs + 1)
      inkEpoch := some acc.epochs.size
      ground := bodyLook.bg.or cx.ground
      groundName := (bodyLook.bg.map (fun _ => "the block body")).or cx.groundName
      groundEpoch := if bodyLook.bg.isSome then none else cx.groundEpoch }
    usesBlocks bodyCx
      (usesInlines titleCx { acc with runs := acc.runs + 2 } title.toList) body.toList
  | .disclosure summary _ body =>
    usesBlocks cx (usesInlines cx acc (Ir.disclosureSummary summary).toList) body.toList
  | .role _ body => usesBlocks cx acc body.toList
  | .link _ body =>
    usesBlocks cx { acc with linkPals := pushUnique acc.linkPals acc.pal } body.toList
  | .spaced _ body => usesBlocks cx acc body.toList
  | .columns cols => usesColumns cx acc cols.toList
  | .onSteps spec body =>
    usesBlocks { cx with covering := cx.covering || spec.maxStep ≥ 2 } (acc.step spec) body.toList
  | .altSteps _ active otherwise =>
    usesBlocks cx (usesBlocks cx acc active.toList) otherwise.toList
  -- Conditional content is judged whichever backend carries it: a colour
  -- pairing is wrong on the surface that shows it, so no target set
  -- exempts it. A nav's links are page text like any other.
  | .only _ body => usesBlocks cx acc body.toList
  | .nav _ body => usesBlocks cx acc body.toList
  | .frame title standout valign _ body =>
    -- A frame title sets at `\large\bfseries` (the shipped bundles'
    -- template): the scale's own step, never a re-spelled factor. The
    -- frame is a design site of its epoch: the resolved-pair judge tests
    -- the frame-title bar and the standout inversion against the palette
    -- in force here, not the document's final one.
    let acc := if title.isEmpty || (Design.declared? acc.pal .frameTitleBar).isNone then acc
      else { acc with titledPals := pushUnique acc.titledPals acc.pal }
    let acc := if cx.chromeFoot && !standout && !(valign matches .golden) then
      { acc with footPals := pushUnique acc.footPals acc.pal }
      else acc
    let acc := if standout then
      { acc with standoutPals := pushUnique acc.standoutPals acc.pal }
      else acc
    let acc := if !standout && valign matches .golden &&
        (Design.ofPalette acc.pal).titlepage.isSome then
      { acc with titlePagePals := pushUnique acc.titlePagePals acc.pal }
      else acc
    let titleCx := cx.style (.size "large")
    let titleCx := { titleCx with
      bold := true
      ground := Design.declared? acc.pal .frameTitleBar
      groundName := (Design.declared? acc.pal .frameTitleBar).map
        (fun _ => "the frame-title bar") }
    -- A foreground-only title has no bar for the site judge to read.
    let (titleCx, acc) := if titleCx.ground.isNone then
      match Design.declared? acc.pal .frameTitleInk with
      | some c => ({ titleCx with cur := some (some (.role .frameTitleInk), c, acc.runs) },
          { acc with runs := acc.runs + 1 })
      | none => (titleCx, acc)
      else (titleCx, acc)
    -- A standout frame's content sits on the inversion, never the page:
    -- the ground Layout paints (`standoutbg`, else the palette's `fg`).
    let d := Design.ofPalette acc.pal
    let bodyCx := if standout then
        { cx with ground := some d.standout.bg
                  inheritedInk := some (.role .standoutInk, d.standout.fg)
                  groundName := some "the standout frame"
                  groundEpoch := some acc.epochs.size }
      -- And a title page with a declared ground sits on that: the ground
      -- `Layout.titleGround` paints (`Ir.titleGroundOf`, the one reading),
      -- so every use on the page is judged against the surface it really
      -- stands on.
      else match titleGroundOf acc.pal valign with
        | some ground =>
          { cx with ground := some ground, groundName := some "the title page"
                    inheritedInk := some (.role .titlePageInk, (d.titlepage.map (·.fg)).getD d.fg)
                    groundEpoch := some acc.epochs.size }
        | none => cx
    usesBlocks bodyCx (usesInlines titleCx acc title.toList) body.toList
  -- A framefoot note lands as footer text on the page: its own declared
  -- colours are judged; its default colour is the muted key, judged once
  -- at the palette level.
  | .framefoot content =>
    usesInlines { cx with
      ground := (Design.ofPalette acc.pal).footline.bar
      groundName := (Design.ofPalette acc.pal).footline.bar.map (fun _ => "the footline") }
      acc content.toList
  -- The epoch boundary: the palette in force changes here, in flow order,
  -- and every use after it is judged against the new state.
  | .setPalette p => { acc with pal := p, epochs := acc.epochs.push p }
  | .setTokens _ => acc
  -- Every cell is page text at the body size, judged in whatever colour
  -- wraps it; a caption is page text beside its float's body.
  | .table _ _ _ rows _ _ =>
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
  -- A note is a side channel, never page text; a rule is decorative ink,
  -- not text, so the text-contrast
  -- contract does not judge it; a logo declaration is furniture, not
  -- page text. A picture's labels sit on the picture's own fills, not on
  -- the page, so judging them against the page surface would be judging
  -- the wrong pairing; the label-on-fill contract is still owed (recorded
  -- in the slice report).
  | .verbatim covered source spec =>
    let acc := match spec.caption with
      | some (_, cap) => usesInlines cx acc cap.toList
      | none => acc
    let own := spec.groundIn acc.pal .print
    let ground := (own.map (·.1)).orElse fun _ =>
      cx.ground.orElse fun _ => some (Design.printPage acc.pal)
    -- On a ground of its own the plain text sets in the colour both
    -- backends fit to it (`Listing.groundInk`), and is judged as such.
    let cur := match own with
      | some (g, _) =>
        let inherited := (cx.cur.map (·.2.1)).getD
          ((cx.inheritedInk.map (·.2)).getD (Design.printInk acc.pal))
        let name := if (Design.declared? acc.pal .codeInk).isSome then some (.role .codeInk)
          else cx.cur.bind (·.1)
        some (name, Listing.groundInk acc.pal g inherited, acc.runs)
      | none => cx.cur
    let codeCx := { cx.style spec.fontSize with
      ground, cur, groundName := (own.map fun _ => "the listing's ground").or cx.groundName
      codeStyle := spec.style.map (·.name) }
    -- One brush per type for the whole listing, as both backends draw it;
    -- the palette changes only at a `.setPalette`, never inside a listing.
    let lines := spec.tokenLines source
    let brushes := Listing.brushes acc.pal ground covered spec.style lines
    lines.foldl (fun acc line =>
      usesInlines codeCx acc
        ((Listing.paintLine acc.pal ground covered spec.style brushes
          line).flatMap fun r => Listing.paintRun r #[.text r.text]).toList) acc
  | .note _ | .rule _ _ _ | .logo _ | .picture _
  | .pagebreak => acc

private def usesItems (cx : UseCx) (acc : UseAcc) :
    List (Array Block) → UseAcc
  | [] => acc
  | item :: rest => usesItems cx (usesBlocks cx acc item.toList) rest

private def usesColumns (cx : UseCx) (acc : UseAcc) :
    List (BoxWidth × Array Block) → UseAcc
  | [] => acc
  | (_, body) :: rest => usesColumns cx (usesBlocks cx acc body.toList) rest

end

/-- Whether the document is shown as a deck's stage: the frame page model,
whose text the judge reads at the size its screen shows it (`UseCx.large`,
`Need.atStage`). -/
public def stageOf (doc : Doc) : Bool := doc.docClass.record.model == .frame

/-- The body walk: every coloured use with the epoch it stood in, the
epoch boundaries, and the design sites each epoch ships, read off
`doc.body` once. One site, so the judge and the judged-pair census read
the same walk and not two copies of it. -/
private def docWalk (doc : Doc) : UseAcc :=
  let hasFrameFoot := doc.body.any fun b => match b with
    | .framefoot xs => !xs.isEmpty
    | _ => false
  let cx : UseCx :=
    { base := doc.page.fontSize, size := doc.page.fontSize
      slides := stageOf doc
      chromeFoot := doc.docClass.record.chrome && doc.foot.isNone &&
        (doc.chrome.hasFooter || hasFrameFoot) }
  let walk := usesBlocks cx { pal := doc.palette } doc.body.toList
  -- A page that ships no stylesheet of the engine's draws no focus ring, and
  -- a document whose declared formats name no HTML ships no page to draw it.
  -- premise: Tests.DeclaredColors.focusGateChecks — the css=none page holds no focus rule where the default page holds one, and a pdf-only declaration builds no HTML
  if doc.output.css == some "none" ||
      (!doc.output.formats.isEmpty && !doc.output.formats.contains "html") then
    { walk with linkPals := #[] } else walk

/-- The uses the document plan enumerates: the body walk's, plus running
heads and feet and the chrome footer. The chrome footer reads its frame's
epoch and band ground; running heads and feet are document state and read
epoch 0. One site, read by the per-use judge and by the judged-pair census. -/
private def docUses (doc : Doc) (walk : UseAcc) : UseAcc := Id.run do
  let base : UseCx := { base := doc.page.fontSize, size := doc.page.fontSize, slides := stageOf doc }
  let mut acc := { walk with pal := doc.palette }
  for pal in walk.footPals do
    let look := (Design.ofPalette pal).footline
    let key : ColorRef := if (Design.declared? pal .muted).isSome then .role .muted else .role .ink
    let cx := { base with
      size := Ir.scaleStep doc.page.fontSize Ir.footline.step
      ground := look.bar, groundName := look.bar.map (fun _ => "the footline") }
    acc := { acc with pal := pal }
    acc := { acc.use cx (some key) look.fg with runs := acc.runs + 1 }
  acc := { acc with pal := doc.palette }
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
public def effectivePair (doc : Doc) : ColorPair :=
  { fg := (Design.ofDoc doc).fg, bg := (Design.at doc.palette .light .page).getD Color.white }

/-- A design site as the document judge reads it: the print site
(`Design.site?`) at its medium's need (`Need.atStage`), with an undeclared
page read as the shipped light surface (`surfaceOf`). That is what the
artifacts ship under a `none` ground — the PDF leaves white paper, HTML's
body takes the page role's light default (`HtmlDoc.baseCss`) — and the
surface is the darker of the two, so a pair that passes here passes on the
white page too. Grounding on white judged the lighter one and passed titles
the HTML page fails: #757575 reads 4.61:1 on white and 4.41:1 on the
surface it ships on. -/
public def judgedSite? (stage : Bool) (pal : Palette) (r : Role) : Option Site :=
  (Design.site? pal .print r).map fun st =>
    let st := { st with need := st.need.atStage stage }
    if st.on == .page then { st with ground := surfaceOf pal } else st

/-- What WCAG 2.2 asks of a need, as a message spells it. -/
private def needClause : Need → String
  | .text => "text (SC 1.4.3)"
  | .largeText => "large-scale text (SC 1.4.3)"
  | .nonText => "non-text information (SC 1.4.11)"
  | .state => "a state change (SC 1.4.11)"
  | .decorative => "nothing"

/-- What a failing site says, on one line. W0345 for a themed element's
pair (its row's `noun`), W0315 for the page's text, or W0330 when that ink
was never declared: the remedy is then the declaration, which its help
names. The colours ship as stated — the judge reports and never repaints. -/
private def siteVerdict (site : ColorSite) (r : Role) (pal : Palette) (st : Site) : Diag :=
  let key := (ColorRef.role r).key
  let req := requiredIn st.scheme st.need
  let milli := contrastMilli st.ink st.ground
  let clause := needClause st.need
  let span := (site pal (some key) st.ink).map (·.2)
  if r.row.noun.isNone && (Design.declared? pal r).isNone then
    let onKey := (ColorRef.role st.on).key
    Diag.of .W0330
      (s!"the declared page keeps the defaulted ink, below the contrast WCAG 2.2 asks of " ++
        clause)
      (span := (site pal (some onKey) st.ground).map (·.2))
      (detail := some s!"{hexOf st.ink} on {hexOf st.ground}: {ratioString milli}, below {ratioString req}")
      (help := some ("a declared surface chooses its ink: declare " ++
        "\\palette{ " ++ key ++ " = ... }" ++ " beside " ++ onKey))
  else match r.row.noun with
    | some noun =>
      Diag.of .W0345
        (s!"{noun} pairs its ink and ground below the contrast WCAG 2.2 asks of " ++ clause)
        (span := span) (subject := some (inkKey key st.ink st.ground))
        (detail := some s!"{hexOf st.ink} on {hexOf st.ground}: {ratioString milli}, below {ratioString req}")
    | none =>
      Diag.of .W0315
        (s!"text coloured '{key}' reads on the page below the contrast WCAG 2.2 asks of " ++
          clause)
        (span := span) (subject := some (inkKey key st.ink st.ground))
        (detail := some s!"{hexOf st.ink} on {hexOf st.ground}: {ratioString milli}, below {ratioString req}")

/-- **The one site judge.** A shipped design site, judged under the palette
in force where it ships: a site that does not ship there, is declared
decorative, meets its need, or was reported by an earlier epoch says
nothing (`judgeSite_id`); a failing one says its verdict once. -/
private def judgeSite (site : ColorSite) (stage : Bool) (s : Array Diag × Array Site) :
    Role × Palette → Array Diag × Array Site
  | (r, pal) =>
    match judgedSite? stage pal r with
    | some st =>
      if pal.decorative.contains (.role r) || st.passes || s.2.contains st then s
      else (s.1.push (siteVerdict site r pal st), s.2.push st)
    | none => s

/-- A family of sites, judged in order. -/
private def judgeSites (site : ColorSite) (stage : Bool) (xs : Array (Role × Palette)) :
    Array Diag :=
  (xs.foldl (judgeSite site stage) (#[], #[])).1

/-- The sites one shipped event stands for: every registry site of the
palette in force (`Design.sites`, in print), whose row the report reads at
that event (`Row.judged`), in registry order. -/
public def eventSites (ev : Judged) (pal : Palette) : Array (Role × Palette) :=
  ((Design.sites pal .print).filter (·.role.row.judged == ev)).toArray.map (·.role, pal)

/-- The page in every epoch, the document's palette first: the page's text
is judged whether or not the document spelled it — a document that declares
a dark page and leaves the ink defaulted ships black on dark, and the
contract judges what ships. -/
private def pageEvents (doc : Doc) (walk : UseAcc) : Array (Judged × Palette) :=
  (#[doc.palette] ++ walk.epochs).map (.page, ·)

/-- The themed elements, per epoch that ships one, which the per-use walk
cannot see because no body text is coloured with them: each titled block's
title (bold at the body size, under WCAG 2.2's large-scale sizes, so 4.5:1),
each frame title on its bar (`\large\bfseries` is 12pt bold, so 4.5:1), each
standout frame (`\Large\bfseries`, 14.4pt bold, large-scale, so 3:1), each
declared title page (mixed matter, so the body threshold) and the focus ring
of each epoch that ships a link (non-text, 3:1, SC 1.4.11). -/
private def elementEvents (walk : UseAcc) : Array (Judged × Palette) :=
  walk.blockPals.map (fun (k, pal) => (.element (Element.ofTitled k), pal)) ++
    walk.titledPals.map (.element .frameTitle, ·) ++
    walk.standoutPals.map (.element .standout, ·) ++
    walk.titlePagePals.map (.element .titlePage, ·) ++
    walk.linkPals.map (.element .focusRing, ·)

private def pageSites (doc : Doc) (walk : UseAcc) : Array (Role × Palette) :=
  (pageEvents doc walk).flatMap fun (ev, pal) => eventSites ev pal

private def elementSites (walk : UseAcc) : Array (Role × Palette) :=
  (elementEvents walk).flatMap fun (ev, pal) => eventSites ev pal

/-- What a document ships that its report reads sites at, in judging order:
the page in every epoch, then each themed element in the epoch it ships
in, each with the palette in force there. -/
public def shippedEvents (doc : Doc) : Array (Judged × Palette) :=
  let walk := docWalk doc
  let elements := elementEvents walk
  pageEvents doc walk ++ elements

/-- The design sites a document ships, in judging order, each with the
palette in force where it ships: every event's sites (`eventSites`). -/
public def shippedSites (doc : Doc) : Array (Role × Palette) :=
  (shippedEvents doc).flatMap fun (ev, pal) => eventSites ev pal

/-- The covering judged, per epoch that ships pending content: SC 1.4.11's
3:1 between an active and an inactive state, and quieter-than-active —
`coveredContract`'s own two bounds, read from `Design.cover`: the cover
fraction is the author's declaration, so the remedy is theirs to choose
(lower it, or name a quieter colour). The ink's cover is judged wherever an
epoch covers anything; the alert's and the example's where a covered use of
that colour ships (`covered`). -/
private def pendingCoverDiags (site : ColorSite) (doc : Doc) (pending : Array Palette)
    (covered : Array (Palette × ColorRef)) : Array Diag := Id.run do
  let mut out : Array Diag := #[]
  for pal in pending do
    if pal.decorative.contains (.role .covered) then continue
    let d := Design.ofDoc { doc with palette := pal }
    let cov := d.cover
    let coverHelp := some ("a cover is a declaration too: lower " ++
      "'covered = <n>%', or declare \\palette{ covered = ... } " ++
      "quieter than the ink it stands for")
    let judge (nm : String) (active covered : Color) : Array Diag :=
      let origin := (site pal (some "covered") covered).orElse fun _ =>
        site pal (some nm) active
      if contrastMilli covered d.bg ≥ contrastMilli active d.bg then
        #[Diag.of .W0345
          (s!"covering '{nm}' does not quiet it: the covered form " ++
            "reads as loud on the page as the active one")
          (span := origin.map (·.2))
          (subject := some s!"covered:{nm}")
          (help := coverHelp)]
      else
        let milli := contrastMilli active covered
        if milli < aaNonText then
          #[Diag.of .W0345
            (s!"covered '{nm}' reads against its active form below the contrast " ++
              "WCAG 2.2 asks of a state change (SC 1.4.11)")
            (span := origin.map (·.2))
            (subject := some s!"covered:{nm}")
            (detail := some (s!"{hexOf covered} against {hexOf active}: " ++
              s!"{ratioString milli}, below {ratioString aaNonText}"))
            (help := coverHelp)]
        else #[]
    out := out ++ judge "fg" d.fg (cov.of d.fg)
    -- A declared constant cover stands for the plain runs itself: judged
    -- under the key that declared it (undeclared, the plain cover IS the
    -- fg cover just judged).
    if d.covered.isSome then
      out := out ++ judge "covered" d.fg cov.plain
    for (role, r) in [("alert", Role.alert), ("example", Role.example)] do
      if let some c := Design.declared? pal r then
        if covered.contains (pal, .role r) then
          out := out ++ judge role c (cov.of c)
  return out

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
  name : Option ColorRef
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
already reported, and the run each pairing last spoke for. A colour ships as
stated whatever its verdict, so the fold's only output is what it says. -/
private def allLargeOf (uses : Array Use) : Std.HashMap UseKey Bool :=
  -- Whether a pairing stood as large-scale text *everywhere* it was used:
  -- one keyed fold over the uses, so the answer is the whole document's and
  -- the order the uses arrived in cannot change it.
  uses.foldl (fun m v => m.insert v.key (v.large && (m[v.key]?).getD true)) {}

private structure UseJudgeState where
  diags : Array Diag := #[]
  /-- The pairings already reported: the effective pair seeds it, since the
  site judge already spoke for it and a body use of the same pairing must
  not report it twice. -/
  done : Std.HashSet UseKey
  /-- The coloured run each pairing warning last spoke for: a later run of
  the same pairing adds a note, a later use in the same run adds nothing. -/
  sites : Std.HashMap UseKey Nat := {}

/-- A pairing warning at one coloured run: the warning, with the pairing's
first span, at the first run; a note at each later run, under one subject,
so the tally puts the run count on the one line that shows. -/
private def UseJudgeState.pairing (s : UseJudgeState) (dup : Bool) (key : UseKey)
    (run : Nat) (subject message detail : String) (span : Option Span) : UseJudgeState :=
  if dup && s.sites[key]? == some run then s
  else
    let d := Diag.of .W0315 message span (subject := some subject) (detail := some detail)
    { s with diags := s.diags.push (if dup then d.demote else d)
             sites := s.sites.insert key run }

private def useStep (site : ColorSite) (large : Std.HashMap UseKey Bool)
    (s : UseJudgeState) (u : Use) : UseJudgeState :=
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
    let assessment := assessPair threshold u.color u.surface
    if assessment.passes then { s with done := done }
    else
      -- The name a pairing reports is its role's or the author's own
      -- spelling where the elaboration recorded one, never one the engine
      -- invents; an anonymous value reports its hex.
      let origin := site u.pal (u.name.map (·.key)) u.color
      let spelled : Option String := match u.name with
        | some role => some role.key
        | none => origin.map Prod.fst
      let label := match u.styleName, spelled with
        | some st, _ => s!"by the '{st}' highlighting style"
        | none, some e => s!"'{e}'"
        | none, none => s!"'{hexOf u.color}'"
      let s := s.pairing dup key u.site
        (inkKey (spelled.getD (hexOf u.color)) u.color u.surface)
        (s!"text coloured {label} reads on {u.groundName.getD "the page"} below the contrast " ++
          s!"WCAG 2.2 asks of {if allLarge then "large-scale text" else "text"} (SC 1.4.3)")
        (s!"{hexOf u.color} on {hexOf u.surface}: {ratioString assessment.ratio}, " ++
          s!"below {ratioString threshold}")
        (origin.map (·.2))
      { s with done := done }

private def declaredUseJudged (site : ColorSite) (doc : Doc) (walk : UseAcc) : Array Diag :=
  let d := Design.ofDoc doc
  let uses := (docUses doc walk).uses
  (uses.foldl (useStep site (allLargeOf uses))
    { done := ({} : Std.HashSet UseKey).insert
        { name := some (.role .ink),
          pair := { color := d.fg, ground := (effectivePair doc).bg } } }).diags

/-- **The document-level contrast report**, one walk: the uses with their
epochs, the design sites per epoch, and the epoch boundaries are read off
`doc.body` once; then each half judges against the palette in force where
the pairing ships, at the size its medium shows it, and a pairing a themed
element's site names is reported by that site alone. Every colour ships as
the document states it: this is a report, and the document is not an input
it returns. `site` names each pairing's authored expression and span. -/
public def docDiags (doc : Doc) (site : ColorSite := fun _ _ _ => none) : Array Diag :=
  let walk := docWalk doc
  let stage := stageOf doc
  let elements := judgeSites site stage (elementSites walk)
  -- A pairing a themed element's site names is reported there, once: the
  -- use judge's report of that same pairing yields to it.
  let uses := (declaredUseJudged site doc walk).filter fun d =>
    !(elements.any fun e => e.subject.isSome && e.subject == d.subject)
  judgeSites site stage (pageSites doc walk) ++ uses ++ elements ++
    pendingCoverDiags site doc walk.pendingPals walk.coveredNames

/-- The judged pair is the shipped pair: what `effectivePairDiags` judges is
the resolved design's own ink — the field `Layout.run` colours every
uncoloured run with — and, on a declared page, the resolved design's own
surface — the fill `Layout.run` paints the page with. Definitional by
construction (`effectivePair` reads `Design.ofDoc`, the one resolving
site), and stated so the construction cannot drift: a defaulted colour
cannot escape the contract by never being spelled. -/
public theorem judged_pair_is_shipped (doc : Doc) :
    (effectivePair doc).fg = (Design.ofDoc doc).fg ∧
    ((Design.ofDoc doc).bgDeclared = true →
      (effectivePair doc).bg = (Design.ofDoc doc).bg) := by
  refine ⟨rfl, fun h => ?_⟩
  have hdec : (Design.ofDoc doc).bgDeclared = (Design.declared? doc.palette .page).isSome := rfl
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hdec ▸ h)
  have hbg : (Design.ofDoc doc).bg = (Design.at doc.palette .print .page).getD Color.white := rfl
  simp only [effectivePair, hbg, Design.at_declared doc.palette .light .page c hc,
    Design.at_declared doc.palette .print .page c hc]

/-- The site judge grounds a titled title where the per-use walk records it:
both read the kind's bar where the palette declares one, and `surfaceOf`,
the engine's one reading of an unpainted page, where it does not — so the
pair the judge weighs is the pair the reader sees.

Stated because the two drifted: the judge read an unbarred title's page as
`Color.white` while the walk read it as `surfaceOf` (`#FAFAF9`, the surface
`HtmlDoc.baseCss` ships under a `none` ground), and white is the lighter
ground — so a title between the two ratios was judged passing and shipped
failing, with no test, theorem or diagnostic to say so. -/
private theorem titled_ground_agree (acc : UseAcc) (cx : UseCx) (kind : TitledKind)
    (nm : Option ColorRef) (c : Color) (stage : Bool) (st : Site)
    (h : judgedSite? stage acc.pal (Role.titleInk kind) = some st) :
    ((acc.use { cx with ground := (titledLook acc.pal kind).bar } nm c).uses.back?).map
        Use.surface = some st.ground := by
  have hg : (Role.titleInk kind).row.ground = some (Role.titleBar kind) := by cases kind <;> rfl
  have hn : (Role.titleInk kind).row.need.paired = true := by cases kind <;> rfl
  have hp : (Role.titleInk kind).row.presence = .always := by cases kind <;> rfl
  have hb : (Role.titleBar kind == Role.page) = false := by cases kind <;> rfl
  simp only [judgedSite?, Design.site?, hg, hn, hp, Presence.holds, Bool.and_self, ite_true,
    Option.bind_some, Option.map_map] at h
  obtain ⟨ink, -, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [UseAcc.use, titledLook, Array.back?_push, Option.map_some, Function.comp]
  cases Design.at acc.pal .print (Role.titleBar kind) <;> simp [hb]

/-- The judged page under a palette is its declared page, else the shipped
light surface — the ground the effective pair reads. -/
private theorem effectivePair_bg (doc : Doc) : (effectivePair doc).bg = surfaceOf doc.palette :=
  rfl

/-- The page's text, as the site judge reads it: the effective pair, at
its medium's need. -/
private theorem judgedSite_ink (stage : Bool) (doc : Doc) :
    judgedSite? stage doc.palette .ink =
      some { role := .ink, ink := (effectivePair doc).fg, on := .page
             ground := (effectivePair doc).bg, need := Need.text.atStage stage
             scheme := .print } := by
  have hink : Design.at doc.palette .print .ink = some (effectivePair doc).fg := by
    have hfg : (effectivePair doc).fg = (Design.at doc.palette .print .ink).getD Color.black := rfl
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (Design.at_ink_isSome doc.palette .print)
    rw [hfg, hc']
    rfl
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (Design.at_page_isSome doc.palette .print)
  simp [judgedSite?, Design.site?, Role.row, Row.keyed, Need.paired, Presence.holds, hink, hc,
    effectivePair_bg]

/-- A site is its role's. -/
private theorem site?_role {pal : Palette} {s : Scheme} {r : Role} {st : Site}
    (h : Design.site? pal s r = some st) : st.role = r := by
  simp only [Design.site?, Option.bind_eq_some_iff] at h
  obtain ⟨g, _, h⟩ := h
  split at h
  · obtain ⟨ink, _, hst⟩ := Option.map_eq_some_iff.mp h
    split at hst <;> (subst hst; rfl)
  · cases h

private theorem filter_filterMap_role (f : Role → Option Site)
    (hf : ∀ r st, f r = some st → st.role = r) (q : Role → Bool) :
    ∀ l : List Role, (l.filterMap f).filter (fun st => q st.role) = (l.filter q).filterMap f
  | [] => rfl
  | r :: rs => by
    have ih := filter_filterMap_role f hf q rs
    cases h : f r with
    | none => by_cases hq : q r = true <;> simp [h, hq, ih]
    | some st =>
      have hr := hf r st h
      subst hr
      by_cases hq : q st.role = true <;> simp [h, hq, ih]

/-- The page's sites in an epoch: the ink's, alone. -/
private theorem eventSites_page (pal : Palette) :
    eventSites .page pal = ((Design.site? pal .print .ink).toList.map (·.role, pal)).toArray := by
  have h := filter_filterMap_role (Design.site? pal .print) (fun _ _ h => site?_role h)
    (fun r => r.row.judged == .page) Role.all
  simp only [eventSites, Design.sites]
  rw [h, Role.judged_page]
  simp only [List.filterMap_cons, List.filterMap_nil]
  cases Design.site? pal .print .ink <;> simp

/-- A fold's invariant, as an induction the judge's lemmas below
instantiate: a property held by the seed and by every step over the list's
own elements is held by the result. -/
private theorem foldlList_invariant {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (xs : List α) (init : β), P init →
      (∀ b a, a ∈ xs → P b → P (f b a)) → P (xs.foldl f init)
  | [], _, hi, _ => hi
  | a :: as, init, hi, hs =>
    foldlList_invariant P f as (f init a) (hs init a (List.mem_cons_self ..) hi)
      (fun b x hx hb => hs b x (List.mem_cons_of_mem a hx) hb)

/-- A step never retracts a message. -/
private theorem judgeSite_diags_mono (site : ColorSite) (stage : Bool)
    (s : Array Diag × Array Site) (x : Role × Palette) :
    s.1.size ≤ (judgeSite site stage s x).1.size := by
  obtain ⟨r, pal⟩ := x
  simp only [judgeSite]
  split
  · split
    · exact Nat.le_refl _
    · simp
  · exact Nat.le_refl _

/-- The load-bearing form of F3, over every document: when the effective
pair fails the ratio its medium asks of text and the ink is not declared
decorative, `docDiags` reports — declared ink or defaulted, because the
page's text is the first site the judge reads, before the declared-use walk
runs. The missing special case is an impossibility, not a covered branch. -/
public theorem defaulted_ink_cannot_escape (doc : Doc)
    (hdec : doc.palette.decorative.contains (.role .ink) = false)
    (hfail : contrastMilli (effectivePair doc).fg (effectivePair doc).bg <
      required (Need.text.atStage (stageOf doc))) :
    0 < (docDiags doc).size := by
  have hp : ({ role := .ink, ink := (effectivePair doc).fg, on := .page
               ground := (effectivePair doc).bg, need := Need.text.atStage (stageOf doc)
               scheme := .print } : Site).passes = false := by
    simp [Site.passes, requiredIn, Scheme.more, Nat.not_le.mpr hfail]
  have hdec' : ColorRef.role Role.ink ∉ doc.palette.decorative := by simpa using hdec
  have h1 : 0 < (judgeSite (fun _ _ _ => none) (stageOf doc) (#[], #[])
      (Role.ink, doc.palette)).1.size := by
    simp [judgeSite, judgedSite_ink (stageOf doc) doc, hdec', hp]
  obtain ⟨st0, h0⟩ : ∃ st0, Design.site? doc.palette .print .ink = some st0 := by
    have := judgedSite_ink (stageOf doc) doc
    simp only [judgedSite?, Option.map_eq_some_iff] at this
    obtain ⟨st0, h0, _⟩ := this
    exact ⟨st0, h0⟩
  have hr : st0.role = .ink := site?_role h0
  have he : (eventSites .page doc.palette).toList = [(Role.ink, doc.palette)] := by
    rw [eventSites_page, h0]
    simp [hr]
  have hps : ∃ rest, (pageSites doc (docWalk doc)).toList = (Role.ink, doc.palette) :: rest := by
    refine ⟨((docWalk doc).epochs.toList.map (Judged.page, ·)).flatMap
      (fun p => (eventSites p.1 p.2).toList), ?_⟩
    simp only [pageSites, pageEvents, Array.toList_flatMap, Array.toList_map, Array.toList_append,
      List.map_append, List.flatMap_append]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, he,
      List.cons_append, List.nil_append]
  have hE : 0 < (judgeSites (fun _ _ _ => none) (stageOf doc) (pageSites doc (docWalk doc))).size := by
    obtain ⟨rest, hrest⟩ := hps
    unfold judgeSites
    rw [← Array.foldl_toList, hrest, List.foldl_cons]
    exact foldlList_invariant (fun b => 0 < b.1.size) _ _ _ h1
      fun b x _ hb => Nat.lt_of_lt_of_le hb (judgeSite_diags_mono _ _ b x)
  simp only [docDiags, Array.size_append]
  omega

-- The built-in theme bundles, held to the same contract.

/-- **A palette's whole contract**: every pair its design ships in print
(`Design.sites`, generated from the registry's rows) meets its need, every
default applied rather than passed vacuously when a key is absent — body,
muted and marker text and the content colours on the page, the frame-title
bar and its subtitle, the section title, the footline, each titled block's
title and body, the standout inversion (large-scale text, 3:1) and a
declared title page. The progress bar and the separator are decorative:
supplementary position indicators the section title already carries,
outside SC 1.4.11's "required to understand the content", and so is a
block template's rule (`Ir.BlockEdge.ink`), a mark beside a title whose
own text names the block; `covered` is a state, held to visibly-covered
by `coveredContract` below. A role a bundle's lineage declares short of its
need (`reported`, `Theme.reported`) ships as declared and is the document's
report's to name. -/
public def paletteContract (pal : Palette) (reported : List Role := []) : Bool :=
  (Design.sites pal .print).all fun st => st.passes || reported.contains st.role

/-- Every listing ink of every shipped style, declared or the engine's
default, is text-AA on every listing ground of a bundle: the page, its
standout inversion, and its title page when declared. A colour the bundle
declares ships as declared, which this holds to AA on every such ground;
every other colour the shared painter adapts there. -/
public def listingContract (pal : Palette) : Bool :=
  let d := Design.ofPalette pal
  (none :: ListingStyle.all.map some).all fun style =>
    Listing.contract pal none style && Listing.contract pal (some d.standout.bg) style
      && (match d.titlepage with
          | some p => Listing.contract pal (some p.bg) style
          | none => true)

public def Theme.contractHolds (th : LeanTex.Core.Theme.Theme) : Bool :=
  paletteContract (th.realize .documents) th.reported &&
    paletteContract (th.realize .decks) th.reported

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
bundle — moloch's 31% — never a reason to weaken this contract. A colour a
bundle's lineage declares short of its need on the page (`reported`) has no
cover 3:1 from it there: it is held to quieting alone, and the document's
report names a covered use of it. -/
public def coveredContract (pal : Palette) (reported : List Role := []) : Bool :=
  let d := Design.ofDoc { palette := pal }
  let cov := d.cover
  let visiblyCovered (r : Role) (c : Color) : Bool :=
    contrastMilli (cov.of c) d.bg < contrastMilli c d.bg
      && (reported.contains r || contrastMilli c (cov.of c) ≥ aaNonText)
  visiblyCovered .ink d.fg
    && (match Design.declared? pal .alert with | some c => visiblyCovered .alert c | none => true)
    && (match Design.declared? pal .example with | some c => visiblyCovered .example c | none => true)
    && contrastMilli cov.plain d.bg < contrastMilli d.fg d.bg
    && contrastMilli d.fg cov.plain ≥ aaNonText

/-- Covering twice quiets further: the cover of a covered colour reads
quieter against the page than the cover itself, for every text role the
bundle ships — the monotonicity that makes "more covered" mean what it
says. The general integer statement needs luminance monotonicity through
the whole pipeline (a refactor, tracked in PLAN, not claimed here); this
is its per-bundle kernel check, with a property test over random colours
in `Tests.lean` beside it. -/
public def coverMonotone (pal : Palette) : Bool :=
  let d := Design.ofDoc { palette := pal }
  let cov := d.cover
  let quieter (c : Color) : Bool :=
    contrastMilli (cov.of (cov.of c)) d.bg < contrastMilli (cov.of c) d.bg
  quieter d.fg
    && (match Design.declared? pal .alert with | some c => quieter c | none => true)
    && (match Design.declared? pal .example with | some c => quieter c | none => true)

/-- The coloured uses the walk met, each as the pair it stood in: its colour
on the ground it stood on, the running head and foot and the chrome footer
included (`docUses`). -/
public def usePairs (doc : Doc) : Array (Color × Color) :=
  (docUses doc (docWalk doc)).uses.map fun u => (u.color, u.surface)

/-- The (ink, ground) pairs the document-level contrast judge enumerates, as
data: every design site the document ships (`shippedSites`, as the judge
reads it) and every coloured use (`usePairs`). This is the domain of the
document's contrast report, not a census of placed glyphs or of emitted
diagnostics. Overlay dimming computes additional colours, picture labels
have their own paint, and exempt uses need not emit a diagnostic.
`contrastContractChecks` pins actual placed counterexamples to the former
claim that this domain contains every shipped pair. -/
public def judgedPairs (doc : Doc) : Array (Color × Color) :=
  let uses := usePairs doc
  (shippedSites doc).filterMap (fun x =>
      (judgedSite? (stageOf doc) x.2 x.1).map fun st => (st.ink, st.ground))
    ++ uses

/-- **The judged pairs cover the registry's sites where they ship**
(`_covers`): for every event the document ships — the page in each epoch,
each themed element in the epoch it ships in — every site the registry
generates for the palette in force there (`Design.sites`) whose row the
report reads at that event (`Row.judged`) is a judged pair, at its medium's
need, and so is every coloured use the walk met. A role added to the
registry enters the report the way its row says, with no list here to
extend; `Design.sites_covers` says which roles have a site. -/
public theorem judged_covers (doc : Doc) :
    (∀ ev ∈ shippedEvents doc, ∀ st ∈ Design.sites ev.2 .print, st.role.row.judged = ev.1 →
      ∀ st', judgedSite? (stageOf doc) ev.2 st.role = some st' →
        (st'.ink, st'.ground) ∈ judgedPairs doc) ∧
    ∀ p ∈ usePairs doc, p ∈ judgedPairs doc := by
  refine ⟨fun ev hev st hst hj st' h' => ?_, fun p hp => Array.mem_append_right _ hp⟩
  have hsite : (st.role, ev.2) ∈ shippedSites doc := by
    unfold shippedSites
    refine Array.mem_flatMap.mpr ⟨ev, hev, ?_⟩
    obtain ⟨e, pal⟩ := ev
    simp only [eventSites, Array.mem_map, List.mem_toArray, List.mem_filter, beq_iff_eq]
    exact ⟨st, ⟨hst, by simpa using hj⟩, rfl⟩
  exact Array.mem_append_left _ (Array.mem_filterMap.mpr ⟨_, hsite, by rw [h']; rfl⟩)

/-- **A passing site is the identity** (`_id`): a site that does not ship,
is declared decorative, or meets its need leaves the judging state exactly
as it was — no message and no dedup entry — so the report cannot name a
pair that meets what its medium asks. -/
private theorem judgeSite_id (site : ColorSite) (stage : Bool) (s : Array Diag × Array Site)
    (r : Role) (pal : Palette) (h : ∀ st, judgedSite? stage pal r = some st → st.passes = true) :
    judgeSite site stage s (r, pal) = s := by
  cases hst : judgedSite? stage pal r with
  | none => simp [judgeSite, hst]
  | some st => simp [judgeSite, hst, h st hst]

/-- What a document's palette amounts to in the schemes an artifact ships,
for the driver's `palette:` phase line: how many roles resolve, how many
sites their pairs create, and the least margin any site keeps above what its
need owes, in thousandths of a ratio (none when no site is paired). -/
public structure PaletteSummary where
  roles : Nat
  schemes : Nat
  sites : Nat
  margin : Option Int
  seeded : Bool
  deriving Repr, BEq

public def paletteSummary (pal : Palette) (schemes : List Scheme) : PaletteSummary :=
  let sites := schemes.flatMap (Design.sites pal)
  let margins := sites.map fun st => (contrastMilli st.ink st.ground : Int) - requiredIn st.scheme st.need
  { roles := (Role.all.filter fun r => schemes.any fun s => (Design.at pal s r).isSome).length
    schemes := schemes.length
    sites := sites.length
    margin := margins.min?
    seeded := pal.seeded.isSome }

/-- The phase line's words: roles, schemes, sites, the least margin — or,
where a site falls short of its need, by how much. -/
public def PaletteSummary.detail (p : PaletteSummary) : String :=
  let margin := match p.margin with
    | some m =>
      if m < 0 then s!"a site {ratioString (-m).toNat} short of its need"
      else s!"least margin {ratioString m.toNat}"
    | none => "no paired site"
  s!"{p.roles} roles, {p.schemes} scheme{if p.schemes == 1 then "" else "s"}, {p.sites} sites, " ++
    margin ++ (if p.seeded then ", generated from seeds" else "")

end LeanTex.Core.Contrast
