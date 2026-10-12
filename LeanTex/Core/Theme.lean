module

public import LeanTex.Core.Ir
import all LeanTex.Core.Ir
import LeanTex.Core.ContrastSolve

namespace LeanTex.Core.Theme

open LeanTex.Core.Ir LeanTex.Core.Dim

/-- The four declaration surfaces a `\theme` installs onto: what the
document has declared at the theme site, and what its later declarations
keep overriding. Values in, values out — the install is `apply` below, a
function of these alone. A `Theme` extends this record: a bundle is the
same four surfaces plus a name.

A theme fixes no page, by construction — a declared design decision this
record's own shape carries, not a theorem: a class fixes the page model and
nothing a theme may override. This structure is `apply`'s whole domain and
codomain, and it carries no page, no class, and no assertion, so a bundle
*cannot* reach the geometry or the class's implied contract
(`Ir.DocClass.record`) — the compiler enforces the rule at the type, the
same way `DocClass` closes the class set, and a key a bundle installs names
its surface by the closed `DeclSurface`. Keep it that way: a bundle wanting
geometry is a genre or class question, never a theme field (the
value-vs-consumer layering rule; audit-layer's `Theme.apply`/W0348 fixed
the value-vs-value face, and W0355 names the consumer face at install). -/
public structure Decls where
  palette : Palette := {}
  tokens : Tokens := {}
  styles : Styles := {}
  /-- The slide footer's slots, declared data (`\chrome`), not colour: no
  theorem ranges over it. -/
  chrome : Chrome := {}
  deriving Repr, BEq

/-- A theme is data: palette, tokens, element styles, and chrome as the
*values* the engine runs on, installed at the `\theme` site through the same
replace-on-redeclare path a document's own declarations use. A document's
later declarations override, so a theme is a default, never a lock — and a
new theme is a new table here, values only, no code. Values rather than
surface strings so a theorem about a bundle ranges over what `\theme`
installs (`Contrast.builtin_palettes_contract` closes by `decide` over
these entries, for every bundle in `builtin` at once);
colour arithmetic a bundle wants (xcolor's `!` mixes) is evaluated right
here, at definition time, with the same `Color.mix` step
`Ir.Palette.resolve` folds at document use sites. The semantic palette keys
are the whole contract with the backends: `fg`/`bg` colour text and page,
declaring `frametitlebg` turns the frame title into a colour bar,
`progressfg`/`bg` draw the section-page progress bar (`progressheight`
sizes it), `standoutfg`/`bg` invert a `[standout]` frame, and `muted`
quiets secondary furniture — the chrome footer draws in it. -/
public structure Theme extends Decls where
  name : String
  /-- The frame-alignment keys the bundle's inner theme sets: beamer's own
  unless the lineage redefines them, as moloch's `[c]` does. -/
  frameKeys : Ir.FrameKeys := .beamer
  /-- The seeds the bundle's palette is generated from, with its block style
  (`SeedPalette`): the bundle's own palette entries stand over what they
  generate. -/
  seeds : Option (SeedPalette.Seeds × SeedPalette.Blocks) := none
  /-- The roles the bundle derives from a lineage colour rather than states:
  each the colour realized as text on the bundle's page at the generated
  text target, its hue held (`ContrastSolve.realizeNearest`). -/
  derived : List (Ir.Role × Color) := []

/-- The palette a bundle's seeds generate at a depth, derived afresh. -/
public def Theme.generatedFresh (th : Theme) (d : GroundDepth) : Option SeedPalette.Colors :=
  th.seeds.bind fun (s, _) => ((SeedPalette.generate s (s.targets d)).toOption).map (·.colors)

/-- The colour a bundle derives from a lineage colour, derived afresh: the
colour realized as text on the bundle's page at the generated text target,
its hue held; the colour itself where nothing realizes it. -/
public def Theme.derivedFresh (th : Theme) (seed : Color) : Color :=
  (ContrastSolve.realizeNearest (Contrast.aaText + SeedPalette.margin)
    (Design.printPage th.palette) seed).getD seed

/-- The palette a bundle's seeds generate at a depth: the generator's answer
kept in `PaletteData`, else derived as asked. -/
public def Theme.generated (th : Theme) (d : GroundDepth) : Option SeedPalette.Colors :=
  match PaletteData.bundleGenerated.find? (fun e => e.1 == th.name && e.2.1 == d) with
  | some e => some e.2.2
  | none => th.generatedFresh d

/-- The colour a bundle derives for a role: the realization kept in
`PaletteData`, else derived as asked. -/
public def Theme.derivedColor (th : Theme) (r : Ir.Role) (seed : Color) : Color :=
  match PaletteData.bundleDerived.find? (fun e => e.1 == th.name && e.2.1 == r) with
  | some e => e.2.2
  | none => th.derivedFresh seed

/-- **What a bundle declares at a depth**: the palette its seeds generate,
its own entries over it, and each colour it derives from a lineage colour —
seeds and relations, realized where a document installs the bundle. -/
public def Theme.realize (th : Theme) (d : GroundDepth) : Palette :=
  let gen : Palette := match th.seeds, th.generated d with
    | some (seeds, blocks), some colors =>
      ({} : Palette).applySeeds { seeds, targets := seeds.targets d, blocks, colors }
    | _, _ => {}
  let lit := th.palette.entries.foldl (fun p e => p.declare e.1 e.2) gen
  let full := th.derived.foldl (fun p e => p.declare (.role e.1) (th.derivedColor e.1 e.2)) lit
  { full with coveredFraction := th.palette.coveredFraction, decorative := th.palette.decorative }

/-- `{\large\bfseries}` (`{\Large\bfseries}` for `large := "Large"`) as the
elaborator reads a `\style` font value: nested wrappers with an empty body
where the element's own content goes. -/
private def boldFont (size : String) : ElementStyle :=
  { font := some #[.styled (.size size) #[.styled .bold #[]]] }

private def pt1 : Dim.SymGlue := { width := Length.ofSp (Dim.pt 1) }

/-- The moloch lineage's furniture weights and title-page gaps, one named
dtx-sourced table: a 1pt progress bar (`progressbar linewidth`,
beamerouterthememoloch.dtx, `\moloch@outer@setdefaults`), a 0.5pt hairline
separator (its default linewidth), the frame-title bar's padding
(`\moloch@frametitle@margin@top`/`@bottom` = `\ht\strutbox` in the
frametitle font, beamerouterthememoloch.dtx `frametitle` template —
`Ir.frameTitlePadding`, em of the title size), and the title page's
inter-part gaps from beamerinnerthememoloch.dtx — 0.3em above the
subtitle, 0.8em below the separator, 0.5em below the author, 1em below the
institute. `moloch` installs it because these are its own source's values;
`daylight` installs the same table because its rhythm is deliberately the
lineage's, not a knob of its own — one edit site for a dtx correction. -/
private def lineageTokens : Tokens := { entries := #[
  ("progressheight", pt1),
  ("frametitlepadding", Ir.frameTitlePadding),
  ("separatorheight", { width := Length.ofSp (Dim.pt 1 / 2) }),
  ("subtitlegap", { width := { em := 300 } }),
  ("separatorgap", { width := { em := 800 } }),
  ("authorgap", { width := { em := 500 } }),
  ("institutegap", { width := { em := 1000 } })] }

/-- The footline every shipped bundle declares, read as data from the
metropolis lineage (beamerouterthememoloch.dtx, `footline` template:
`\usebeamertemplate*{frame footer}` `\hfill` `\usebeamertemplate*{page
number in head/foot}`): the left slot is the author's `\framefoot` and
nothing else — the template names no section slot, so an undeclared frame's
footer-left is empty, as the lineage renders it — and the right slot is
the frame number. One value, three installs; `footline_left_contract`
holds every shipped bundle to the template. A section title in the footer
would be an engine embellishment a document opts into (`\chrome{ footer =
{ left = \sectiontitle } }`), never a bundle's claim about its source. -/
private def builtinChrome : Chrome :=
  { footerLeft := none
    footerRight := some .frameNumber }

/-- The Metropolis lineage as a token bundle: an inverted frame-title bar,
one warm accent, a near-white page. Values map the moloch beamer theme's
light preset onto the semantic keys, mixes evaluated (the original xcolor
spelling rides in the comment beside each); the lineage's warm colour is a
seed its decorative marks take exactly and its alert derives from. -/
public def moloch : Theme :=
  let fg : Color := { r := 0x23, g := 0x37, b := 0x3B }
  let bg := Color.black.mix 2 Color.white                     -- black!2
  -- mLightBrown (beamercolorthememoloch.sty), the lineage's one warm colour:
  -- the progress bar and the title separator in it exactly, as lualatex
  -- draws them — decorative marks, owing no contrast.
  let lineage := Color.ofHtml 0xEB 0x81 0x1B
  let progressbg := (lineage.mix 50 .black).mix 30 .white      -- progressfg!50!black!30
  { name := "moloch"
    palette := {
      entries := #[
        (.role .ink, fg), (.role .page, bg),
        (.role .example, { r := 0x00, g := 0x80, b := 0x80 }),
        -- The muted step: the theme's own ink mixed 70:30 into its page, a
        -- declared quieting that keeps 4.79:1 on this page, a pinned margin
        -- over the 4.6:1 a generated text ink stands at
        -- (`ThemeContract.builtin_muted_margin`).
        (.role .muted, fg.mix 70 bg),                              -- fg!70!bg
        (.role .frameTitleInk, bg), (.role .frameTitleBar, fg),
        (.role .progressFill, lineage), (.role .progressTrack, progressbg),
        (.role .separator, lineage),
        (.role .standoutInk, bg), (.role .standoutGround, fg)]
      -- Covered overlay content keeps each colour at 31% of itself over
      -- the page, mixed in Oklab (Core/Oklab.lean). Material's
      -- disabled-state opacity is 38% (m2.material.io/design/interaction/
      -- states.html#disabled), but at 38% this bundle's alert and example
      -- read under the 3:1 WCAG 2.2 SC 1.4.11 asks of state-identifying
      -- information against their active forms; 31% is the largest
      -- fraction where every text role clears it
      -- (`Contrast.builtin_designs_covered` is the check).
      coveredFraction := some 31 }
    -- The lineage's alert is the warm colour itself, which reads at 2.61:1 on
    -- this page, under the 4.5:1 WCAG 2.2 SC 1.4.3 asks of text: the alert
    -- is that colour realized as text here, its hue held.
    derived := [(.alert, lineage)]
    tokens := lineageTokens
    frameKeys := .moloch
    styles := { entries := #[
      ("frametitle", boldFont "large"),
      ("sectionpage", boldFont "Large"),
      ("standout", boldFont "Large"),
      -- moloch's `title page` template sets the title matter ragged left
      -- and draws a separator rule between the title block and the author
      -- block, in the palette's separator colour.
      ("titlepage", { align := some .left
                      separator := some (lineage, some (.role .separator)) })] }
    chrome := builtinChrome }

/-- A quieter default: near-black ink on white, one restrained accent, no
title bar — frame titles set as plain bold headings because the bar key is
simply absent. A third theme costs exactly one more table like this. -/
public def plain : Theme :=
  let fg : Color := { r := 0x1B, g := 0x1B, b := 0x1F }
  let bg : Color := { r := 0xFF, g := 0xFF, b := 0xFF }
  { name := "plain"
    palette := {
      entries := #[
        (.role .ink, fg), (.role .page, bg), (.role .alert, { r := 0xB3, g := 0x26, b := 0x1E }),
        (.role .example, { r := 0x20, g := 0x5E, b := 0x3B }),
        -- Same muted rule as moloch: ink 70:30 into the page (6.36:1 here).
        (.role .muted, fg.mix 70 bg),                              -- fg!70!bg
        (.role .progressFill, fg.mix 60 .white),                     -- fg!60
        (.role .progressTrack, fg.mix 15 .white),                     -- fg!15
        (.role .separator, fg.mix 40 .white),                      -- fg!40
        (.role .standoutInk, bg), (.role .standoutGround, fg)]
      -- Covered keeps each colour at 38% of itself over the page — the
      -- Material disabled-state opacity, per colour in Oklab; this
      -- bundle's roles all clear the 3:1 state change at 38%
      -- (Contrast.builtin_designs_covered is the kernel check).
      coveredFraction := some 38 }
    tokens := { entries := #[("progressheight", pt1)] }
    styles := { entries := #[
      ("sectionpage", boldFont "Large"),
      ("standout", boldFont "Large")] }
    chrome := builtinChrome }

/-- A bright, warm default for decks: warm paper, warm near-black ink, one
azure accent — quiet chrome, no title bar (the bar key is deliberately
absent: hierarchy rides size and weight). Its palette is generated from its
four seeds (`SeedPalette`): the page and ink are the warm-neutral family
practice (Tailwind's `stone`; Material's own on-surface is never pure black),
the accent a link-blue azure, the example GOV.UK's `success` green verbatim;
its blocks are tonal cards, its secondary ink the quietest tone that reads,
and its standout frame the inversion on the accent. The slides class installs
this bundle when a deck declares no theme; `moloch` stays by name. -/
public def daylight : Theme :=
  let fg : Color := { r := 0x29, g := 0x25, b := 0x24 }     -- stone-800
  let bg : Color := { r := 0xFD, g := 0xFC, b := 0xF9 }     -- warm near-white
  let accent : Color := { r := 0x0B, g := 0x66, b := 0xC2 } -- azure
  let success : Color := { r := 0x0F, g := 0x7A, b := 0x52 } -- GOV.UK success
  { name := "daylight"
    seeds := some ({ ink := fg, paper := bg, accent, exampleColor := some success }, .tonal)
    palette := {
      entries := #[(.role .standoutInk, bg), (.role .standoutGround, accent)]
      coveredFraction := some 38 }
    -- The lineage's rhythm, not this bundle's own knob: the shared table
    -- makes the docstring's claim true in code.
    tokens := lineageTokens
    styles := { entries := #[
      -- No frametitle bar: the title sets as a plain bold heading in the
      -- ink (the absent `frametitlebg` key is the declaration).
      ("frametitle", boldFont "large"),
      ("sectionpage", boldFont "Large"),
      ("standout", boldFont "Large"),
      ("titlepage", { align := some .left
                      separator := some (accent, some (.role .separator)) })] }
    chrome := builtinChrome }

/-- The Gemini poster lineage as a token bundle: a blue headline band with
near-white text, blue block titles on the page, alert and example blocks
carrying the band's pair. Values map beamercolorthemegemini.sty
(github.com/anishathalye/gemini) onto the semantic keys, each entry's
original spelling beside it; the poster class is the intended consumer
(its headline band and titled blocks read exactly these roles), and the
bundle deliberately declares no chrome and no slides furniture styles —
the poster class never draws them (W0355 names an install that would be
inert). -/
public def gemini : Theme :=
  let blue : Color := { r := 0x40, g := 0x73, b := 0x9E }      -- blue, RGB 64,115,158
  let lightgray : Color := { r := 0xF5, g := 0xF6, b := 0xFA } -- lightgray, RGB 245,246,250
  let darkblue : Color := { r := 0x27, g := 0x3C, b := 0x75 }  -- darkblue, RGB 39,60,117
  let fg := Color.black                                        -- palette primary fg=black
  let bg := Color.white                                        -- palette primary bg=white
  { name := "gemini"
    palette := {
      entries := #[
        (.role .ink, fg), (.role .page, bg),
        -- The lineage leaves alerted/example text to beamer's defaults
        -- (beamercolorthemedefault.sty: `alerted text` fg=red, `example
        -- text` fg=green!50!black). red reads 4.00:1 on this page, under
        -- the 4.5:1 WCAG 2.2 SC 1.4.3 asks of text; this is the same hue
        -- at the nearest lightness that clears it on this ground
        -- (ContrastSolve.realizeNearest; 4.53:1), moloch's alert precedent.
        (.role .alert, { r := 0xEE, g := 0x00, b := 0x00 }),
        (.role .example, { r := 0x00, g := 0x80, b := 0x00 }),      -- green!50!black
        -- The same 70:30 ink-into-page muted rule the other bundles use
        -- (8.45:1 here); gemini declares no muted step of its own.
        (.role .muted, fg.mix 70 bg),                               -- fg!70!bg
        (.role .frameTitleInk, lightgray), (.role .frameTitleBar, blue),   -- headline fg/bg
        (.role .blockTitleInk, blue),                                -- block title fg=blue (bg=white: the page, no bar)
        (.role .alertTitleInk, lightgray), (.role .alertTitleBar, blue),   -- block alerted title
        (.role .exampleTitleInk, blue), (.role .exampleTitleBar, lightgray), -- block example title
        (.role .standoutInk, bg), (.role .standoutGround, fg),                -- palette tertiary bg=black,fg=white
        (.role .separator, darkblue)]                               -- headline rule bg=darkblue
      -- Covered overlay content keeps each colour at 30% of itself over
      -- the page, mixed in Oklab. At Material's 38% disabled-state
      -- default this bundle's alert and example read at 2.70:1 and
      -- 2.99:1 against their active forms — under the 3:1 WCAG 2.2
      -- SC 1.4.11 asks of state-identifying information; 30% is the
      -- largest fraction where every text role clears it
      -- (Contrast.builtin_designs_covered is the kernel check).
      coveredFraction := some 30 }
    styles := { entries := #[
      -- The headline band centres its title matter (beamerthemegemini.sty,
      -- headline template: the logo columns keep space on both sides "to
      -- keep title centered") — declared here, the alignment token the
      -- band reads, never a hard-coded centring. The separator is the
      -- lineage's headline rule, in its own colour.
      ("titlepage", { align := some .center
                      separator := some (darkblue, some (.role .separator)) })] } }

public def builtin : List Theme := [moloch, plain, daylight, gemini]

/-- `footline_left_contract`: no shipped bundle declares a footer-left
datum. The lineage's footline template (beamerouterthememoloch.dtx,
`\defbeamertemplate{footline}{plain}`) has exactly two slots — the
author's `frame footer` and the frame number — so a bundle that cites it
owes an empty left slot; a bundle wanting a section title there would be
adding to its source and must say so as an opt-in, not as data read from
the dtx. Quantified over `builtin`: adding a bundle enters the contract. -/
public theorem footline_left_contract : ∀ th ∈ builtin, th.chrome.footerLeft = none := by
  intro th h
  simp only [builtin, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> rfl

public def find? (name : String) : Option Theme :=
  builtin.find? (·.name == name)

public def names : List String := builtin.map (·.name)

/-- Key-wise onto the element's existing entry: the theme's key wins where
both declare it (the positional last-writer rule every palette entry
follows), and the document's survives where the theme is silent — over
every field of `ElementStyle`, the same merge a later `\style` block
performs against the running entry. Built positionally, so a field added
to the record is a compile error here rather than a silently dropped key:
the structure-instance spelling this replaces omitted `color` and erased a
link colour at every install. -/
public def styleMerge (top base : ElementStyle) : ElementStyle :=
  ElementStyle.mk (top.font <|> base.font) (top.before <|> base.before)
    (top.after <|> base.after) (top.rule <|> base.rule)
    (top.rulePosition <|> base.rulePosition) (top.ruleThickness <|> base.ruleThickness)
    (top.marker <|> base.marker) (top.indent <|> base.indent) (top.gap <|> base.gap)
    (top.align <|> base.align) (top.separator <|> base.separator)
    (top.ruleAbove <|> base.ruleAbove) (top.ruleAboveSkip <|> base.ruleAboveSkip)
    (top.ruleAboveGap <|> base.ruleAboveGap) (top.ruleBelow <|> base.ruleBelow)
    (top.ruleBelowGap <|> base.ruleBelowGap) (top.ruleBelowSkip <|> base.ruleBelowSkip)
    (top.authorFont <|> base.authorFont) (top.authorStrut <|> base.authorStrut)
    (top.bodySize <|> base.bodySize) (top.hover <|> base.hover) (top.focus <|> base.focus)
    (top.motion <|> base.motion) (top.color <|> base.color)
    (if top.slots.isEmpty then base.slots else top.slots)
    (top.shape <|> base.shape)

private def installPalette (p : Palette) : List (ColorRef × Color) → Palette
  | [] => p
  | (k, c) :: es => installPalette (p.declare k c) es

private def installTokens (t : Tokens) : List (String × Dim.SymGlue) → Tokens
  | [] => t
  | (k, g) :: es => installTokens (t.declare k g) es

private def installStyles (s : Styles) : List (String × ElementStyle) → Styles
  | [] => s
  | (k, st) :: es =>
    installStyles (s.declare k (styleMerge st ((s.find? k).getD {}))) es

/-- The bundle-palette install: entries fold through `Palette.declare`, and
the bundle's covered fraction rides with them (`<|>`: a document's earlier
`covered = <n>\%` yields, its later one overrides). Its own function so the
layering statements below take it whole. -/
private def paletteApply (bp p : Palette) : Palette :=
  let pal := installPalette p bp.entries.toList
  { pal with coveredFraction := bp.coveredFraction <|> pal.coveredFraction
             seeded := bp.seeded <|> pal.seeded }

/-- The bundle-chrome install: per slot, the same shape as every palette
entry — the bundle's slot wins where it declares one, the document's
survives where it is silent. -/
private def chromeApply (bc c : Chrome) : Chrome :=
  { footerLeft := bc.footerLeft <|> c.footerLeft
    footerRight := bc.footerRight <|> c.footerRight
    standoutNote := bc.standoutNote <|> c.standoutNote }

/-- The `\theme` install as a value: the bundle's entries fold onto the
document's declarations through the same replace-on-redeclare doors the
document's own blocks use (`Palette.declare`, `Tokens.declare`,
`Styles.declare`), the bundle's covered fraction rides with its palette,
styles merge key-wise onto any entry already declared, and the bundle's
chrome merges per slot — a slot the bundle declares wins, as any later
declaration does, and a slot it leaves silent keeps the document's,
instead of the band replacing wholesale. Values in, values out, no
elaborator state — effects as data: `Elab` calls exactly this function at
the `\theme` site, so a statement about layering ranges over the install
the engine runs. -/
public def apply (th : Theme) (s : Decls) : Decls :=
  { palette := paletteApply (th.realize s.palette.classColors.depth) s.palette
    tokens := installTokens s.tokens th.tokens.entries.toList
    styles := installStyles s.styles th.styles.entries.toList
    chrome := chromeApply th.chrome s.chrome }

/-- A bundle's generated palette under a document: an element's generated
ink whose ground the document declares gives way, for it was chosen for the
bundle's ground (`SeedPalette.bindings`), and an ink the engine derives is
solved on the ground it stands on — the registry's default for the declared
ground (`Row.ground`). A bundle that generates nothing installs as it is. -/
private def underDocument (th : Theme) (real doc : Palette) : Palette :=
  if th.seeds.isNone then real else
    { real with entries := real.entries.filter fun (k, _) => match k with
        | .role r => !(SeedPalette.elementRoles.contains r && r.row.ground.any fun g =>
            SeedPalette.elementRoles.contains g && (Design.declared? doc g).isSome)
        | .color _ => true }

private theorem underDocument_decorative (th : Theme) (real doc : Palette) :
    (underDocument th real doc).decorative = real.decorative := by
  unfold underDocument
  split <;> rfl

/-- A class-default bundle installs *under* the document: the document's
own declarations win per key — `apply` with the priorities mirrored,
because the author never wrote this bundle and a default must not replace
a declaration. `\theme{...}` keeps `apply`'s positional rule; only the
class-default site calls this. -/
public def applyUnder (th : Theme) (s : Decls) : Decls :=
  { palette :=
      let real := underDocument th (th.realize s.palette.classColors.depth) s.palette
      let pal := installPalette real s.palette.entries.toList
      { pal with
        coveredFraction := s.palette.coveredFraction <|> real.coveredFraction
        decorative := s.palette.decorative ++ pal.decorative
        seeded := s.palette.seeded <|> real.seeded
        classColors := s.palette.classColors }
    tokens := installTokens th.tokens s.tokens.entries.toList
    styles := installStyles th.styles s.styles.entries.toList
    chrome := chromeApply s.chrome th.chrome }

/-- The four declaration surfaces a `\theme` installs onto (`Decls`), closed:
a key a bundle declares lives on one of them by type, so a bundle cannot
reach the page model or the class's contract. -/
public inductive DeclSurface where
  | palette
  | tokens
  | style
  | chrome
  deriving Repr, DecidableEq, Inhabited

/-- The surface's spelling: the declaration block it is written in. -/
public def DeclSurface.name : DeclSurface → String
  | .palette => "palette"
  | .tokens => "tokens"
  | .style => "style"
  | .chrome => "chrome"

/-- Every `(surface, key)` the bundle installs at a depth — `(.palette,
"alert")`, `(.chrome, "footer.left")` — whatever stood there before: the
keys whose standing value is the theme's after `apply`. -/
public def declares (th : Theme) (d : GroundDepth) : Array (DeclSurface × String) := Id.run do
  let mut out : Array (DeclSurface × String) := #[]
  let real := th.realize d
  for (k, _) in real.entries do
    out := out.push (.palette, k.key)
  if real.coveredFraction.isSome then
    out := out.push (.palette, "covered")
  for (k, _) in th.tokens.entries do
    out := out.push (.tokens, k)
  for (element, _) in th.styles.entries do
    out := out.push (.style, element)
  if th.chrome.footerLeft.isSome then
    out := out.push (.chrome, "footer.left")
  if th.chrome.footerRight.isSome then
    out := out.push (.chrome, "footer.right")
  return out

/-- The `(declaration, key)` pairs `apply` would overwrite with a
*different* value, computed against the same state `apply` consumes: the
positional last-writer rule says the theme wins them, and W0348's site
says so out loud when the loser was the document's own declaration. A key
the theme re-declares at the standing value replaces nothing and is not
listed. Install order: palette entries, `covered`, tokens, styles,
chrome. -/
public def replaces (th : Theme) (s : Decls) : Array (DeclSurface × String) := Id.run do
  let mut out : Array (DeclSurface × String) := #[]
  let real := th.realize s.palette.classColors.depth
  for (k, c) in real.entries do
    if let some c0 := s.palette.lookup k then
      if c0 != c then
        out := out.push (.palette, k.key)
  if let some n := real.coveredFraction then
    if let some m := s.palette.coveredFraction then
      if n != m then
        out := out.push (.palette, "covered")
  for (k, g) in th.tokens.entries do
    if let some g0 := s.tokens.find? k then
      if g0 != g then
        out := out.push (.tokens, k)
  for (element, st) in th.styles.entries do
    if let some cur := s.styles.find? element then
      if styleMerge st cur != cur then
        out := out.push (.style, element)
  if let some d := th.chrome.footerLeft then
    if let some d0 := s.chrome.footerLeft then
      if d0 != d then
        out := out.push (.chrome, "footer.left")
  if let some d := th.chrome.footerRight then
    if let some d0 := s.chrome.footerRight then
      if d0 != d then
        out := out.push (.chrome, "footer.right")
  return out

/-! ## The layering contract over the install

T1 (`Palette.declare_last_wins`, `Palette.declare_keeps_others` and the
`Tokens` twins beside them in `Ir`) states the per-key contract of one
declaration. The statements below are its bundle-side companions, in the
same terms, over the install the engine runs (`apply`):

* T2, the keeps side — a bundle changes only the keys it declares:
  `apply_palette_keeps_others` and its per-surface siblings. The positional
  reading (a bundle *wins* the keys it does declare, wherever it stands) is
  the beamer lineage's `\usetheme` semantics — a `\setbeamercolor` before
  `\usetheme` loses the same way — and per entry it is exactly
  `Palette.declare_last_wins`.
* Idempotence — applying a theme twice is applying it once:
  `apply_fixed_point`. A bundle declares a state, it does not perform an
  action, so `apply th s` is a fixed point of `apply th`.
-/

/-- No key declared twice. Every shipped bundle satisfies it
(`builtin_styles_nodup`), and it is what pins the style fold's read-back
to the pre-install state in `apply_fixed_point`. -/
public def nodupKeys {α : Type} : List (String × α) → Bool
  | [] => true
  | e :: es => !(es.any (·.1 == e.1)) && nodupKeys es

private theorem orElse_absorb {α : Type} (a b : Option α) :
    (a <|> (a <|> b)) = (a <|> b) := by
  cases a <;> rfl

private theorem or_absorb {α : Type} (a b : Option α) : a.or (a.or b) = a.or b := by
  cases a <;> rfl

private theorem styleMerge_absorb (a b : ElementStyle) :
    styleMerge a (styleMerge a b) = styleMerge a b := by
  simp [styleMerge, or_absorb]
  intro h h'
  exact absurd h' h

/-- The keyed store, as every declare door writes it: filter the key out,
push the entry. `Palette.declare`, `Tokens.declare`, and `Styles.declare`
all reduce to iterating this step, so the fold lemmas below serve all
three surfaces. -/
private def installEntries {κ α : Type} [BEq κ] [LawfulBEq κ] (xs : Array (κ × α)) :
    List (κ × α) → Array (κ × α)
  | [] => xs
  | (k, v) :: es => installEntries ((xs.filter (·.1 != k)).push (k, v)) es

private theorem installEntries_keeps {κ α : Type} [BEq κ] [LawfulBEq κ] (es : List (κ × α))
    (xs : Array (κ × α)) (k : κ) (h : ∀ e ∈ es, e.1 ≠ k) :
    (installEntries xs es).find? (·.1 == k) = xs.find? (·.1 == k) := by
  induction es generalizing xs with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k0, v0⟩ := e
    have hk : k0 ≠ k := h (k0, v0) (List.mem_cons_self ..)
    simp only [installEntries]
    rw [ih _ (fun e' he' => h e' (List.mem_cons_of_mem _ he')),
      declare_keeps _ _ _ _ (fun hh => hk hh.symm)]

private theorem installEntries_residue {κ α : Type} [BEq κ] [LawfulBEq κ] (es : List (κ × α))
    (xs : Array (κ × α)) :
    installEntries xs es =
      xs.filter (fun x => !(es.any (fun e => x.1 == e.1))) ++ installEntries #[] es := by
  induction es generalizing xs with
  | nil =>
    simp only [installEntries, List.any_nil, Bool.not_false]
    rw [Array.filter_eq_self.mpr (fun a _ => rfl)]
    simp
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    simp only [installEntries]
    rw [ih ((xs.filter (·.1 != k)).push (k, v)),
      ih (((#[] : Array (κ × α)).filter (·.1 != k)).push (k, v))]
    rw [Array.filter_push, Array.filter_push, Array.filter_filter]
    have hpred : (fun x : κ × α => (!(es.any fun e => x.1 == e.1)) && (x.1 != k))
        = (fun x : κ × α => !(((k, v) :: es).any fun e => x.1 == e.1)) := by
      funext x
      simp only [List.any_cons, Bool.not_or]
      rw [Bool.and_comm]
      rfl
    rw [hpred]
    have hempty : ((#[] : Array (κ × α)).filter (·.1 != k)) = #[] := rfl
    rw [hempty]
    cases _hP : (!(es.any fun e => ((k, v) : κ × α).1 == e.1)) with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [show (Array.filter (fun x => !es.any fun e => x.fst == e.fst)
        (#[] : Array (κ × α))) = #[] from rfl]
      simp
    | true =>
      simp only [ite_true]
      rw [show (Array.filter (fun x => !es.any fun e => x.fst == e.fst)
        (#[] : Array (κ × α))) = #[] from rfl]
      rw [Array.push_eq_append, Array.push_eq_append]
      simp

private theorem installEntries_mem {κ α : Type} [BEq κ] [LawfulBEq κ] (es : List (κ × α))
    (xs : Array (κ × α)) (x : κ × α) (hx : x ∈ installEntries xs es) :
    x ∈ xs ∨ (es.any (fun e => x.1 == e.1)) = true := by
  induction es generalizing xs with
  | nil => exact .inl hx
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    simp only [installEntries] at hx
    rcases ih _ hx with hmem | hany
    · rcases Array.mem_push.mp hmem with hf | heq
      · exact .inl (Array.mem_filter.mp hf).1
      · right
        simp [heq, List.any_cons]
    · right
      simp [List.any_cons, hany]

private theorem installEntries_idem {κ α : Type} [BEq κ] [LawfulBEq κ] (es : List (κ × α))
    (xs : Array (κ × α)) :
    installEntries (installEntries xs es) es = installEntries xs es := by
  have hself : ((installEntries (#[] : Array (κ × α)) es).filter
      (fun x => !(es.any (fun e => x.1 == e.1)))) = #[] := by
    rw [Array.filter_eq_empty_iff]
    intro x hx
    rcases installEntries_mem es #[] x hx with hmem | hany
    · simp at hmem
    · simp [hany]
  rw [installEntries_residue es (installEntries xs es), installEntries_residue es xs]
  rw [Array.filter_append (by simp), Array.filter_filter]
  have hidem : (fun x : κ × α => (!(es.any fun e => x.1 == e.1)) &&
      !(es.any fun e => x.1 == e.1)) = (fun x : κ × α => !(es.any fun e => x.1 == e.1)) := by
    funext x
    exact Bool.and_self _
  rw [hidem, hself]
  simp

private theorem find?_none_keys {κ α : Type} [BEq κ] [LawfulBEq κ] (xs : Array (κ × α)) (k : κ)
    (h : xs.find? (·.1 == k) = none) : ∀ e ∈ xs.toList, e.1 ≠ k := by
  intro e he hk
  rw [Array.find?_eq_none] at h
  have := h e (by simpa using he)
  simp [hk] at this

private theorem installPalette_entries (p : Palette) (es : List (ColorRef × Color)) :
    (installPalette p es).entries = installEntries p.entries es := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, c⟩ := e
    simp only [installPalette, installEntries]
    rw [ih]
    rfl

private theorem installPalette_covered (p : Palette) (es : List (ColorRef × Color)) :
    (installPalette p es).coveredFraction = p.coveredFraction := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, c⟩ := e
    simp only [installPalette]
    rw [ih]
    rfl

private theorem installPalette_seeded (p : Palette) (es : List (ColorRef × Color)) :
    (installPalette p es).seeded = p.seeded := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, c⟩ := e
    simp only [installPalette]
    rw [ih]
    rfl

private theorem installPalette_classColors (p : Palette) (es : List (ColorRef × Color)) :
    (installPalette p es).classColors = p.classColors := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, c⟩ := e
    simp only [installPalette]
    rw [ih]
    rfl

private theorem installPalette_decorative (p : Palette) (es : List (ColorRef × Color)) :
    (installPalette p es).decorative =
      p.decorative.filter (fun x => !(es.any (fun e => x == e.1))) := by
  induction es generalizing p with
  | nil =>
    simp only [installPalette, List.any_nil, Bool.not_false]
    exact (Array.filter_eq_self.mpr (fun a _ => rfl)).symm
  | cons e es ih =>
    obtain ⟨k, c⟩ := e
    simp only [installPalette]
    rw [ih]
    show (p.decorative.filter (· != k)).filter _ = _
    rw [Array.filter_filter]
    congr 1
    funext x
    simp only [List.any_cons, Bool.not_or]
    rw [Bool.and_comm]
    rfl

private theorem installTokens_entries (t : Tokens) (es : List (String × Dim.SymGlue)) :
    (installTokens t es).entries = installEntries t.entries es := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, g⟩ := e
    simp only [installTokens, installEntries]
    rw [ih]
    rfl

/-- The style fold's writes, read against one base: nodup keys are what
make the running fold's reads equal these (each key is written once, so no
read sees an earlier write). -/
private def styleWrites (s : Styles) :
    List (String × ElementStyle) → List (String × ElementStyle)
  | [] => []
  | (k, st) :: es => (k, styleMerge st ((s.find? k).getD {})) :: styleWrites s es

private theorem styles_declare_find_ne (s : Styles) (k k' : String) (st : ElementStyle)
    (h : k' ≠ k) : (s.declare k st).find? k' = s.find? k' := by
  show (((s.entries.filter (·.1 != k)).push (k, st)).find? (·.1 == k')).map (·.2)
      = (s.entries.find? (·.1 == k')).map (·.2)
  rw [declare_keeps _ _ _ _ h]

private theorem styleWrites_congr (s₁ s₂ : Styles) (es : List (String × ElementStyle))
    (h : ∀ e ∈ es, styleMerge e.2 ((s₁.find? e.1).getD {})
      = styleMerge e.2 ((s₂.find? e.1).getD {})) :
    styleWrites s₁ es = styleWrites s₂ es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, st⟩ := e
    simp only [styleWrites]
    rw [h (k, st) (List.mem_cons_self ..), ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]

private theorem nodup_head {α : Type} (k : String) (v : α) (es : List (String × α))
    (h : nodupKeys ((k, v) :: es) = true) :
    (∀ e ∈ es, e.1 ≠ k) ∧ nodupKeys es = true := by
  simp only [nodupKeys, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun e he hk => ?_, h.2⟩
  have hall := List.any_eq_false.mp h.1 e he
  simp [hk] at hall

private theorem installStyles_entries (s : Styles) (es : List (String × ElementStyle))
    (h : nodupKeys es = true) :
    (installStyles s es).entries = installEntries s.entries (styleWrites s es) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, st⟩ := e
    obtain ⟨hne, hnd⟩ := nodup_head k st es h
    simp only [installStyles, styleWrites, installEntries]
    rw [ih _ hnd]
    have hw : styleWrites (s.declare k (styleMerge st ((s.find? k).getD {}))) es
        = styleWrites s es := by
      apply styleWrites_congr
      intro e' he'
      rw [styles_declare_find_ne _ _ _ _ (hne e' he')]
    rw [hw]
    rfl

private theorem installStyles_keeps (s : Styles) (es : List (String × ElementStyle))
    (k : String) (h : ∀ e ∈ es, e.1 ≠ k) :
    (installStyles s es).find? k = s.find? k := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k0, st0⟩ := e
    simp only [installStyles]
    rw [ih _ (fun e' he' => h e' (List.mem_cons_of_mem _ he')),
      styles_declare_find_ne _ _ _ _ (fun hh => (h (k0, st0) (List.mem_cons_self ..)) hh.symm)]

private theorem installStyles_find_mem (s : Styles) (es : List (String × ElementStyle))
    (h : nodupKeys es = true) (k : String) (st : ElementStyle) (hmem : (k, st) ∈ es) :
    (installStyles s es).find? k = some (styleMerge st ((s.find? k).getD {})) := by
  induction es generalizing s with
  | nil => cases hmem
  | cons e es ih =>
    obtain ⟨k0, st0⟩ := e
    obtain ⟨hne, hnd⟩ := nodup_head k0 st0 es h
    cases hmem with
    | head =>
      simp only [installStyles]
      rw [installStyles_keeps _ _ _ hne]
      show ((((s.entries.filter (·.1 != k)).push
          (k, styleMerge st ((s.find? k).getD {}))).find? (·.1 == k)).map (·.2)) = _
      rw [declare_find_eq]
      rfl
    | tail _ hmem' =>
      have hkne : k ≠ k0 := by
        intro hk
        exact (hne (k, st) hmem') (by rw [hk])
      simp only [installStyles]
      rw [ih _ hnd hmem', styles_declare_find_ne _ _ _ _ hkne]

private theorem styles_ext {a b : Styles} (h : a.entries = b.entries) : a = b := by
  cases a
  cases b
  simpa using h

private theorem tokens_ext {a b : Tokens} (h : a.entries = b.entries) : a = b := by
  cases a
  cases b
  simpa using h

private theorem palette_ext {a b : Palette} (he : a.entries = b.entries)
    (hc : a.coveredFraction = b.coveredFraction) (hd : a.decorative = b.decorative)
    (hs : a.seeded = b.seeded) (hk : a.classColors = b.classColors) :
    a = b := by
  cases a
  cases b
  simp_all

private theorem installStyles_idem (s : Styles) (es : List (String × ElementStyle))
    (h : nodupKeys es = true) :
    installStyles (installStyles s es) es = installStyles s es := by
  apply styles_ext
  have hw : styleWrites (installStyles s es) es = styleWrites s es := by
    apply styleWrites_congr
    intro e he
    obtain ⟨k, st⟩ := e
    rw [installStyles_find_mem s es h k st he]
    show styleMerge st (styleMerge st ((s.find? k).getD {})) = _
    rw [styleMerge_absorb]
  rw [installStyles_entries _ _ h, hw, installStyles_entries s es h, installEntries_idem]

private theorem installTokens_idem (t : Tokens) (es : List (String × Dim.SymGlue)) :
    installTokens (installTokens t es) es = installTokens t es := by
  apply tokens_ext
  rw [installTokens_entries, installTokens_entries]
  exact installEntries_idem ..

private theorem paletteApply_entries (bp : Palette) : ∀ q : Palette,
    (paletteApply bp q).entries = installEntries q.entries bp.entries.toList := by
  intro q
  show (installPalette q bp.entries.toList).entries = _
  exact installPalette_entries ..

private theorem paletteApply_covered (bp : Palette) : ∀ q : Palette,
    (paletteApply bp q).coveredFraction
      = (bp.coveredFraction <|> q.coveredFraction) := by
  intro q
  show (bp.coveredFraction <|>
      (installPalette q bp.entries.toList).coveredFraction) = _
  rw [installPalette_covered]

private theorem paletteApply_decorative (bp : Palette) : ∀ q : Palette,
    (paletteApply bp q).decorative
      = q.decorative.filter
          (fun x => !(bp.entries.toList.any (fun e => x == e.1))) := by
  intro q
  show (installPalette q bp.entries.toList).decorative = _
  exact installPalette_decorative ..

private theorem paletteApply_idem (bp p : Palette) :
    paletteApply bp (paletteApply bp p) = paletteApply bp p := by
  apply palette_ext
  · simp only [paletteApply_entries]
    exact installEntries_idem ..
  · simp only [paletteApply_covered]
    exact orElse_absorb ..
  · simp only [paletteApply_decorative]
    rw [Array.filter_filter]
    congr 1
    funext x
    exact Bool.and_self _
  · show (bp.seeded <|> (installPalette (paletteApply bp p) bp.entries.toList).seeded) =
      (bp.seeded <|> (installPalette p bp.entries.toList).seeded)
    rw [installPalette_seeded]
    show (bp.seeded <|> (bp.seeded <|> (installPalette p bp.entries.toList).seeded)) = _
    exact orElse_absorb ..
  · show (installPalette (paletteApply bp p) bp.entries.toList).classColors =
      (installPalette p bp.entries.toList).classColors
    rw [installPalette_classColors, installPalette_classColors]
    show (installPalette p bp.entries.toList).classColors = _
    rw [installPalette_classColors]

private theorem chromeApply_idem (bc c : Chrome) :
    chromeApply bc (chromeApply bc c) = chromeApply bc c := by
  simp only [chromeApply]
  rw [orElse_absorb, orElse_absorb, orElse_absorb]

private theorem bangParts_plain (cur : List Char) (l : List Char) (h : '!' ∉ l) :
    bangParts cur l = [bangParts.trimmed (l.reverse ++ cur)] := by
  induction l generalizing cur with
  | nil => simp [bangParts]
  | cons c rest ih =>
    have hc : c ≠ '!' := fun e => h (e ▸ List.mem_cons_self ..)
    have hr : '!' ∉ rest := fun m => h (List.mem_cons_of_mem _ m)
    simp only [bangParts, beq_iff_eq, hc, ite_false, ih (c :: cur) hr, List.reverse_cons,
      List.append_assoc, List.cons_append, List.nil_append]

private theorem dropWhile_head_keep (p : Char → Bool) (l : List Char)
    (h : l.head?.all (fun c => !p c) = true) : l.dropWhile p = l := by
  cases l with
  | nil => rfl
  | cons c rest =>
    simp only [List.head?_cons, Option.all_some, Bool.not_eq_true'] at h
    simp [h]

/-- **A plain name resolves to its entry.** `Palette.resolve` — the
evaluator `\textcolor` and every declaration value go through — reads a
name with no `!` and no blank at either end as exactly what `find?` reads:
the two spellings of one colour use cannot diverge, for any palette. The
side condition is what `resolve` itself splits and trims on. -/
public theorem resolve_find_exact (pal : Palette) (n : String) (c : Color)
    (hn : plainName n = true) (h : pal.find? n = some c) : pal.resolve n = some c := by
  simp only [plainName, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hn
  obtain ⟨⟨hb, hhead⟩, hlast⟩ := hn
  have hparts : bangParts [] n.toList = [n] := by
    rw [bangParts_plain [] n.toList hb, List.append_nil]
    simp only [bangParts.trimmed]
    have h1 : n.toList.reverse.dropWhile asciiBlank = n.toList.reverse := by
      apply dropWhile_head_keep
      rw [List.head?_reverse]
      exact hlast
    rw [h1, List.reverse_reverse, dropWhile_head_keep _ _ hhead, String.ofList_toList]
  unfold Palette.resolve
  rw [hparts]
  simp [Palette.atom, h, Palette.resolve.go]

/-- **A class default never re-exempts a redeclared key.** The exemption a
class-default bundle installs under the document survives exactly for the
keys the document did not declare: a document that redeclares a theme's
decorative entry is judged on its own declaration, as `Palette.declare`
judges every redeclaration. -/
public theorem applyUnder_decorative_exact (th : Theme) (s : Decls) (k : ColorRef) :
    k ∈ (applyUnder th s).palette.decorative ↔
      (k ∈ s.palette.decorative ∨ (k ∈ (th.realize s.palette.classColors.depth).decorative ∧
        s.palette.lookup k = none)) := by
  show k ∈ s.palette.decorative ++ (installPalette (underDocument th
    (th.realize s.palette.classColors.depth) s.palette) s.palette.entries.toList).decorative ↔ _
  rw [Array.mem_append, installPalette_decorative, underDocument_decorative, Array.mem_filter]
  have hnone : (!(s.palette.entries.toList.any fun e => k == e.1)) = true ↔
      s.palette.lookup k = none := by
    simp only [Palette.lookup, Option.map_eq_none_iff, Array.find?_eq_none, Bool.not_eq_true',
      List.any_eq_false, Array.mem_toList_iff, beq_iff_eq]
    constructor
    · intro hall x hx hxk
      exact hall x hx (by simpa using hxk.symm)
    · intro hall x hx hkx
      exact hall x hx (by simpa using hkx.symm)
  rw [hnone]

/-- T2, the palette half, in `Palette.declare_keeps_others`'s terms: a
bundle changes only the keys it declares — a key the theme does not name
resolves after `\theme` exactly as before it. -/
public theorem apply_palette_keeps_others (th : Theme) (s : Decls) (k : ColorRef)
    (h : (th.realize s.palette.classColors.depth).lookup k = none) :
    (apply th s).palette.lookup k = s.palette.lookup k := by
  have hall : ∀ e ∈ (th.realize s.palette.classColors.depth).entries.toList, e.1 ≠ k := by
    apply find?_none_keys
    simp only [Palette.lookup, Option.map_eq_none_iff] at h
    exact h
  show ((installPalette s.palette (th.realize s.palette.classColors.depth).entries.toList).entries.find?
      (·.1 == k)).map (·.2) = _
  rw [installPalette_entries, installEntries_keeps _ _ _ hall]
  rfl

/-- The covered fraction is part of the same contract: a bundle that
declares no `covered` leaves the document's standing. -/
public theorem apply_keeps_covered (th : Theme) (s : Decls)
    (h : th.palette.coveredFraction = none) :
    (apply th s).palette.coveredFraction = s.palette.coveredFraction := by
  show (th.palette.coveredFraction <|>
      (installPalette s.palette
        (th.realize s.palette.classColors.depth).entries.toList).coveredFraction) = _
  rw [h, installPalette_covered]
  rfl

/-- The decorative exemption is per key and rides with declarations
(`declare_decorative_rides`); a bundle that does not declare a key never
touches its exemption. -/
public theorem apply_palette_keeps_decorative (th : Theme) (s : Decls) (k : ColorRef)
    (h : (th.realize s.palette.classColors.depth).lookup k = none) :
    (k ∈ (apply th s).palette.decorative) ↔ k ∈ s.palette.decorative := by
  have hall : ∀ e ∈ (th.realize s.palette.classColors.depth).entries.toList, e.1 ≠ k := by
    apply find?_none_keys
    simp only [Palette.lookup, Option.map_eq_none_iff] at h
    exact h
  show k ∈ (installPalette s.palette
    (th.realize s.palette.classColors.depth).entries.toList).decorative ↔ _
  rw [installPalette_decorative]
  constructor
  · intro hm
    exact (Array.mem_filter.mp hm).1
  · intro hm
    refine Array.mem_filter.mpr ⟨hm, ?_⟩
    simp only [Bool.not_eq_true']
    rw [List.any_eq_false]
    intro e he
    simpa using fun hk => (hall e he) hk.symm

/-- T2, the tokens half: `Tokens.declare_keeps_others` lifted over the
bundle fold. -/
public theorem apply_tokens_keeps_others (th : Theme) (s : Decls) (k : String)
    (h : th.tokens.find? k = none) :
    (apply th s).tokens.find? k = s.tokens.find? k := by
  have hall : ∀ e ∈ th.tokens.entries.toList, e.1 ≠ k := by
    apply find?_none_keys
    simp only [Tokens.find?, Option.map_eq_none_iff] at h
    exact h
  show ((installTokens s.tokens th.tokens.entries.toList).entries.find?
      (·.1 == k)).map (·.2) = _
  rw [installTokens_entries, installEntries_keeps _ _ _ hall]
  rfl

/-- T2, the styles half: an element the bundle does not style keeps the
document's whole entry. -/
public theorem apply_styles_keeps_others (th : Theme) (s : Decls) (element : String)
    (h : th.styles.find? element = none) :
    (apply th s).styles.find? element = s.styles.find? element := by
  have hall : ∀ e ∈ th.styles.entries.toList, e.1 ≠ element := by
    apply find?_none_keys
    simp only [Styles.find?, Option.map_eq_none_iff] at h
    exact h
  exact installStyles_keeps _ _ _ hall

/-- T2, the chrome half: a slot the bundle leaves silent keeps the
document's datum — the statement whose absence let the install replace the
band wholesale. -/
public theorem apply_chrome_keeps_left (th : Theme) (s : Decls)
    (h : th.chrome.footerLeft = none) :
    (apply th s).chrome.footerLeft = s.chrome.footerLeft := by
  show (th.chrome.footerLeft <|> s.chrome.footerLeft) = _
  rw [h]
  rfl

public theorem apply_chrome_keeps_right (th : Theme) (s : Decls)
    (h : th.chrome.footerRight = none) :
    (apply th s).chrome.footerRight = s.chrome.footerRight := by
  show (th.chrome.footerRight <|> s.chrome.footerRight) = _
  rw [h]
  rfl

/-- Idempotence: applying a theme twice is applying it once — `apply th s`
is a fixed point of `apply th`. A bundle declares a state rather than
performing an action, so a repeated `\theme{name}` cannot drift the
document. The one hypothesis — the bundle declares each style element
once — holds for every shipped bundle (`builtin_styles_nodup`) and is what
pins the style fold's read-back to the pre-install state. -/
public theorem apply_fixed_point (th : Theme) (s : Decls)
    (h : nodupKeys th.styles.entries.toList = true) :
    apply th (apply th s) = apply th s := by
  have hk : (paletteApply (th.realize s.palette.classColors.depth) s.palette).classColors =
      s.palette.classColors := installPalette_classColors ..
  simp only [apply]
  rw [hk, paletteApply_idem, installTokens_idem, installStyles_idem _ _ h, chromeApply_idem]

end LeanTex.Core.Theme
