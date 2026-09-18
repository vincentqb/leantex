import LeanTex.Core.Ir

namespace LeanTex.Core.Theme

open LeanTex.Core.Ir LeanTex.Core.Dim

/-- A theme is data: palette, tokens, element styles, and chrome as the
*values* the engine runs on, installed at the `\theme` site through the same
replace-on-redeclare path a document's own declarations use. A document's
later declarations override, so a theme is a default, never a lock — and a
new theme is a new table here, values only, no code. Values rather than
surface strings so a theorem about a bundle ranges over what `\theme`
installs (`Contrast.moloch_contract` closes by `decide` over these entries);
colour arithmetic a bundle wants (xcolor's `!` mixes) is evaluated right
here, at definition time, with the same `Color.mix` step
`Ir.Palette.resolve` folds at document use sites. The semantic palette keys
are the whole contract with the backends: `fg`/`bg` colour text and page,
declaring `frametitlebg` turns the frame title into a colour bar,
`progressfg`/`bg` draw the section-page progress bar (`progressheight`
sizes it), `standoutfg`/`bg` invert a `[standout]` frame, and `muted`
quiets secondary furniture — the chrome footer draws in it. -/
structure Theme where
  name : String
  palette : Palette
  tokens : Tokens
  styles : Styles
  /-- The slide footer's slots, declared data (`\chrome`), not colour: no
  theorem ranges over it. -/
  chrome : Chrome := {}

/-- `{\large\bfseries}` (`{\Large\bfseries}` for `large := "Large"`) as the
elaborator reads a `\style` font value: nested wrappers with an empty body
where the element's own content goes. -/
private def boldFont (size : String) : ElementStyle :=
  { font := some #[.styled (.size size) #[.styled .bold #[]]] }

private def pt1 : Dim.SymGlue := { width := Length.ofSp (Dim.pt 1) }

/-- The Metropolis lineage as a token bundle: an inverted frame-title bar,
one warm accent, a near-white page. Values map the moloch beamer theme's
light preset onto the semantic keys, mixes evaluated (the original xcolor
spelling rides in the comment beside each). -/
def moloch : Theme :=
  let fg : Color := { r := 0x23, g := 0x37, b := 0x3B }
  let bg := Color.black.mix 2 Color.white                     -- black!2
  -- moloch's own alert is #EB811B, which reads at 2.61:1 on this page —
  -- under the 4.5:1 WCAG 2.2 SC 1.4.3 asks of text. The same orange at
  -- 70% over black clears it at 4.94:1, so the lineage keeps its hue and
  -- the bundle keeps the engine's contract (Core/Contrast.lean).
  let alert : Color := { r := 0xA5, g := 0x5A, b := 0x13 }
  let progressfg := alert
  let progressbg := (progressfg.mix 50 .black).mix 30 .white  -- progressfg!50!black!30
  { name := "moloch"
    palette := {
      entries := #[
        ("fg", fg), ("bg", bg), ("alert", alert), ("example", { r := 0x00, g := 0x80, b := 0x80 }),
        -- The muted step: the theme's own ink mixed 70:30 into its page, the
        -- strongest quieting that still clears the 4.5:1 WCAG 2.2 SC 1.4.3
        -- asks of the small footer text (4.79:1 here; moloch_contract is the
        -- kernel check, and 60:40 already fails at 3.65:1).
        ("muted", fg.mix 70 bg),                              -- fg!70!bg
        ("frametitlefg", bg), ("frametitlebg", fg),
        ("progressfg", progressfg), ("progressbg", progressbg),
        ("separator", progressfg),
        ("standoutfg", bg), ("standoutbg", fg)]
      -- Covered overlay content keeps each colour at 31% of itself over
      -- the page, mixed in Oklab (Core/Oklab.lean). Material's
      -- disabled-state opacity is 38% (m2.material.io/design/interaction/
      -- states.html#disabled), but at 38% this bundle's alert and example
      -- read at 2.89:1 and 2.75:1 against their active forms — under the
      -- 3:1 WCAG 2.2 SC 1.4.11 asks of state-identifying information; 31%
      -- is the largest fraction where every text role clears it
      -- (Contrast.moloch_covered is the kernel check).
      coveredFraction := some 31 }
    -- The title page's inter-part spacing, from the moloch source
    -- (beamerinnerthememoloch.dtx): 0.3em above the subtitle, 0.8em below
    -- the separator (its default linewidth is 0.5pt), 0.5em below the
    -- author, 1em below the institute.
    tokens := { entries := #[
      ("progressheight", pt1),
      ("separatorheight", { width := Length.ofSp (Dim.pt 1 / 2) }),  -- 0.5pt
      ("subtitlegap", { width := { em := 300 } }),                   -- 0.3em
      ("separatorgap", { width := { em := 800 } }),                  -- 0.8em
      ("authorgap", { width := { em := 500 } }),                     -- 0.5em
      ("institutegap", { width := { em := 1000 } })] }               -- 1em
    styles := { entries := #[
      ("frametitle", boldFont "large"),
      ("sectionpage", boldFont "Large"),
      ("standout", boldFont "Large"),
      -- moloch's `title page` template sets the title matter ragged left
      -- and draws a separator rule between the title block and the author
      -- block, in the palette's separator colour (resolved here, exactly
      -- what `separator = separator` resolved to at install time).
      ("titlepage", { align := some "left"
                      separator := some (progressfg, some "separator") })] }
    -- The footline of the lineage read as data: metropolis puts the frame
    -- number in the footline and a `frame footer` template beside it; here
    -- the section title keeps the reader placed and the frame number says
    -- how far along (beamerouterthememoloch.dtx, footline template).
    chrome := { footerLeft := some .sectionTitle
                footerRight := some .frameNumber } }

/-- A quieter default: near-black ink on white, one restrained accent, no
title bar — frame titles set as plain bold headings because the bar key is
simply absent. A third theme costs exactly one more table like this. -/
def plain : Theme :=
  let fg : Color := { r := 0x1B, g := 0x1B, b := 0x1F }
  let bg : Color := { r := 0xFF, g := 0xFF, b := 0xFF }
  { name := "plain"
    palette := {
      entries := #[
        ("fg", fg), ("bg", bg), ("alert", { r := 0xB3, g := 0x26, b := 0x1E }),
        ("example", { r := 0x20, g := 0x5E, b := 0x3B }),
        -- Same muted rule as moloch: ink 70:30 into the page (6.36:1 here).
        ("muted", fg.mix 70 bg),                              -- fg!70!bg
        ("progressfg", fg.mix 60 .white),                     -- fg!60
        ("progressbg", fg.mix 15 .white),                     -- fg!15
        ("separator", fg.mix 40 .white),                      -- fg!40
        ("standoutfg", bg), ("standoutbg", fg)]
      -- Covered keeps each colour at 38% of itself over the page — the
      -- Material disabled-state opacity, per colour in Oklab; this
      -- bundle's roles all clear the 3:1 state change at 38%
      -- (Contrast.plain_covered is the kernel check).
      coveredFraction := some 38 }
    tokens := { entries := #[("progressheight", pt1)] }
    styles := { entries := #[
      ("sectionpage", boldFont "Large"),
      ("standout", boldFont "Large")] }
    chrome := { footerLeft := some .sectionTitle
                footerRight := some .frameNumber } }

def builtin : List Theme := [moloch, plain]

/-- Arch-design I2, the value half: every shipped bundle that styles the
title page declares its alignment and its separator — moloch's title
matter is ragged left with a rule by declaration
(beamerinnerthememoloch.dtx's `title page` template is `\raggedright`
with a separator rule), never by a backend constant. The stronger
reading — that the declaration survives `\theme` through the elaborator —
is the staged `titlepage_align_declared_engine`. -/
theorem titlepage_align_declared :
    ∀ t ∈ builtin,
      ((t.styles.find? "titlepage").all fun st =>
        st.align.isSome && st.separator.isSome) = true := by decide

def find? (name : String) : Option Theme :=
  builtin.find? (·.name == name)

def names : List String := builtin.map (·.name)

end LeanTex.Core.Theme
