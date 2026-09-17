import LeanTex.Core.Ir

namespace LeanTex.Core.Theme

/-- A theme is data: declaration bodies in the surface language, applied at
the `\theme` site exactly as if the document had written them. A document's
own later declarations override (palette and tokens replace on redeclare),
so a theme is a default, never a lock — and a new theme is a new table
here, values only, no code. The semantic palette keys are the whole
contract with the backends: `fg`/`bg` colour text and page, declaring
`frametitlebg` turns the frame title into a colour bar, `progressfg`/`bg`
draw the section-page progress bar (`progressheight` sizes it),
`standoutfg`/`bg` invert a `[standout]` frame, and `muted` quiets
secondary furniture — the chrome footer draws in it. -/
structure Theme where
  name : String
  /-- `\palette{...}` body. -/
  palette : String
  /-- `\tokens{...}` body. -/
  tokens : String
  /-- `\style{element}{...}` bodies, element first. -/
  styles : List (String × String)
  /-- `\chrome{...}` body: the slide footer's slots. -/
  chrome : String := ""

/-- The Metropolis lineage as a token bundle: an inverted frame-title bar,
one warm accent, a near-white page. Values map the moloch beamer theme's
light preset onto the semantic keys, mixes included. -/
def moloch : Theme := {
  name := "moloch"
  palette :=
    -- moloch's own alert is #EB811B, which reads at 2.61:1 on this page --
    -- under the 4.5:1 WCAG 2.2 SC 1.4.3 asks of text. The same orange at
    -- 70% over black clears it at 4.94:1, so the lineage keeps its hue and
    -- the bundle keeps the engine's contract (Core/Contrast.lean).
    "fg = #23373B, bg = black!2, alert = #A55A13, example = #008080, " ++
    -- The muted step: the theme's own ink mixed 70:30 into its page, the
    -- strongest quieting that still clears the 4.5:1 WCAG 2.2 SC 1.4.3
    -- asks of the small footer text (4.79:1 here; moloch_contract is the
    -- kernel check, and 60:40 already fails at 3.65:1).
    "muted = fg!70!bg, " ++
    "frametitlefg = bg, frametitlebg = fg, progressfg = alert, " ++
    "progressbg = progressfg!50!black!30, separator = progressfg, " ++
    "standoutfg = bg, standoutbg = fg, " ++
    -- Covered overlay content shows at 38% of the body ink over the page --
    -- the Material Design disabled-state opacity (m2.material.io/design/
    -- interaction/states.html#disabled); WCAG 2.2 SC 1.4.3 exempts text in
    -- an inactive state, and Contrast.coveredContract holds the value to
    -- "quieter than body, still distinguishable" for every bundle.
    "covered = fg!38!bg"
  tokens := "progressheight = 1pt"
  styles := [("frametitle", "font = {\\large\\bfseries}"),
             ("sectionpage", "font = {\\Large\\bfseries}"),
             ("standout", "font = {\\Large\\bfseries}")]
  -- The footline of the lineage read as data: metropolis puts the frame
  -- number in the footline and a `frame footer` template beside it; here
  -- the section title keeps the reader placed and the frame number says
  -- how far along (beamerouterthememoloch.dtx, footline template).
  chrome := "footer = { left = \\sectiontitle, right = \\framenumber }"
}

/-- A quieter default: near-black ink on white, one restrained accent, no
title bar — frame titles set as plain bold headings because the bar key is
simply absent. A third theme costs exactly one more table like this. -/
def plain : Theme := {
  name := "plain"
  palette :=
    "fg = #1B1B1F, bg = #FFFFFF, alert = #B3261E, example = #205E3B, " ++
    -- Same muted rule as moloch: ink 70:30 into the page (6.36:1 here).
    "muted = fg!70!bg, " ++
    "progressfg = fg!60, progressbg = fg!15, separator = fg!40, " ++
    "standoutfg = bg, standoutbg = fg, " ++
    -- The same 38% disabled-state convention as moloch's covered.
    "covered = fg!38!bg"
  tokens := "progressheight = 1pt"
  styles := [("sectionpage", "font = {\\Large\\bfseries}"),
             ("standout", "font = {\\Large\\bfseries}")]
  chrome := "footer = { left = \\sectiontitle, right = \\framenumber }"
}

def builtin : List Theme := [moloch, plain]

def find? (name : String) : Option Theme :=
  builtin.find? (·.name == name)

def names : List String := builtin.map (·.name)

end LeanTex.Core.Theme
