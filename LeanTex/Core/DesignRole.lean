module

public import LeanTex.Core.Color
public import LeanTex.Core.CodeRoles

/-!
The colour roles every artifact paints, as one typed registry. A role is a
name with a row of data: the `\palette` key that declares it, its CSS
identifier, the contrast need it is judged by and the role it stands on, its
default in each scheme, the beamer elements that write it, and its export
name. Every consumer reads a role through this table and the one resolver
over it (`Design.at`), so a default chain is data, never a site's code.

Two tiers, as beamer's own colour elements and the reference → system →
component layering of Material 3 and the W3C Design Tokens format
(https://www.designtokens.org/tr/drafts/format/, aliases): palette roles
(the page, the ink, the content colours) and element roles (the frame-title
bar and its ink, a block's title and body, the standout pair), whose
defaults refer to palette roles.
-/

namespace LeanTex.Core.Ir

/-- What a role's ink owes the ground it stands on, by the WCAG 2.2 success
criterion that judges it: text (SC 1.4.3), large-scale text (SC 1.4.3),
non-text information (SC 1.4.11), a state change (SC 1.4.11), or nothing — a
ground, or pure decoration, which both criteria exempt. -/
public inductive Need where
  | text | largeText | nonText | state | decorative
  deriving Repr, DecidableEq, Inhabited

/-- A need the contrast judge holds a pair to on a ground: text, large-scale
text, non-text information. A state change is judged against its active
form (the cover contract), and a ground or decoration owes nothing. -/
@[expose] public def Need.paired : Need → Bool
  | .text | .largeText | .nonText => true
  | .state | .decorative => false

/-- A need as its medium shows it. A deck's stage is shown at the size of the
screen it is projected on, where its text stands past WCAG 2.2's large-scale
sizes, so a slide's text is judged as large-scale text; nothing else moves. -/
@[expose] public def Need.atStage (stage : Bool) : Need → Need
  | .text => if stage then .largeText else .text
  | .largeText => .largeText
  | .nonText => .nonText
  | .state => .state
  | .decorative => .decorative

/-- The titled block's kind, closed: beamer's three block environments
(`{block}`, `{alertblock}`, `{exampleblock}` — beamer user guide §12.3,
"Highlighting"), and tcolorbox's box, which its lowering sets through the
same surface (`Tcolorbox.lower`). The kind selects the roles the title and
body resolve through (the box the plain block's) and the box the block
stands in: beamer's two colour boxes for the three, tcolorbox's frame for
the box — a poster and a deck set the same node at different base sizes. -/
public inductive TitledKind where
  | block
  | alert
  | example
  | box
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The kind's one spelling: the HTML class suffix, one naming site for both
backends and the dump. -/
@[expose] public def TitledKind.name : TitledKind → String
  | .block => "block"
  | .alert => "alert"
  | .example => "example"
  | .box => "box"

/-- The role-key stem the kind's colours resolve through (`alerttitlefg`):
tcolorbox's box takes the plain block's roles, where its lowering declares
its colours. -/
@[expose] public def TitledKind.roleStem : TitledKind → String
  | .block | .box => "block"
  | .alert => "alert"
  | .example => "example"

/-- The medium a resolution is for: print is the PDF's (LaTeX's black ink on
unpainted paper), light and dark are the screen's two colour schemes. -/
public inductive Scheme where
  | print | light | dark
  deriving Repr, DecidableEq, Inhabited

@[expose] public def Scheme.all : List Scheme := [.print, .light, .dark]

/-- How far a class's tinted grounds stand from its page, as WCAG 2.2 ratios
to it ×1000: a body fill, a title band, a rule, and the least ratio a band
keeps to the body below it (`SeedPalette.Targets`). -/
public structure GroundDepth where
  body : Nat
  band : Nat
  rule : Nat
  pair : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A document's: a body as deep as GitHub's code ground on white (1.06:1),
a band at 1.15:1, rules at Tailwind v4 slate-300's 1.49:1
(https://tailwindcss.com/docs/colors). The band keeps 1.07:1 to the body
below it: what the two targets leave (1.15 / 1.06 = 1.085), less the slack
of the band's quantized answer. -/
@[expose] public def GroundDepth.documents : GroundDepth :=
  { body := 1060, band := 1150, rule := 1490, pair := 1070 }

/-- A deck's and a poster's, read across a room on a projector: Radix slate
steps 3 and 5 on white (1.14:1, 1.31:1; https://www.radix-ui.com/colors),
the same rules. The band keeps 1.10:1 to the body below it, inside what the
two targets leave (1.30 / 1.12 = 1.16). -/
@[expose] public def GroundDepth.decks : GroundDepth :=
  { body := 1120, band := 1300, rule := 1490, pair := 1100 }

/-- What a class asks of the colours nothing declares, beside its ground
depth: LaTeX's standard classes and the résumé print every line in the ink
and leave verbatim unpainted; a deck, a poster and a card keep a quieter
secondary ink and unpainted verbatim; the web's page and a markdown note set
verbatim on a tinted ground, in print as on screen — GitHub's practice. One
row per class, read by both artifacts (`Role.row`'s fallbacks take it). -/
public inductive ClassRow where
  | latex
  | stage
  | web
  deriving Repr, DecidableEq, Inhabited

@[expose] public def ClassRow.all : List ClassRow := [.latex, .stage, .web]

/-- A palette's class defaults: the class's row and the depth its generated
grounds stand at. -/
public structure ClassColors where
  row : ClassRow := .latex
  depth : GroundDepth := .documents
  deriving Repr, DecidableEq, Inhabited

public instance : BEq ClassColors := ⟨fun a b => decide (a = b)⟩

/-- The seeds the engine's own screen colours are generated from where a
document declares none, invented here: an ink, a paper and an accent —
Tailwind v4's zinc-900, white, and blue-700 (https://tailwindcss.com/docs/colors). -/
@[expose] public def ClassColors.ink : Color := { r := 0x18, g := 0x18, b := 0x1B }

@[expose] public def ClassColors.paper : Color := { r := 0xFF, g := 0xFF, b := 0xFF }

@[expose] public def ClassColors.accent : Color := { r := 0x1D, g := 0x4E, b := 0xD8 }

/-- Every colour role. Palette roles first (the page, the ink, the content
and furniture colours), then the element roles that paint one site each. -/
public inductive Role where
  | page | ink | muted | alert | example | covered
  | marker | codeSurface | rule | focus
  | accent | surface | surfaceStrong | accentWash | accentSoft | accentText | accentEdge
  | mutedOnInverse | accentOnInverse | diagramMuted | alertBandInk | exampleBandInk
  | paper | printInk
  | frameTitleBar | frameTitleInk | frameSubtitleInk | sectionTitleInk
  | footBand | footInk
  | blockTitleBar | alertTitleBar | exampleTitleBar
  | blockTitleInk | alertTitleInk | exampleTitleInk
  | blockBodyInk | alertBodyInk | exampleBodyInk
  | blockBodyGround | alertBodyGround | exampleBodyGround
  | standoutGround | standoutInk | titlePageGround | titlePageInk | separator
  | progressFill | progressTrack | sectionProgressFill | sectionProgressTrack
  | codeInk | codeKeyword | codeName | codeLiteral | codeComment | codeError
  deriving Repr, DecidableEq, Inhabited, Hashable

@[expose] public def Role.titleBar : TitledKind → Role
  | .block | .box => .blockTitleBar
  | .alert => .alertTitleBar
  | .example => .exampleTitleBar

@[expose] public def Role.titleInk : TitledKind → Role
  | .block | .box => .blockTitleInk
  | .alert => .alertTitleInk
  | .example => .exampleTitleInk

@[expose] public def Role.bodyInk : TitledKind → Role
  | .block | .box => .blockBodyInk
  | .alert => .alertBodyInk
  | .example => .exampleBodyInk

@[expose] public def Role.bodyGround : TitledKind → Role
  | .block | .box => .blockBodyGround
  | .alert => .alertBodyGround
  | .example => .exampleBodyGround

/-- A role's default where nothing declares it. `first` takes the first of
its roles that resolves (one role is the one-level alias); `readable` stands
on a bar: the first candidate whose colour meets the role's need there, else
the first candidate, and the `unbarred` list where no bar resolves; `inPrint`
is a role's value in the print column whatever the scheme asked for — the
paper and ink as printed; `code` is a listing code role's colour, which the
code rule derives from the palette's roles on the ground the listing stands
on (`CodeColor.resolve`), the listing's style holding what it leaves open;
`seeded` is the colour the palette's seeds generate for a role. -/
public inductive Fallback where
  | first (roles : List Role)
  | readable (bar : Role) (candidates : List Role) (unbarred : List Role)
  | inPrint (role : Role)
  | const (c : Color)
  | absent
  | code
  /-- The colour the palette's seeds generate for a role: the document's own
  seeds where it declares them, else the class's default seeds at the class's
  depth (`SeedPalette`). -/
  | seeded (role : Role)
  deriving Repr, BEq

/-- The roles a default reads. -/
@[expose] public def Fallback.refs : Fallback → List Role
  | .first rs => rs
  | .readable bar cs us => bar :: cs ++ us
  | .inPrint r => [r]
  | .const _ | .absent | .code | .seeded _ => []

/-- When a role's site exists: always, or only where another role resolves —
a title page's ink stands only on a declared title-page ground. -/
public inductive Presence where
  | always
  | on (r : Role)
  deriving Repr, BEq, DecidableEq

/-- Whether a site's presence holds, reading the roles it depends on
through `look`. -/
@[expose] public def Presence.holds (look : Role → Option Color) : Presence → Bool
  | .always => true
  | .on r => (look r).isSome

/-- An element whose shipping the document's contrast report reads off the
body, per epoch: a titled block's title (by the title's colour kind), a
frame title on its bar, a standout frame, a title page with a ground of its
own, a link's focus ring. -/
public inductive Element where
  | blockTitle | alertTitle | exampleTitle | frameTitle | standout | titlePage
  /-- The ring the HTML page draws around a link that takes focus. -/
  | focusRing
  deriving Repr, DecidableEq, Inhabited

/-- The element a titled block's title ships as: tcolorbox's box takes the
plain block's colours, as its roles do (`Role.titleInk`). -/
@[expose] public def Element.ofTitled : TitledKind → Element
  | .block | .box => .blockTitle
  | .alert => .alertTitle
  | .example => .exampleTitle

/-- Where the document's contrast report reads a role's site: on every page,
in every epoch (the page's text); wherever the element it inks ships, in the
epoch it ships in; or through the runs coloured with it, which the report's
walk meets as uses. A role's row decides this, so a role added to the
registry is read by the report the way its row says (`Contrast.judged_covers`). -/
public inductive Judged where
  | page
  | element (e : Element)
  | uses
  deriving Repr, DecidableEq, Inhabited

/-- The beamer colour channel an element writes. -/
public inductive Channel where
  | fg | bg
  deriving Repr, BEq, DecidableEq

/-- One role's data. `ground` is the role its ink is judged on (the page
when that role resolves to nothing); `beamer` the `\setbeamercolor`
elements and channels that write it; `exportName` its name in a TeX export;
`noun` what a diagnostic calls the role's element; `region` whether body
content (running text, a listing, a figure) flows on it as a ground; `judged`
where the document's contrast report reads its site. -/
public structure Row where
  key : Option String
  css : String
  need : Need
  ground : Option Role
  fallback : ClassRow → Scheme → Fallback
  judged : Judged
  presence : Presence
  beamer : List (String × Channel)
  exportName : Option String
  noun : Option String
  region : Bool

@[expose] public def Row.hex (r g b : UInt8) : Color := { r, g, b }

/-- A default that is the same in every class and scheme. -/
@[expose] public def Row.every (f : Fallback) : ClassRow → Scheme → Fallback := fun _ _ => f

/-- A print default beside the screen pair (light, dark), in every class. -/
@[expose] public def Row.screen (print light : Fallback) (dark : Color) :
    ClassRow → Scheme → Fallback
  | _, .print => print
  | _, .light => light
  | _, .dark => .const dark

/-- A palette key's row: declared by `\palette{<key> = …}` and named
`--ltx-<key>` in CSS. -/
@[expose] public def Row.keyed (key : String) (need : Need) (ground : Option Role)
    (fallback : ClassRow → Scheme → Fallback) (judged : Judged) (beamer : List (String × Channel) := [])
    (presence : Presence := .always) (exportName : Option String := none)
    (noun : Option String := none) (region : Bool := false) : Row :=
  { key := some key, css := key, need, ground, fallback, judged, presence, beamer, exportName,
    noun, region }

/-- An engine role no `\palette` key declares, named `--ltx-<css>` in CSS. -/
@[expose] public def Row.engine (css : String) (need : Need) (ground : Option Role)
    (fallback : ClassRow → Scheme → Fallback) (judged : Judged) : Row :=
  { key := none, css, need, ground, fallback, judged, presence := .always, beamer := [],
    exportName := none, noun := none, region := false }

/-- A role a palette's seeds generate (`SeedPalette`): no `\palette` key, no
default, named `--ltx-<css>` in CSS and `<export>` in a TeX export. -/
@[expose] public def Row.generated (css : String) (need : Need) (ground : Option Role)
    (exportName : String) : Row :=
  { key := none, css, need, ground, fallback := Row.every .absent, judged := .uses,
    presence := .always, beamer := [], exportName := some exportName, noun := none,
    region := false }

/-- The candidates a bar's ink is chosen from: the page, then the ink. -/
@[expose] public def Row.onBar (bar : Role) (unbarred : List Role) :
    ClassRow → Scheme → Fallback :=
  Row.every (.readable bar [.page, .ink] unbarred)

/-- A secondary ink where nothing declares one, one relation in print and on
the light screen: the ink in LaTeX's classes, as they print every line, and
on a stage, as beamer's default theme does; on the web's row, which no LaTeX
class prints, the quietest tone the seeds generate that reads
(`SeedPalette`). -/
@[expose] public def Row.mutedFallback : ClassRow → Scheme → Fallback
  | .latex, _ => .first [.ink]
  | .stage, .dark => .const (Row.hex 0xA1 0xA1 0xAA)
  | .stage, _ => .first [.ink]
  | .web, .dark => .const (Row.hex 0xA1 0xA1 0xAA)
  | .web, _ => .seeded .muted

/-- A list marker's ink: the printed ink on paper and on the light screen —
one mark in both artifacts, as LaTeX sets a label in the running ink — and
the dark screen's own ink there. -/
@[expose] public def Row.markerFallback : ClassRow → Scheme → Fallback
  | _, .print => .first [.ink]
  | _, .light => .inPrint .ink
  | _, .dark => .first [.ink]

/-- The ground verbatim stands on where nothing declares one: none in LaTeX's
classes and on a stage, as they print it; on the web the documents' surface
the seeds generate, in print and on screen. -/
@[expose] public def Row.codeGround : ClassRow → Scheme → Fallback
  | .web, .print => .seeded .surface
  | .web, .light => .seeded .surface
  | .web, .dark => .const (Row.hex 0x27 0x27 0x2A)
  | .latex, _ => .absent
  | .stage, _ => .absent

open Row in

/-- **The registry.** One row per role, written out per constructor — an
added role is a missing arm, never a silent default. The print column is
the PDF's: black ink on unpainted (white) paper. The light column is the
screen's: the class's default seeds (`ClassColors.ink`, `.paper`, `.accent`)
and what they generate; the dark column the screen stylesheet's own colours.
The standout frame keeps the printed inversion in every scheme: its ground is
the ink as printed and its ink the paper (`paper`, `printInk`). -/
@[expose] public def Role.row : Role → Row
  | .page => keyed "bg" .decorative none
      (screen (.const Color.white) (.const ClassColors.paper) (Row.hex 0x18 0x18 0x1B))
      [("normal text", .bg), ("background canvas", .bg)] (exportName := some "Paper")
      (region := true) (judged := .uses)
  | .ink => keyed "fg" .text (some .page)
      (screen (.const Color.black) (.const ClassColors.ink) (Row.hex 0xFA 0xFA 0xF9))
      [("normal text", .fg)] (exportName := some "Ink") (judged := .page)
  | .muted => keyed "muted" .text (some .page) mutedFallback
      [("footline", .fg), ("page number in head/foot", .fg)] (exportName := some "Muted") (judged := .uses)
  | .alert => keyed "alert" .text (some .page) (every .absent) [("alerted text", .fg)]
      (exportName := some "Alert") (judged := .uses)
  | .example => keyed "example" .text (some .page) (every .absent) [("example text", .fg)]
      (exportName := some "Example") (judged := .uses)
  | .covered => keyed "covered" .state (some .page) (every .absent) (judged := .uses)
  | .marker => engine "marker" .text (some .page) markerFallback (judged := .uses)
  | .codeSurface => keyed "tint" .decorative none codeGround (judged := .uses)
  | .rule => keyed "rule" .decorative none
      (screen .absent (.seeded .rule) (Row.hex 0x3F 0x3F 0x46)) (judged := .uses)
  | .focus => keyed "focus" .nonText (some .page) (every (.first [.accentEdge, .accent]))
      (noun := some "the focus ring") (judged := .element .focusRing)
  | .accent => keyed "accent" .decorative none
      (screen .absent (.const ClassColors.accent) (Row.hex 0x60 0xA5 0xFA))
      (exportName := some "Accent") (judged := .uses)
  | .surface => generated "surface" .decorative none "Surface"
  | .surfaceStrong => generated "surface-strong" .decorative none "SurfaceStrong"
  | .accentWash => generated "accent-wash" .decorative none "AccentWash"
  | .accentSoft => generated "accent-soft" .decorative none "AccentSoft"
  | .accentText => generated "accent-text" .text (some .page) "AccentText"
  | .accentEdge => generated "accent-edge" .nonText (some .page) "AccentEdge"
  | .mutedOnInverse => generated "muted-on-inverse" .text (some .ink) "MutedOnDark"
  | .accentOnInverse => generated "accent-on-inverse" .text (some .ink) "AccentOnDark"
  | .diagramMuted => generated "diagram-muted" .nonText (some .page) "DiagramMuted"
  | .alertBandInk => generated "alert-band-ink" .text (some .accentSoft) "AlertTitle"
  | .exampleBandInk => generated "example-band-ink" .text (some .surfaceStrong) "ExampleTitle"
  | .paper => engine "paper" .decorative none (every (.inPrint .page)) (judged := .uses)
  | .printInk => engine "print-ink" .decorative none (every (.inPrint .ink)) (judged := .uses)
  | .frameTitleBar => keyed "frametitlebg" .decorative none (every .absent)
      [("frametitle", .bg), ("headline", .bg)] (noun := some "the frame-title bar") (judged := .uses)
  | .frameTitleInk => keyed "frametitlefg" .text (some .frameTitleBar)
      (onBar .frameTitleBar [.ink]) [("frametitle", .fg), ("headline", .fg)]
      (noun := some "the frame-title bar") (judged := .element .frameTitle)
  | .frameSubtitleInk => keyed "framesubtitlefg" .text (some .frameTitleBar)
      (every (.first [.frameTitleInk])) [("framesubtitle", .fg)] (judged := .uses)
  | .sectionTitleInk => keyed "sectiontitlefg" .text (some .page) (every (.first [.ink]))
      [("section title", .fg)] (judged := .uses)
  | .footBand => keyed "footlinebg" .decorative none (every .absent) [("footline", .bg)]
      (noun := some "the footline") (judged := .uses)
  | .footInk => engine "foot-ink" .text (some .footBand) (every (.first [.muted])) (judged := .uses)
  | .blockTitleBar => keyed "blocktitlebg" .decorative none (every .absent)
      [("block title", .bg)] (noun := some "the block-title bar") (judged := .uses)
  | .alertTitleBar => keyed "alerttitlebg" .decorative none (every .absent)
      [("block title alerted", .bg)] (noun := some "the block-title bar") (judged := .uses)
  | .exampleTitleBar => keyed "exampletitlebg" .decorative none (every .absent)
      [("block title example", .bg)] (noun := some "the block-title bar") (judged := .uses)
  | .blockTitleInk => keyed "blocktitlefg" .text (some .blockTitleBar)
      (onBar .blockTitleBar [.ink]) [("block title", .fg)] (noun := some "the block block title")
      (judged := .element .blockTitle)
  | .alertTitleInk => keyed "alerttitlefg" .text (some .alertTitleBar)
      (onBar .alertTitleBar [.alert, .ink]) [("block title alerted", .fg)]
      (noun := some "the alert block title") (judged := .element .alertTitle)
  | .exampleTitleInk => keyed "exampletitlefg" .text (some .exampleTitleBar)
      (onBar .exampleTitleBar [.example, .ink]) [("block title example", .fg)]
      (noun := some "the example block title") (judged := .element .exampleTitle)
  | .blockBodyInk => keyed "blockbodyfg" .text (some .blockBodyGround)
      (every (.first [.ink])) [("block body", .fg)] (judged := .uses)
  | .alertBodyInk => keyed "alertbodyfg" .text (some .alertBodyGround)
      (every (.first [.ink])) [("block body alerted", .fg)] (judged := .uses)
  | .exampleBodyInk => keyed "examplebodyfg" .text (some .exampleBodyGround)
      (every (.first [.ink])) [("block body example", .fg)] (judged := .uses)
  | .blockBodyGround => keyed "blockbodybg" .decorative none (every (.first [.page]))
      [("block body", .bg)] (noun := some "the block body") (region := true) (judged := .uses)
  | .alertBodyGround => keyed "alertbodybg" .decorative none (every (.first [.page]))
      [("block body alerted", .bg)] (noun := some "the block body") (region := true) (judged := .uses)
  | .exampleBodyGround => keyed "examplebodybg" .decorative none (every (.first [.page]))
      [("block body example", .bg)] (noun := some "the block body") (region := true) (judged := .uses)
  | .standoutGround => keyed "standoutbg" .decorative none (every (.first [.printInk]))
      [("standout", .bg)] (noun := some "the standout frame") (region := true) (judged := .uses)
  | .standoutInk => keyed "standoutfg" .largeText (some .standoutGround)
      (every (.readable .standoutGround [.paper, .printInk] [.paper])) [("standout", .fg)]
      (noun := some "the standout frame") (judged := .element .standout)
  | .titlePageGround => keyed "titlepagebg" .decorative none (every .absent)
      (noun := some "the title page") (region := true) (judged := .uses)
  | .titlePageInk => keyed "titlepagefg" .text (some .titlePageGround)
      (onBar .titlePageGround []) (presence := .on .titlePageGround)
      (noun := some "the title page") (judged := .element .titlePage)
  | .separator => keyed "separator" .decorative none (every (.first [.progressFill, .ink]))
      [("title separator", .fg)] (judged := .uses)
  | .progressFill => keyed "progressfg" .decorative none (every .absent)
      [("progress bar", .fg)] (judged := .uses)
  | .progressTrack => keyed "progressbg" .decorative none (every (.first [.page]))
      [("progress bar", .bg)] (judged := .uses)
  | .sectionProgressFill => keyed "sectionprogressfg" .decorative none
      (every (.first [.progressFill])) [("progress bar in section page", .fg)] (judged := .uses)
  | .sectionProgressTrack => keyed "sectionprogressbg" .decorative none
      (every (.first [.progressTrack])) [("progress bar in section page", .bg)] (judged := .uses)
  | .codeInk => keyed "codeink" .text (some .codeSurface) (every (.first [.ink])) (judged := .uses)
  | .codeKeyword => keyed "codekeyword" .text (some .codeSurface) (every .code) (judged := .uses)
  | .codeName => keyed "codename" .text (some .codeSurface) (every .code) (judged := .uses)
  | .codeLiteral => keyed "codeliteral" .text (some .codeSurface) (every .code) (judged := .uses)
  | .codeComment => keyed "codecomment" .text (some .codeSurface) (every .code) (judged := .uses)
  | .codeError => keyed "codeerror" .text (some .codeSurface) (every .code) (judged := .uses)

/-- A role's stratum: one more than the deepest role its defaults read, in
any scheme. `Role.fallback_depth_monotone` checks the table against every
row, so the resolver's recursion on it is well founded by the data. -/
@[expose] public def Role.depth : Role → Nat
  | .page | .ink | .alert | .example | .covered | .codeSurface | .rule => 0
  | .accent | .surface | .surfaceStrong | .accentWash | .accentSoft | .accentText => 0
  | .accentEdge | .mutedOnInverse | .accentOnInverse | .diagramMuted => 0
  | .alertBandInk | .exampleBandInk => 0
  | .focus => 1
  | .frameTitleBar | .footBand | .blockTitleBar | .alertTitleBar | .exampleTitleBar => 0
  | .titlePageGround | .progressFill => 0
  | .codeKeyword | .codeName | .codeLiteral | .codeComment | .codeError => 0
  | .muted | .codeInk | .frameTitleInk | .sectionTitleInk | .paper | .printInk => 1
  | .blockTitleInk | .alertTitleInk | .exampleTitleInk => 1
  | .blockBodyInk | .alertBodyInk | .exampleBodyInk => 1
  | .blockBodyGround | .alertBodyGround | .exampleBodyGround => 1
  | .titlePageInk | .separator | .progressTrack | .sectionProgressFill => 1
  | .marker => 1
  | .frameSubtitleInk | .footInk | .standoutGround | .sectionProgressTrack => 2
  | .standoutInk => 3

/-- A number at or past the last constructor's index: `ofNat` saturates, so
it names the last constructor without naming it by hand, which makes
`Role.count` derivable (the `DiagCode` registry's shape). -/
@[expose] public def Role.ctorCeiling : Nat := 4096

/-- How many roles the registry holds, read off the type. -/
@[expose] public def Role.count : Nat := (Role.ofNat Role.ctorCeiling).ctorIdx + 1

/-- Every role, derived from the type through the `ofNat` that
`deriving DecidableEq` synthesises: constructor declaration order, complete
by `Role.all_complete` and duplicate-free by `Role.all_nodup`
(`DesignRoleContract`). -/
@[expose] public def Role.all : List Role :=
  (List.range Role.count).map Role.ofNat

public theorem Role.all_complete (r : Role) : Role.all.contains r := by
  cases r <;> rfl

/-- **Every default reads only shallower roles**, in every class and scheme:
the measure `Design.at` recurses on. -/
public theorem Role.fallback_depth_monotone :
    (Role.all.all fun r => ClassRow.all.all fun c => Scheme.all.all fun s =>
      ((r.row.fallback c s).refs.all fun r' => decide (r'.depth < r.depth))) = true := by
  decide +kernel

/-- **The page's text is the one role read at every page**: the ink. -/
public theorem Role.judged_page : Role.all.filter (fun r => r.row.judged == .page) = [.ink] := by
  decide

/-- Every keyed role beside its key, in registry order: the table a key is
read through, so a lookup compares keys and builds no row. -/
@[expose] public def Role.keyed : Array (String × Role) :=
  (Role.all.filterMap fun r => r.row.key.map (·, r)).toArray

/-- The role a `\palette` key declares. -/
@[expose] public def Role.ofKey? (k : String) : Option Role :=
  (Role.keyed.find? (·.1 == k)).map (·.2)

/-- The registry's role for a listing code role (`ListingHighlight.Role`):
the role whose `\palette` key declares that code role's colour. -/
@[expose] public def Role.ofCode : ListingHighlight.Role → Role
  | .ink => .codeInk
  | .keyword => .codeKeyword
  | .name => .codeName
  | .literal => .codeLiteral
  | .comment => .codeComment
  | .error => .codeError

/-- The listing code role a registry role is, if it is one. -/
@[expose] public def Role.code? : Role → Option ListingHighlight.Role
  | .codeInk => some .ink
  | .codeKeyword => some .keyword
  | .codeName => some .name
  | .codeLiteral => some .literal
  | .codeComment => some .comment
  | .codeError => some .error
  | .page | .ink | .muted | .alert | .example | .covered | .marker | .codeSurface
  | .rule | .focus | .accent | .surface | .surfaceStrong | .accentWash | .accentSoft
  | .accentText | .accentEdge | .mutedOnInverse | .accentOnInverse | .diagramMuted
  | .alertBandInk | .exampleBandInk | .paper | .printInk | .frameTitleBar | .frameTitleInk
  | .frameSubtitleInk
  | .sectionTitleInk | .footBand | .footInk | .blockTitleBar | .alertTitleBar
  | .exampleTitleBar | .blockTitleInk | .alertTitleInk | .exampleTitleInk
  | .blockBodyInk | .alertBodyInk | .exampleBodyInk | .blockBodyGround
  | .alertBodyGround | .exampleBodyGround | .standoutGround | .standoutInk
  | .titlePageGround | .titlePageInk | .separator | .progressFill | .progressTrack
  | .sectionProgressFill | .sectionProgressTrack => none

/-- **The role an xcolor colour of a key declares**: a listing's code role,
whose colour a document declares by an xcolor colour of its key
(`\definecolor{codekeyword}`, `\colorlet{codecomment}{…}`) — the spelling
both engines compile, no beamer element carrying the role: leantex reads the
role, and a TeX build the colour wherever the document's own highlighting
names it. Every other name an xcolor definition gives stays an author colour,
as xcolor keeps it: the minted manual's `\definecolor{bg}` paints no page,
and beamer's `\alert` reads its `alerted text`, never a colour named alert. -/
@[expose] public def Role.ofXcolor? (k : String) : Option Role :=
  (Role.ofKey? k).filter fun r => (Role.code? r).isSome

public theorem Role.code?_ofCode (r : ListingHighlight.Role) : (Role.ofCode r).code? = some r := by
  cases r <;> rfl

/-- The code roles, in registry order. -/
@[expose] public def Role.codeRoles : List Role := ListingHighlight.Role.all.map Role.ofCode

/-- The `\palette` key a code role's colour is declared under. -/
@[expose] public def codeKey (r : ListingHighlight.Role) : String := (Role.ofCode r).row.key.getD ""

/-! ## CSS names

Every colour custom property the HTML backend declares, by kind: a role is
`--ltx-<css>`, an author colour `--ltx-c-<escape>`, a length token keeps its
own `--<name>`. The kinds cannot collide (`CssName.ident_inj`), and none
can collide with the engine's internal `--ltx-box-*` and `--ltx-cap*`
names (`CssName.ident_internal`). -/

private def hexDigit (d : Nat) : Char :=
  "0123456789abcdef".toList.getD d '0'

/-- A scalar as six hex digits: every Unicode scalar fits (below 0x110000). -/
private def hex6 (n : Nat) : List Char :=
  [hexDigit (n / 1048576 % 16), hexDigit (n / 65536 % 16), hexDigit (n / 4096 % 16),
   hexDigit (n / 256 % 16), hexDigit (n / 16 % 16), hexDigit (n % 16)]

/-- An ASCII letter or digit stands as itself; every other character as `_`
and its scalar's six hex digits, so the escape is a valid CSS identifier
whatever the name, and the `_` it introduces is never a kept character. -/
private def escChar (c : Char) : List Char :=
  if c.isAlphanum then [c] else '_' :: hex6 c.toNat

public def cssEscape (s : String) : String := String.ofList (s.toList.flatMap escChar)

/-- A colour custom property, by kind. -/
public inductive CssName where
  | role (r : Role)
  | color (name : String)
  | token (name : String)
  deriving Repr, BEq, DecidableEq

/-- The property's identifier after its `--`. -/
@[expose] public def CssName.ident : CssName → String
  | .role r => "ltx-" ++ r.row.css
  | .color n =>
    let escaped := cssEscape n
    "ltx-c-" ++ escaped
  | .token n => n

/-- A token name a `\tokens` declaration can carry: a document key is an
identifier (`Decl.isIdentChar`), which never holds `-`. -/
public def CssName.wellFormed : CssName → Prop
  | .token n => '-' ∉ n.toList
  | .role _ | .color _ => True

/-- A colour a document names: a role of the registry, or an author colour
(`\definecolor`, `\colorlet`, a `\palette` key no role owns). Separate kinds,
so no author name ever binds a role: `\definecolor{bg}` is the colour `bg`,
never the page. -/
public inductive ColorRef where
  | role (r : Role)
  | color (name : String)
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- The name's source spelling: a role's `\palette` key (its CSS identifier
when it has none), an author colour's own name. What the dump prints. -/
@[expose] public def ColorRef.key : ColorRef → String
  | .role r => r.row.key.getD r.row.css
  | .color n => n

/-- How a `\palette` key reads: the role it names, else an author colour. -/
@[expose] public def ColorRef.ofKey (k : String) : ColorRef :=
  match Role.ofKey? k with
  | some r => .role r
  | none => .color k

/-- The custom property a name is declared as. -/
@[expose] public def ColorRef.css : ColorRef → CssName
  | .role r => .role r
  | .color n => .color n

/-- The custom property a run named by this colour reads in HTML: a role's
`--ltx-<css>`, an author colour's `--ltx-c-<escape>` (`CssName.ident`), so no
author name can spell a role's or the engine's own property. -/
@[expose] public def ColorRef.property (ref : ColorRef) : String :=
  "--" ++ ref.css.ident

end LeanTex.Core.Ir
