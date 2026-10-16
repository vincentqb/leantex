module

public import LeanTex.Core.Color
public import LeanTex.Core.CodeRoles

/-! The colour roles every artifact paints, as one typed registry read through one resolver
(`Design.at`): palette roles, and element roles whose defaults refer to them. -/

namespace LeanTex.Core.Ir

/-- What a role's ink owes its ground by WCAG 2.2: text, large text (SC 1.4.3), non-text, a
state change (SC 1.4.11), or nothing. -/
public inductive Need where
  | text | largeText | nonText | state | decorative
  deriving Repr, DecidableEq, Inhabited

/-- A need the contrast judge holds a pair to on a ground. -/
@[expose] public def Need.paired : Need → Bool
  | .text | .largeText | .nonText => true
  | .state | .decorative => false

/-- A need as its medium shows it: a slide's text is judged as large-scale text. -/
@[expose] public def Need.atStage (stage : Bool) : Need → Need
  | .text => if stage then .largeText else .text
  | .largeText => .largeText
  | .nonText => .nonText
  | .state => .state
  | .decorative => .decorative

/-- The titled block's kind: beamer's three block environments and tcolorbox's box. -/
public inductive TitledKind where
  | block
  | alert
  | example
  | box
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The kind's one spelling, the HTML class suffix. -/
@[expose] public def TitledKind.name : TitledKind → String
  | .block => "block"
  | .alert => "alert"
  | .example => "example"
  | .box => "box"

/-- The role-key stem the kind's colours resolve through; the box takes the plain block's. -/
@[expose] public def TitledKind.roleStem : TitledKind → String
  | .block | .box => "block"
  | .alert => "alert"
  | .example => "example"

/-- The medium a resolution is for: print, light and dark screens, and their
`prefers-contrast: more` variants. -/
public inductive Scheme where
  | print | light | dark | lightMore | darkMore
  deriving Repr, DecidableEq, Inhabited

@[expose] public def Scheme.all : List Scheme := [.print, .light, .dark, .lightMore, .darkMore]

/-- Whether a scheme stands on a dark page. -/
@[expose] public def Scheme.onDark : Scheme → Bool
  | .dark | .darkMore => true
  | .print | .light | .lightMore => false

/-- Whether a scheme is one the reader asks more contrast of, judged by WCAG
2.2's enhanced criterion (SC 1.4.6). -/
@[expose] public def Scheme.more : Scheme → Bool
  | .lightMore | .darkMore => true
  | .print | .light | .dark => false

/-- The scheme of the same polarity that asks no more contrast: what a more
scheme starts from. -/
@[expose] public def Scheme.base : Scheme → Scheme
  | .print => .print
  | .light | .lightMore => .light
  | .dark | .darkMore => .dark

/-- The scheme's one spelling: a diagnostic's subject, a report's column. -/
@[expose] public def Scheme.name : Scheme → String
  | .print => "print"
  | .light => "light"
  | .dark => "dark"
  | .lightMore => "lightMore"
  | .darkMore => "darkMore"

/-- How far a class's grounds stand from its page as WCAG 2.2 ratios ×1000, and whether its
medium is a stage, whose text is judged as large-scale (`Need.atStage`). -/
public structure GroundDepth where
  body : Nat
  band : Nat
  rule : Nat
  pair : Nat
  stage : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The medium's text floor on a light page, ×1000: large-scale text's 3:1 on a stage, normal
text's 4.5:1 elsewhere (WCAG 2.2 SC 1.4.3, `Contrast.depth_text_exact`). -/
@[expose] public def GroundDepth.text (d : GroundDepth) : Nat := if d.stage then 3000 else 4500

/-- A document's: a body at GitHub's code ground on white (1.06:1), a band at 1.15:1, rules at
Tailwind slate-300's 1.49:1, the band 1.07:1 from the body. -/
@[expose] public def GroundDepth.documents : GroundDepth :=
  { body := 1060, band := 1150, rule := 1490, pair := 1070, stage := false }

/-- A deck's: grounds near Radix slate steps 3 and 5 on white (1.14:1, 1.31:1), the band 1.10:1
from the body, its stage text large-scale. -/
@[expose] public def GroundDepth.decks : GroundDepth :=
  { body := 1120, band := 1300, rule := 1490, pair := 1100, stage := true }

/-- A poster's: a deck's grounds, read across a room too, on a printed
board, whose text the judge holds as a page's. -/
@[expose] public def GroundDepth.posters : GroundDepth := { GroundDepth.decks with stage := false }

/-- The depths the classes stand at, each once. -/
@[expose] public def GroundDepth.all : List GroundDepth := [.documents, .decks, .posters]

/-- The share pending overlay content covers to unless the document declares one: none, so it
is hidden with its place kept, as beamer's default `invisible` covering hides it. -/
@[expose] public def coveredFractionDefault : Nat := 0

/-- beamer's `transparent` share, which `\setbeamercovered{transparent}` declares and a declared
cover colour's own coloured runs take. -/
@[expose] public def transparentShare : Nat := 15

/-- beamer's `dynamic` share for the steps next to show, which its graded covering sets ahead of
fainter ones (beamerbaseoverlay.sty). -/
@[expose] public def dynamicShare : Nat := 10

/-- beamer's `highly dynamic` share for the step next to show, which its graded covering sets ahead
of fainter ones (beamerbaseoverlay.sty). -/
@[expose] public def highlyDynamicShare : Nat := 15

/-- What a class asks of colours nothing declares: LaTeX's classes print secondary ink in the
ink, the web's keep a quieter one and tinted verbatim. -/
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

/-- The default seeds' ink, Tailwind v4's zinc-900; the paper is white, the accent blue-700. -/
@[expose] public def ClassColors.ink : Color := { r := 0x18, g := 0x18, b := 0x1B }

@[expose] public def ClassColors.paper : Color := { r := 0xFF, g := 0xFF, b := 0xFF }

@[expose] public def ClassColors.accent : Color := { r := 0x1D, g := 0x4E, b := 0xD8 }

/-- Every colour role: palette roles first, then the element roles that paint one site each. -/
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
  | alertMark
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

/-- A role's default where nothing declares it: the first role that resolves, a readable ink on a
bar, the printed value, a code role's derived colour, or a seeded one. -/
public inductive Fallback where
  | first (roles : List Role)
  | readable (bar : Role) (candidates : List Role) (unbarred : List Role)
  | inPrint (role : Role)
  | const (c : Color)
  | absent
  | code
  /-- The colour the palette's seeds generate for a role, else the class's default seeds'. -/
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

/-- An element whose shipping the contrast report reads off the body, per epoch. -/
public inductive Element where
  | blockTitle | alertTitle | exampleTitle | frameTitle | standout | titlePage
  /-- The ring the HTML page draws around a link that takes focus. -/
  | focusRing
  deriving Repr, DecidableEq, Inhabited

/-- The element a titled block's title ships as; the box takes the plain block's. -/
@[expose] public def Element.ofTitled : TitledKind → Element
  | .block | .box => .blockTitle
  | .alert => .alertTitle
  | .example => .exampleTitle

/-- Where the contrast report reads a role's site: every page, where its element ships, or its
coloured runs. -/
public inductive Judged where
  | page
  | element (e : Element)
  | uses
  deriving Repr, DecidableEq, Inhabited

/-- The beamer colour channel an element writes. -/
public inductive Channel where
  | fg | bg
  deriving Repr, BEq, DecidableEq

/-- One role's data: `ground` the role its ink is judged on, `noun` its element's name in a
diagnostic, `judged` where its site is read. -/
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

@[expose] public def Row.hex (r g b : UInt8) : Color := { r, g, b }

/-- A default that is the same in every class and scheme. -/
@[expose] public def Row.every (f : Fallback) : ClassRow → Scheme → Fallback := fun _ _ => f

/-- A print default beside the screen's, in every class: one default for
every screen scheme, which resolves against that scheme's own seeds. -/
@[expose] public def Row.screen (print screen : Fallback) : ClassRow → Scheme → Fallback
  | _, .print => print
  | _, .light | _, .dark | _, .lightMore | _, .darkMore => screen

/-- A palette key's row: declared by `\palette{<key> = …}` and named
`--ltx-<key>` in CSS. -/
@[expose] public def Row.keyed (key : String) (need : Need) (ground : Option Role)
    (fallback : ClassRow → Scheme → Fallback) (judged : Judged) (beamer : List (String × Channel) := [])
    (presence : Presence := .always) (exportName : Option String := none)
    (noun : Option String := none) : Row :=
  { key := some key, css := key, need, ground, fallback, judged, presence, beamer, exportName,
    noun }

/-- An engine role no `\palette` key declares, named `--ltx-<css>` in CSS. -/
@[expose] public def Row.engine (css : String) (need : Need) (ground : Option Role)
    (fallback : ClassRow → Scheme → Fallback) (judged : Judged) : Row :=
  { key := none, css, need, ground, fallback, judged, presence := .always, beamer := [],
    exportName := none, noun := none }

/-- A role a palette's seeds generate (`SeedPalette`): no `\palette` key, no
default, named `--ltx-<css>` in CSS and `<export>` in a TeX export. -/
@[expose] public def Row.generated (css : String) (need : Need) (ground : Option Role)
    (exportName : String) : Row :=
  { key := none, css, need, ground, fallback := Row.every .absent, judged := .uses,
    presence := .always, beamer := [], exportName := some exportName, noun := none }

/-- The candidates a bar's ink is chosen from: the page, then the ink. -/
@[expose] public def Row.onBar (bar : Role) (unbarred : List Role) :
    ClassRow → Scheme → Fallback :=
  Row.every (.readable bar [.page, .ink] unbarred)

/-- A secondary ink where nothing declares one: the ink in LaTeX's classes and on a stage, the
seeds' quietest legible tone on the web. -/
@[expose] public def Row.mutedFallback : ClassRow → Scheme → Fallback
  | .latex, _ | .stage, _ => .first [.ink]
  | .web, _ => .seeded .muted

/-- A list marker's ink: the printed ink on paper and a light screen, a dark screen's own ink. -/
@[expose] public def Row.markerFallback : ClassRow → Scheme → Fallback
  | _, .print => .first [.ink]
  | _, .light | _, .lightMore => .inPrint .ink
  | _, .dark | _, .darkMore => .first [.ink]

/-- Verbatim's ground where nothing declares one: none in LaTeX's classes, the generated
surface on the web. -/
@[expose] public def Row.codeGround : ClassRow → Scheme → Fallback
  | .web, _ => .seeded .surface
  | .latex, _ | .stage, _ => .absent

open Row in

/-- The registry: one row per role, every constructor spelled; the print column is black ink on
white paper. -/
@[expose] public def Role.row : Role → Row
  | .page => keyed "bg" .decorative none (screen (.const Color.white) (.seeded .page))
      [("normal text", .bg), ("background canvas", .bg)] (exportName := some "Paper")
      (judged := .uses)
  | .ink => keyed "fg" .text (some .page) (screen (.const Color.blackInk) (.seeded .ink))
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
  | .rule => keyed "rule" .decorative none (screen .absent (.seeded .rule)) (judged := .uses)
  | .focus => keyed "focus" .nonText (some .page) (every (.first [.accentEdge, .accent]))
      (noun := some "the focus ring") (judged := .element .focusRing)
  | .accent => keyed "accent" .decorative none (screen .absent (.seeded .accent))
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
      [("block body", .bg)] (noun := some "the block body") (judged := .uses)
  | .alertBodyGround => keyed "alertbodybg" .decorative none (every (.first [.page]))
      [("block body alerted", .bg)] (noun := some "the block body") (judged := .uses)
  | .exampleBodyGround => keyed "examplebodybg" .decorative none (every (.first [.page]))
      [("block body example", .bg)] (noun := some "the block body") (judged := .uses)
  | .standoutGround => keyed "standoutbg" .decorative none (every (.first [.printInk]))
      [("standout", .bg)] (noun := some "the standout frame") (judged := .uses)
  | .standoutInk => keyed "standoutfg" .largeText (some .standoutGround)
      (every (.readable .standoutGround [.paper, .printInk] [.paper])) [("standout", .fg)]
      (noun := some "the standout frame") (judged := .element .standout)
  | .titlePageGround => keyed "titlepagebg" .decorative none (every .absent)
      (noun := some "the title page") (judged := .uses)
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
  | .alertMark => keyed "alertmark" .decorative none (every .absent) (judged := .uses)
      (exportName := some "AlertMark") (noun := some "the alert's mark")

/-- A role's stratum: one more than the deepest role its defaults read, in any scheme. -/
@[expose] public def Role.depth : Role → Nat
  | .page | .ink | .alert | .example | .covered | .codeSurface | .rule => 0
  | .accent | .surface | .surfaceStrong | .accentWash | .accentSoft | .accentText => 0
  | .accentEdge | .mutedOnInverse | .accentOnInverse | .diagramMuted => 0
  | .alertBandInk | .exampleBandInk => 0
  | .focus => 1
  | .frameTitleBar | .footBand | .blockTitleBar | .alertTitleBar | .exampleTitleBar => 0
  | .titlePageGround | .progressFill => 0
  | .codeKeyword | .codeName | .codeLiteral | .codeComment | .codeError | .alertMark => 0
  | .muted | .codeInk | .frameTitleInk | .sectionTitleInk | .paper | .printInk => 1
  | .blockTitleInk | .alertTitleInk | .exampleTitleInk => 1
  | .blockBodyInk | .alertBodyInk | .exampleBodyInk => 1
  | .blockBodyGround | .alertBodyGround | .exampleBodyGround => 1
  | .titlePageInk | .separator | .progressTrack | .sectionProgressFill => 1
  | .marker => 1
  | .frameSubtitleInk | .footInk | .standoutGround | .sectionProgressTrack => 2
  | .standoutInk => 3

/-- A number at or past the last constructor's index, where `ofNat` saturates. -/
@[expose] public def Role.ctorCeiling : Nat := 4096

/-- How many roles the registry holds, read off the type. -/
@[expose] public def Role.count : Nat := (Role.ofNat Role.ctorCeiling).ctorIdx + 1

/-- Every role, in declaration order, derived from the type. -/
@[expose] public def Role.all : List Role :=
  (List.range Role.count).map Role.ofNat

public theorem Role.all_complete (r : Role) : Role.all.contains r := by
  cases r <;> rfl

public theorem Role.fallback_depth_monotone :
    (Role.all.all fun r => ClassRow.all.all fun c => Scheme.all.all fun s =>
      ((r.row.fallback c s).refs.all fun r' => decide (r'.depth < r.depth))) = true := by
  decide +kernel

public theorem Role.judged_page : Role.all.filter (fun r => r.row.judged == .page) = [.ink] := by
  decide

/-- Every keyed role beside its key, in registry order. -/
@[expose] public def Role.keyed : Array (String × Role) :=
  (Role.all.filterMap fun r => r.row.key.map (·, r)).toArray

/-- The role a `\palette` key declares. -/
@[expose] public def Role.ofKey? (k : String) : Option Role :=
  (Role.keyed.find? (·.1 == k)).map (·.2)

/-- The registry role whose `\palette` key declares a listing code role's colour. -/
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
  | .sectionProgressFill | .sectionProgressTrack | .alertMark => none

/-- The role an xcolor colour of a key declares: a listing code role or the alert's mark; any other
name stays an author colour. -/
@[expose] public def Role.ofXcolor? (k : String) : Option Role :=
  (Role.ofKey? k).filter fun r => (Role.code? r).isSome || r == .alertMark

public theorem Role.code?_ofCode (r : ListingHighlight.Role) : (Role.ofCode r).code? = some r := by
  cases r <;> rfl

/-- The `\palette` key a code role's colour is declared under. -/
@[expose] public def codeKey (r : ListingHighlight.Role) : String := (Role.ofCode r).row.key.getD ""

/-- An ASCII letter or digit as itself, any other character as `_` and six hex digits, which hold
every Unicode scalar. -/
private def escChar (c : Char) : List Char :=
  if c.isAlphanum then [c] else '_' :: Hex.digitList false 6 c.toNat

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

/-- A colour a document names: a registry role, or an author colour, which never binds a role. -/
public inductive ColorRef where
  | role (r : Role)
  | color (name : String)
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- The name's source spelling: a role's `\palette` key, else its CSS identifier; an author
colour's name. -/
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

/-- The custom property a run named by this colour reads in HTML. -/
@[expose] public def ColorRef.property (ref : ColorRef) : String :=
  "--" ++ ref.css.ident

end LeanTex.Core.Ir
