module

public import LeanTex.Core.Diag
public import LeanTex.Core.Heading
public import LeanTex.Core.ListingLang
public import LeanTex.Core.SurfaceKind
public import LeanTex.Core.Dim
public import LeanTex.Core.ClassArea
public import LeanTex.Core.Gfx
public import LeanTex.Core.Decl
public import LeanTex.Core.Image
public import LeanTex.Core.Math
public import LeanTex.Core.LocaleContract
public import LeanTex.Core.ListingHighlight
public import LeanTex.Core.DesignRole
public import LeanTex.Core.ContrastRatio
public import LeanTex.Core.Oklab
public import LeanTex.Core.Icc
public import LeanTex.Core.SeedPalette
public import LeanTex.Core.PaletteData
public import LeanTex.Core.CiteDecl
import LeanTex.Core.Loop
import LeanTex.Core.NameClaim
import LeanTex.Core.Marker
import LeanTex.Core.PdfLex
import LeanTex.Core.ContrastSolve
import Init.Data.Nat.ToString
public import Std.Data.HashMap
import Std.Data.HashSet
import LeanTex.Core.DeriveBEq

namespace LeanTex.Core.Ir

open LeanTex.Core LeanTex.Core.Dim

@[expose] public def baseFontSize : Length := Dim.pt 10

/-- Baseline distance as a per-mille of the font size. -/
@[expose] public def leadingMilli : Nat := 1200

/-- Baseline distance for a size: `leadingMilli` of it, scaled by the page's `leading` factor. -/
@[expose] public def leadingFor (size : Length) (factor : Nat := 1000) : Length :=
  size * (leadingMilli : Int) / (1000 : Int) * (factor : Int) / (1000 : Int)

@[expose] public def rhythmQuantum (size : Length) (factor : Nat := 1000) : Length :=
  leadingFor size factor / 2

/-- TeX's own `\parskip` where nothing declares one: latex.ltx's `\parskip 0pt plus 1pt`. -/
public def texParskipDefault : SymGlue := { stretch := Dim.SymLength.ofLength (Dim.pt 1) }

/-- The default gap between peer paragraphs: one rhythm quantum of the governing size, stretching
as TeX's `\parskip` does. -/
@[expose] public def parskipDefault (size : Length) : SymGlue :=
  { texParskipDefault with width := Dim.SymLength.ofLength (rhythmQuantum size) }

public theorem rhythmQuantum_pos (size : Length) (h : Dim.pt 1 ≤ size) :
    0 < rhythmQuantum size := by
  simp only [rhythmQuantum, leadingFor, leadingMilli, Dim.pt_eq] at h ⊢
  length_omega

public theorem rhythmQuantum_lt_double (size : Length) (h : Dim.pt 1 ≤ size) :
    rhythmQuantum size < 2 * rhythmQuantum size := by
  simp only [rhythmQuantum, leadingFor, leadingMilli, Dim.pt_eq] at h ⊢
  length_omega

/-- The default gap between a cut mark's inner end and the trim, wider than
guillotine cutting tolerance (1/16 in). -/
public def cutMarkGap : Length := inch 3 / 40

/-- The default cut-mark thickness: a 0.5 bp hairline. -/
public def cutMarkThickness : Length := bp 1 / 2

/-- The line-through rule thickness both backends draw: ulem's default `\ULthickness`. -/
@[expose] public def lineThroughThickness : Length := pt 2 / 5

/-- One rule a shipout hook draws on every printed sheet, so the PDF's alone: its box in medium
coordinates, x right and y down from the top-left corner, its palette name, and whether it paints
over the content, as `shipout/foreground` draws. -/
public structure DrawnRule where
  x : Length
  y : Length
  w : Length
  h : Length
  color : String
  front : Bool
  deriving Repr, BEq, Inhabited

/-- A PDF page box (ISO 32000-2 §14.11.2). -/
public inductive BoxKind where
  | crop
  | bleed
  | trim
  | art
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The page dictionary key a box is written under. -/
@[expose] public def BoxKind.key : BoxKind → String
  | .crop => "CropBox"
  | .bleed => "BleedBox"
  | .trim => "TrimBox"
  | .art => "ArtBox"

/-- A page box a document declares, in PDF user space: x right and y up from the medium's
lower-left corner, lower-left corner first, and where it was declared. -/
public structure PageBox where
  kind : BoxKind
  x0 : Length
  y0 : Length
  x1 : Length
  y1 : Length
  span : Option Span
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The box within a medium `w` by `h`, each corner moved inside it. -/
@[expose] public def PageBox.clampTo (b : PageBox) (w h : Length) : PageBox :=
  let c (lo hi v : Length) : Length := max lo (min hi v)
  { b with x0 := c 0 w b.x0, y0 := c 0 h b.y0, x1 := c 0 w b.x1, y1 := c 0 h b.y1 }

@[expose] public def PageBox.hasArea (b : PageBox) : Bool := b.x0 < b.x1 && b.y0 < b.y1

/-- The declared boxes a medium `w` by `h` ships: each moved inside it, one with no area there
dropped. -/
@[expose] public def PageBox.shipped (boxes : Array PageBox) (w h : Length) : Array PageBox :=
  (boxes.map (·.clampTo w h)).filter (·.hasArea)

/-- A page's declared vertical keys, which place its text block once the class settles the page. -/
public structure TextBlockDecl where
  top : Option Length := none
  bottom : Option Length := none
  height : Option Length := none
  ratio : Option (Nat × Nat) := none
  /-- The height as thousandths of the page's, where no height is declared (geometry's `vscale`). -/
  scale : Option Nat := none
  /-- A height standing under the top the other keys place (the kernel's `\textheight`). -/
  under : Option Length := none
  deriving Repr, BEq, Inhabited

/-- The declaration with its scaled height fixed on a page `page` tall. -/
public def TextBlockDecl.scaled (b : TextBlockDecl) (page : Length) : TextBlockDecl :=
  match b.height, b.scale with
  | none, some s => { b with height := some (page * (s : Int) / 1000) }
  | _, _ => b

/-- The margins a declaration leaves on a page `page` tall, else at `vm` and `bm`: a declared top, or
one a height places above a declared bottom or by a ratio, with a declared height under it. -/
@[expose] public def TextBlockDecl.place (b : TextBlockDecl) (page vm bm : Length) : Length × Length :=
  let top : Length := match b.top, b.bottom, b.height, b.ratio with
    | some t, _, _, _ => t
    | none, some m, some h, _ => page - m - h
    | none, none, some h, some (a, r) => (page - h) * (a : Int) / ((a + r : Nat) : Int)
    | _, _, _, _ => vm
  (top, match b.under.orElse fun _ => b.height with
    | some h => page - top - h
    | none => b.bottom.getD bm)

private theorem place_under (page t h : Length) : page - t - (page - t - h) = h := by length_omega

/-- A declared height is the text block's height. -/
public theorem TextBlockDecl.place_height (b : TextBlockDecl) (page vm bm h : Length)
    (hh : b.height = some h) (hu : b.under = none) :
    page - (b.place page vm bm).1 - (b.place page vm bm).2 = h := by
  simp only [TextBlockDecl.place, hh, hu, Option.orElse]
  exact place_under _ _ _

/-- A height standing under the top is the text block's height, and leaves the top where the other
keys place it. -/
public theorem TextBlockDecl.place_under_top (b : TextBlockDecl) (page vm bm u : Length)
    (hu : b.under = some u) :
    page - (b.place page vm bm).1 - (b.place page vm bm).2 = u ∧
      (b.place page vm bm).1 = ({ b with under := none }.place page vm bm).1 := by
  simp only [TextBlockDecl.place, hu, Option.orElse]
  exact ⟨place_under _ _ _, trivial⟩

private theorem place_over (page m h : Length) : page - (page - m - h) - h = m := by length_omega

/-- A height beside a declared bottom and no declared top stands on that bottom. -/
public theorem TextBlockDecl.place_bottom (b : TextBlockDecl) (page vm bm h m : Length)
    (hh : b.height = some h) (hm : b.bottom = some m) (ht : b.top = none)
    (hu : b.under = none) :
    (b.place page vm bm).2 = m := by
  simp only [TextBlockDecl.place, hh, hm, ht, hu, Option.orElse]
  exact place_over _ _ _

/-- TeX's page-break penalties at a paragraph's lines as latex.ltx sets them (`\clubpenalty`,
`\widowpenalty`, `\brokenpenalty`, `\displaywidowpenalty`, `\interlinepenalty`, `\predisplaypenalty`). -/
public structure PagePenalties where
  club : Int := 150
  widow : Int := 150
  broken : Int := 100
  displayWidow : Int := 50
  interline : Int := 0
  predisplay : Int := 10000
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A flow's web page layout, after the MyST site themes (@myst-theme/book and article 1.4.1 at
their widest breakpoint; testdata/oracles/myst-themes.tsv). -/
public inductive WebLayout where
  /-- book-theme's: the outline in a sidebar before the text, a free column after it. -/
  | book
  /-- article-theme's: the text first, the outline in a margin column after it. -/
  | article
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A web layout's grid in milli-rem, its measure's columns in digit widths (`ch`). -/
public structure WebGrid where
  /-- The measure's six body columns: `minmax(8ch,10ch)` (article-grid) or `minmax(8ch,12ch)`
  (article-left-grid) at their widest. -/
  proseCh : Nat
  /-- The rest of the measure: the body's two 1rem insets and its seven 0.75rem column gaps. -/
  insetMilli : Nat
  /-- Before the text: book-theme's sidebar (its table of contents 13.6 to 15.75rem wide), or
  article-left-grid's 3rem body outset. -/
  leadMilli : Nat
  /-- Between the lead and the text, or the text and the margin column: the sidebar's 1.5rem, or
  the margin column's 0.75rem gap and its outline's 2.5rem inset. -/
  gapMilli : Nat
  /-- After the text, at least: none (book), or article-left-grid's margin column's 10rem. -/
  marginMinMilli : Nat
  /-- After the text, at most: article-grid's 3rem, 13rem and 3rem page outset, or the 24rem the
  article outline's 388 px at a 1440 px viewport rounds to. -/
  marginMilli : Nat
  deriving Repr, BEq, Inhabited

public def WebLayout.grid : WebLayout → WebGrid
  | .book =>
    { proseCh := 60, insetMilli := 7250, leadMilli := 15000, gapMilli := 1500
      marginMinMilli := 0, marginMilli := 19000 }
  | .article =>
    { proseCh := 72, insetMilli := 7250, leadMilli := 3000, gapMilli := 3250
      marginMinMilli := 10000, marginMilli := 24000 }

public def WebLayout.names : List (String × WebLayout) := [("book", .book), ("article", .article)]

public def WebLayout.ofName? (n : String) : Option WebLayout := WebLayout.names.lookup n

/-- Page geometry, as declared by `\page`. -/
public structure PageSpec where
  width : Length := bp 612
  height : Length := bp 792
  vmargin : Length := 6 * leadingFor baseFontSize
  /-- The bottom margin where the page declares one apart from the top's (`vmargin`). -/
  bmargin : Option Length := none
  /-- The vertical keys declared so far, placed by `PageSpec.placed`. -/
  block : TextBlockDecl := {}
  hmargin : Length := inch 1
  /-- The body size, from `\page{ fontsize }` or the class option. -/
  fontSize : Length := baseFontSize
  /-- Line spacing as a factor over the default 1.2, in thousandths. -/
  leading : Nat := 1000
  /-- `\linespread` (`\page{ leading = … }`), in thousandths. -/
  spread : Nat := 1000
  /-- The body's `\baselineskip` as a class's `\normalsize` declares it;
  `none` keeps the 6⁄5 rule. -/
  bodySkip : Option Length := none
  /-- The gap between peer paragraphs, with its rubber; `none` is the engine's default. -/
  parskip : Option SymGlue := none
  /-- Whether the measure is checked against the readable band;
  `\page{ measure = free }` turns the check off. -/
  measureChecked : Bool := true
  /-- How far past the trim edge the PDF page extends on every side, for print finishing. -/
  bleed : Length := 0
  /-- Whether the pages ship printer's cut marks (`\page{ marks = cut }`). -/
  marks : Bool := false
  /-- The clearance between a cut mark's inward end and the trim line
  (`\page{ mark-gap = ... }`). -/
  markGap : Length := cutMarkGap
  /-- The cut marks' stroke thickness (`\page{ mark-thickness = ... }`). -/
  markThickness : Length := cutMarkThickness
  /-- The document's size ladder, per mille of the body; `none` is the engine's `sizeScale`. -/
  sizes : Option (List (String × Nat)) := none
  /-- Each named size's declared `\baselineskip`, per mille of the body size;
  `none` is size10.clo's. -/
  skips : Option (List (String × Nat)) := none
  /-- Whether paragraphs may hyphenate; `none` takes the class default. -/
  hyphenate : Option Bool := none
  /-- Whether paragraphs justify; `none` takes the class default. -/
  justify : Option Bool := none
  /-- Whether the ragged setting `justify` turns off is LaTeX's `\raggedright`
  (`\rightskip 0pt plus 1fil`). -/
  raggedFil : Bool := false
  /-- Whether boundary glyphs protrude into the margin (microtype's character
  protrusion); `none` takes the default, on. -/
  protrude : Option Bool := none
  /-- Whether font boxes may expand within microtype's ±2%; `none` takes the default, on. -/
  expand : Option Bool := none
  /-- Whether pages carry the physical page number, centred in the foot;
  `none` takes the class default. -/
  numbers : Option Bool := none
  /-- Whether counted body lines carry margin line numbers (lineno's `\linenumbers`). -/
  linenumbers : Option Bool := none
  /-- Print only line numbers divisible by this modulus (lineno's
  `\modulolinenumbers[n]`); `none` prints every counted line. -/
  lineModulo : Option Nat := none
  /-- Whether the list levels are the parskip package's (parskip.sty), which read a positive
  `\parskip` as KOMA-Script's do (`ListExtra.koma`). -/
  listsParskip : Bool := false
  /-- The distance from the running head's and foot's body-side ink edge to the body area. -/
  furnitureGap : Option Length := none
  /-- LaTeX's `\headsep`, as declared: it positions the header's baseline against the body. -/
  headsep : Option Length := none
  /-- LaTeX's `\footskip`, as declared: from the text area's floor to the foot's baseline. -/
  footskip : Option Length := none
  /-- The class's `\headsep` and `\footskip`, under any the document declares. -/
  classSeps : Option (Length × Length) := none
  /-- TeX's `\maxdepth` as the class sets it: how far a page's last line may reach below its text
  area. -/
  maxDepth : Length := 0
  /-- LaTeX's `\flushbottom` (`some true`) or `\raggedbottom` (`some false`);
  `none` is the class's own. -/
  flushBottom : Option Bool := none
  /-- The page-break penalties a paragraph's lines carry, as declared over LaTeX's. -/
  penalties : PagePenalties := {}
  /-- The rules the document draws on every page, in the order drawn. -/
  drawn : Array DrawnRule := #[]
  /-- The page boxes the document declares, one per kind, the last declaration standing. -/
  boxes : Array PageBox := #[]
  /-- Whether a declaration named the page's width, or its height, which the class's default leaves
  on that axis alone. -/
  widthSized : Bool := false
  heightSized : Bool := false
  /-- The text block's declared width, which centres it on the page the class settles. -/
  blockWidth : Option Length := none
  /-- The text block's width as thousandths of the page's (geometry's `hscale`), centred likewise. -/
  widthScale : Option Nat := none
  /-- Whether pages are two-sided: an even page is a verso, its margins and running fields mirrored. -/
  twoside : Bool := false
  /-- The left margin's share against the right's of the width the text block leaves, on a recto
  (geometry's `hmarginratio`); `none` centres the block, or splits 2:3 on two-sided pages. -/
  sideRatio : Option (Nat × Nat) := none
  /-- Whether the running head shows the headings' marks (LaTeX's `headings` page style). -/
  markHeads : Bool := false
  /-- Whether a chapter opens on a recto of two-sided pages (book.cls's `openright`). -/
  openRight : Bool := false
  /-- The web layout as declared (`\page{ web = … }`); `none` takes the class's. -/
  web : Option WebLayout := none
  /-- Whether the web page's measure is its layout's, the surface leaving the text block undeclared. -/
  webMeasure : Bool := false
  /-- The rule under a running head, fancyhdr's `\headrulewidth` thick, a strut's depth below its
  baseline. -/
  headRule : Option Length := none
  /-- Whether a plain page (a chapter's opening, `\maketitle`'s) sets the plain style over the
  declared running fields, as LaTeX's page styles do. -/
  plainPages : Bool := false
  deriving Repr, BEq, Inhabited

public def PageSpec.bottomMargin (spec : PageSpec) : Length := spec.bmargin.getD spec.vmargin

/-- The left margin's share against the right's: as declared, else 2:3 on two-sided pages, as the
standard classes' `\oddsidemargin` and geometry's `twoside` split it. -/
public def PageSpec.sides (spec : PageSpec) : Option (Nat × Nat) :=
  spec.sideRatio.orElse fun _ => if spec.twoside then some (2, 3) else none

/-- A recto's left margin: the width the text block leaves, split by the sides' ratio. -/
public def PageSpec.rectoLeft (spec : PageSpec) : Length :=
  match spec.sides with
  | some (a, b) =>
    let free : Length := 2 * spec.hmargin
    if a + b == 0 then spec.hmargin else free * (a : Int) / ((a + b : Nat) : Int)
  | none => spec.hmargin

/-- The text block's left edge on the page numbered `folio`: a verso's is the recto's right margin. -/
public def PageSpec.leftMargin (spec : PageSpec) (folio : Nat) : Length :=
  if spec.twoside && folio % 2 == 0 then 2 * spec.hmargin - spec.rectoLeft else spec.rectoLeft

/-- Two-sided pages mirror: a verso's left margin and its recto's sum to the width the block
leaves, so the inner margins of facing pages match. -/
public theorem PageSpec.leftMargin_mirror (spec : PageSpec) (k : Nat) (h : spec.twoside = true) :
    spec.leftMargin (2 * k + 2) + spec.leftMargin (2 * k + 1) = 2 * spec.hmargin := by
  have he : (2 * k + 2) % 2 = 0 := by omega
  have ho : ((2 * k + 1) % 2 == 0) = false := by
    rw [show (2 * k + 1) % 2 = 1 by omega]; rfl
  simp only [PageSpec.leftMargin, h, he, ho, Bool.true_and, Bool.and_false, beq_self_eq_true,
    ite_true, ite_false, Bool.false_eq_true]
  length_omega

/-- Whether a declaration named the page's size on either axis. -/
public def PageSpec.sized (spec : PageSpec) : Bool := spec.widthSized || spec.heightSized

/-- The page with its declared text block placed on its settled height. -/
public def PageSpec.placed (spec : PageSpec) : PageSpec :=
  let (t, m) := (spec.block.scaled spec.height).place spec.height spec.vmargin spec.bottomMargin
  { spec with vmargin := t, bmargin := if m == t then none else some m, block := {} }

/-- The medium a page spec ships on: its page and the bleed on every side. -/
@[expose] public def PageSpec.medium (spec : PageSpec) : Length × Length :=
  (spec.width + 2 * spec.bleed, spec.height + 2 * spec.bleed)

public theorem PageBox.clampTo_inside (b : PageBox) (w h : Length) (hw : 0 ≤ w) (hh : 0 ≤ h) :
    0 ≤ (b.clampTo w h).x0 ∧ (b.clampTo w h).x0 ≤ w ∧ 0 ≤ (b.clampTo w h).y0 ∧
      (b.clampTo w h).y0 ≤ h ∧ 0 ≤ (b.clampTo w h).x1 ∧ (b.clampTo w h).x1 ≤ w ∧
      0 ≤ (b.clampTo w h).y1 ∧ (b.clampTo w h).y1 ≤ h := by
  simp only [PageBox.clampTo]
  exact ⟨Int.le_max_left _ _, Int.max_le.mpr ⟨hw, Int.min_le_left _ _⟩,
    Int.le_max_left _ _, Int.max_le.mpr ⟨hh, Int.min_le_left _ _⟩,
    Int.le_max_left _ _, Int.max_le.mpr ⟨hw, Int.min_le_left _ _⟩,
    Int.le_max_left _ _, Int.max_le.mpr ⟨hh, Int.min_le_left _ _⟩⟩

/-- Every box the medium ships lies inside it and encloses some area. -/
public theorem PageBox.shipped_inside (boxes : Array PageBox) (w h : Length) (hw : 0 ≤ w)
    (hh : 0 ≤ h) : ∀ b ∈ PageBox.shipped boxes w h,
      0 ≤ b.x0 ∧ b.x0 < b.x1 ∧ b.x1 ≤ w ∧ 0 ≤ b.y0 ∧ b.y0 < b.y1 ∧ b.y1 ≤ h := by
  intro b hb
  simp only [PageBox.shipped, Array.mem_filter, Array.mem_map] at hb
  obtain ⟨⟨c, _, rfl⟩, ha⟩ := hb
  have hi := PageBox.clampTo_inside c w h hw hh
  simp only [PageBox.hasArea, Bool.and_eq_true, decide_eq_true_eq] at ha
  exact ⟨hi.1, ha.1, hi.2.2.2.2.2.1, hi.2.2.1, ha.2, hi.2.2.2.2.2.2.2⟩

/-- W0442 for each declared page box the PDF cannot write as declared: one reaching past the medium
is written inside it, and one with no area there is not written. -/
public def boxDiags (spec : PageSpec) : Array Diag :=
  let (w, h) := spec.medium
  let medium := s!"[0 0 {w.toBpString} {h.toBpString}]"
  spec.boxes.filterMap fun b =>
    let c := b.clampTo w h
    let diag : Diag := Diag.of .W0442 (Diag.say .W0442 .pageBox b.kind.key) b.span
      (help := some s!"keep the box within the medium, '{medium}' in PDF points")
      (subject := some s!"pagebox:{b.kind.key}") (output := some .pdf)
      (detail := some s!"[{b.x0.toBpString} {b.y0.toBpString} {b.x1.toBpString} \
{b.y1.toBpString}] against the medium's {medium}")
    -- a box the PDF spells as the medium's edge meets it
    let near (a d : Length) : Bool := a.toBpMilli == d.toBpMilli
    if !c.hasArea then
      some diag
    else if near c.x0 b.x0 && near c.y0 b.y0 && near c.x1 b.x1 && near c.y1 b.y1 then none
    else some diag

public def texParskipOf (spec : PageSpec) : SymGlue := spec.parskip.getD texParskipDefault

public def baselineSkipOf (spec : PageSpec) : Length := leadingFor spec.fontSize spec.leading

/-- The text block of an undeclared tex page no class area sets: 26 picas, Bringhurst's
copy-fitting measure for a 10 pt text face. -/
public def articleTextBlock : Length := pt 312

/-- The text block of a markdown page: 32 picas, which keeps every default
family within 75 to 85 characters per line. -/
public def markdownTextBlock : Length := pt 384

/-- The text block an undeclared flow page takes on this surface. -/
public def Surface.textBlock : Surface → Length
  | .tex => articleTextBlock
  | .markdown | .code _ => markdownTextBlock

/-- Beamer's default slides stage, 128×96 mm. -/
@[expose] public def slidesStage43 : Length × Length := (Dim.mm 128, Dim.mm 96)
@[expose] public def slidesStage169 : Length × Length := (Dim.mm 160, Dim.mm 90)

/-- Beamer's `aspectratio` table: each stage named by its ratio, with
`beamer.cls`'s millimetre pairs. -/
@[expose] public def slidesStages : Array (String × Length × Length) :=
  #[("4:3", slidesStage43),
    ("16:9", slidesStage169),
    ("16:10", Dim.mm 160, Dim.mm 100),
    ("14:9", Dim.mm 140, Dim.mm 90),
    ("141", Dim.mm100 14850, Dim.mm 105),
    ("5:4", Dim.mm 125, Dim.mm 100),
    ("3:2", Dim.mm 135, Dim.mm 90)]

/-- The stage a ratio name selects, colon elided on both sides. -/
public def slidesStageNamed (name : String) : Option (Length × Length) :=
  let strip := fun (s : String) => String.ofList (s.toList.filter (· != ':'))
  (slidesStages.find? fun r => strip r.1 == strip name).map (·.2)

public def slidesHMargin : Length := Dim.mm 10
@[expose] public def slidesFontSize : Length := Dim.pt 11
@[expose] public def slidesVMargin : Length := 2 * leadingFor slidesFontSize

public theorem vmargin_on_rhythm :
    ({} : PageSpec).vmargin = 6 * leadingFor baseFontSize := by decide

/-- The card class's legibility floor: a 1.4 mm x-height, 0.2° at a 40 cm
reading distance (Legge & Bigelow 2011). -/
public def cardXHeightFloor : Length := Dim.mm100 140
/-- The poster class's body size: beamerposter's scale-1 normalsize, 24.88 pt. -/
public def posterFontSize : Length := Dim.pt 2488 / 100

/-- The poster class's legibility floor: the card's angular x-height bound at
a 1 m viewing distance. -/
public def posterXHeightFloor : Length := Dim.mm100 350

/-- Equality for a lookup that selects source-bearing data, stronger than screen equality. -/
public def Color.sameSource (a b : Color) : Bool :=
  a == b && a.pdfModel == b.pdfModel

/-- xcolor's screen projection of one CMYK channel: `1 - min(1, c+k)`, scaled to an HTML byte. -/
private def Color.cmykPreviewByte (v k : Decl.ColorComponent) : UInt8 :=
  let scale := v.scale * k.scale
  let used := min scale (v.num * k.scale + k.num * v.scale)
  ({ num := scale - used, scale := scale } : Decl.ColorComponent).unitByte

/-- A CMYK colour from components in thousandths, for the engine's mix arithmetic. -/
public def Color.ofCmyk (c m y k : Nat) : Color :=
  let part (v : Nat) : Decl.ColorComponent := { num := min 1000 v, scale := 1000 }
  let black := part k
  { r := cmykPreviewByte (part c) black, g := cmykPreviewByte (part m) black,
    b := cmykPreviewByte (part y) black, cmyk := some (c, m, y, k) }

/-- The colour model a colour was declared in, read off its rider. -/
public inductive Color.Model where
  | srgb
  | cmyk
  deriving Repr, BEq, DecidableEq, Inhabited

public def Color.model (c : Color) : Color.Model :=
  match c.cmyk, c.ink? with
  | some _, _ | none, some _ => .cmyk
  | none, none => .srgb

/-- Thousandths as a PDF decimal: 830 ↦ "0.83". -/
public def Color.pdfMilli (v : Nat) : String :=
  let v := min v 1000
  if v == 0 then "0" else if v == 1000 then "1"
  else
    let ds := Nat.toDigits 10 v
    let ds := List.replicate (3 - ds.length) '0' ++ ds
    "0." ++ String.ofList (ds.reverse.dropWhile (· == '0')).reverse

/-- An 8-bit channel in thousandths, rounded half up. -/
public def Color.milli (v : UInt8) : Nat := (v.toNat * 1000 + 127) / 255

/-- An HTML byte triple, keeping its exact screen bytes and xcolor's
five-decimal DeviceRGB values. -/
public def Color.ofHtml (r g b : UInt8) : Color :=
  let part (v : UInt8) : Decl.ColorComponent := { num := v.toNat, scale := 1 }
  { r := r, g := g, b := b, origin := .declared,
    pdfModel := some (.rgb (part r).xcolorRgb (part g).xcolorRgb (part b).xcolorRgb) }

/-- An RGB-range source, keeping decimal components for the PDF and projecting
each to an HTML byte. -/
public def Color.ofRgbByte (r g b : Decl.ColorComponent) : Color :=
  { r := r.rgbByte, g := g.rgbByte, b := b.rgbByte, origin := .declared,
    pdfModel := some (.rgb r.pdfRgb g.pdfRgb b.pdfRgb) }

/-- A unit-rgb source, keeping exact components for the PDF and using xcolor's
fixed-point projection on screen. -/
public def Color.ofRgbUnit (r g b : Decl.ColorComponent) : Color :=
  { r := r.unitByte, g := g.unitByte, b := b.unitByte, origin := .declared,
    pdfModel := some (.rgb r.pdfUnit g.pdfUnit b.pdfUnit) }

/-- A gray source: DeviceGray in the PDF, xcolor's byte projection on screen. -/
public def Color.ofGray (v : Decl.ColorComponent) : Color :=
  { r := v.unitByte, g := v.unitByte, b := v.unitByte, origin := .declared,
    pdfModel := some (.gray v.pdfUnit) }

/-- A source CMYK value, keeping every decimal digit for DeviceCMYK. -/
public def Color.ofCmykSource (c m y k : Decl.ColorComponent) : Color :=
  { r := cmykPreviewByte c k, g := cmykPreviewByte m k, b := cmykPreviewByte y k,
    pdfModel := some (.cmyk c.pdfUnit m.pdfUnit y.pdfUnit k.pdfUnit),
    cmyk := some (c.milli, m.milli, y.milli, k.milli), origin := .declared }

/-- A declared DeviceCMYK decimal as an exact fraction. -/
private def decimalRat? (s : String) : Option Rat :=
  (Decl.parseDecimal s).bind fun (m, scale) => if m < 0 then none else some (mkRat m scale)

/-- The CMYK a colour paints in, as unit fractions: its separation's alternate at its tint, its
DeviceCMYK as declared, else its CMYK rider; none for a colour of another model. -/
public def Color.cmykParts? (c : Color) : Option (Rat × Rat × Rat × Rat) :=
  let unit (v : Rat) : Rat := if v < 0 then 0 else if 1 < v then 1 else v
  match c.ink?, c.pdfModel, c.cmyk with
  | some (i, t), _, _ => some (unit (i.c * unit t), unit (i.m * unit t), unit (i.y * unit t),
      unit (i.k * unit t))
  | none, some (.cmyk cy m y k), some _ =>
    match decimalRat? cy, decimalRat? m, decimalRat? y, decimalRat? k with
    | some a, some b, some d, some e => some (unit a, unit b, unit d, unit e)
    | _, _, _, _ => none
  | none, _, some (cy, m, y, k) =>
    some (unit (mkRat cy 1000), unit (mkRat m 1000), unit (mkRat y 1000), unit (mkRat k 1000))
  | none, _, none => none

/-- A colour as xcolor's own arithmetic converts it to RGB, each CMYK channel `1 - min(1, v + k)`,
whatever its screen preview; any other colour as it stands. -/
public def Color.xcolorRgb (c : Color) : Color :=
  match c.cmykParts? with
  | some (cy, m, y, k) =>
    { c with r := inkPreviewByte cy k, g := inkPreviewByte m k, b := inkPreviewByte y k }
  | none => c

/-- A colour's screen preview through a CMYK output profile: its CMYK converted relatively
colorimetrically, any other colour as it stands. -/
public def Color.through (t : Icc.Transform) (c : Color) : Color :=
  let at16 (v : Rat) : Nat := (v * 65535 + 1 / 2).floor.toNat
  match c.cmykParts? with
  | some (cy, m, y, k) =>
    if t.space != "CMYK" then c else
    let (r, g, b) := t.toSrgb #[at16 cy, at16 m, at16 y, at16 k]
    { c with r, g, b }
  | none => c

/-- An exact fraction as a PDF decimal, at most nine places. -/
public def Color.pdfRat (v : Rat) : String := Dim.ratString v.num v.den

/-- An ink's colorant name as a PDF name's characters: one per byte of its UTF-8 encoding, which
the name escape writes as those bytes (ISO 32000-2 §7.3.5). -/
@[expose] public def Ink.pdfName (i : Ink) : String :=
  String.ofList (i.name.toUTF8.toList.map fun b => Char.ofNat b.toNat)

/-- The `/ColorSpace` resource key an ink's separation is named by on every page. -/
@[expose] public def Ink.resKey (i : Ink) : String := "Ink." ++ i.pdfName

/-- The `All` colorant at full tint on every plate (§8.6.6.4): the colour of printer's marks. -/
@[expose] public def Ink.all : Ink := { name := "All", c := 1, m := 1, y := 1, k := 1 }

/-- The xcolor name a boundary standalone gives an ink: its colorant name's bytes in hex. -/
public def Ink.xcolorName (i : Ink) : String :=
  i.name.toUTF8.toList.foldl (fun s b => s ++ Hex.byte false b) "ink@"

/-- Components in 0–1 at three decimals, finer than 8-bit input. -/
@[expose] public def Color.pdfComponents (c : Color) : String :=
  pdfMilli (milli c.r) ++ " " ++ pdfMilli (milli c.g) ++ " " ++ pdfMilli (milli c.b)

/-- The PDF fill-colour operation for this colour, in its source model's device operator. -/
public def Color.pdfFill (c : Color) : String :=
  match c.pdfModel with
  | some (.rgb r g b) => s!"{r} {g} {b} rg"
  | some (.gray v) => s!"{v} g"
  | some (.cmyk cy m y k) => s!"{cy} {m} {y} {k} k"
  | some (.separation i t) => s!"/{PdfLex.escapeName i.resKey} cs {pdfRat t} scn"
  | none => match c.cmyk with
    | some (cy, m, y, k) =>
      s!"{pdfMilli cy} {pdfMilli m} {pdfMilli y} {pdfMilli k} k"
    | none => s!"{c.pdfComponents} rg"

/-- The stroke-colour twin of `pdfFill`. -/
public def Color.pdfStroke (c : Color) : String :=
  match c.pdfModel with
  | some (.rgb r g b) => s!"{r} {g} {b} RG"
  | some (.gray v) => s!"{v} G"
  | some (.cmyk cy m y k) => s!"{cy} {m} {y} {k} K"
  | some (.separation i t) => s!"/{PdfLex.escapeName i.resKey} CS {pdfRat t} SCN"
  | none => match c.cmyk with
    | some (cy, m, y, k) =>
      s!"{pdfMilli cy} {pdfMilli m} {pdfMilli y} {pdfMilli k} K"
    | none => s!"{c.pdfComponents} RG"

public theorem Color.cmyk_components_kept (c m y k : Nat) :
    (Color.ofCmyk c m y k).cmyk = some (c, m, y, k) ∧
    (Color.ofCmyk c m y k).pdfFill
      = s!"{pdfMilli c} {pdfMilli m} {pdfMilli y} {pdfMilli k} k" := by
  exact ⟨rfl, rfl⟩

public theorem Color.pdfFill_srgb (c : Color) (hm : c.pdfModel = none) (hc : c.cmyk = none) :
    c.pdfFill = s!"{c.pdfComponents} rg" := by
  simp [Color.pdfFill, hm, hc]

/-- The reader of `pdfMilli`'s output: `"1"` ↦ 1000, `"0.d…"` ↦ the digits
padded to three, anything else 0. -/
public def Color.decodeMilli (s : String) : Nat :=
  match s.toList with
  | '0' :: '.' :: ds =>
    (ds ++ List.replicate (3 - ds.length) '0').foldl
      (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0
  | cs => if cs == ['1'] then 1000 else 0

public theorem Color.pdfMilli_decode : ∀ v < 1001, decodeMilli (pdfMilli v) = v := by
  have digitZero (n : Nat) : (n.digitChar == '0') = (n == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Nat.digitChar_eq_zero]
  intro v hv
  have hmin : min v 1000 = v := Nat.min_eq_left (by omega)
  by_cases hz : v = 0
  · subst v
    rfl
  by_cases hunit : v = 1000
  · subst v
    rfl
  have hn : v < 1000 := by omega
  simp only [pdfMilli, hmin, beq_iff_eq, hz, hunit, ↓reduceIte]
  unfold decodeMilli
  rw [String.toList_append, String.toList_ofList]
  by_cases hten : v < 10
  · rw [Nat.toDigits_of_lt_base hten]
    simp [hz, Nat.toNat_digitChar_of_lt_ten hten]
  · rw [Nat.toDigits_of_base_le (by decide) (by omega : 10 ≤ v)]
    by_cases hhundred : v < 100
    · have hq : v / 10 < 10 := by omega
      have hq0 : v / 10 ≠ 0 := by omega
      have hqz : (v / 10 == 0) = false := beq_eq_false_iff_ne.mpr hq0
      have hr : v % 10 < 10 := by omega
      rw [Nat.toDigits_of_lt_base hq]
      by_cases hlast : v % 10 = 0
      · simp [List.dropWhile, digitZero, hqz, hlast,
          Nat.toNat_digitChar_of_lt_ten hq]
        omega
      · simp [hlast, Nat.toNat_digitChar_sub_48_of_lt_ten hq,
          Nat.toNat_digitChar_sub_48_of_lt_ten hr]
        omega
    · have hq : v / 10 / 10 < 10 := by omega
      have hq0 : v / 10 / 10 ≠ 0 := by omega
      have hqz : (v / 10 / 10 == 0) = false := beq_eq_false_iff_ne.mpr hq0
      have hm : v / 10 % 10 < 10 := by omega
      have hr : v % 10 < 10 := by omega
      rw [Nat.toDigits_of_base_le (by decide) (by omega : 10 ≤ v / 10)]
      rw [Nat.toDigits_of_lt_base hq]
      by_cases hlast : v % 10 = 0
      · by_cases hmiddle : v / 10 % 10 = 0
        · simp [List.dropWhile, digitZero, hqz, hlast, hmiddle,
            Nat.toNat_digitChar_of_lt_ten hq]
          omega
        · have hmz : (v / 10 % 10 == 0) = false := beq_eq_false_iff_ne.mpr hmiddle
          simp [List.dropWhile, digitZero, hlast, hmz,
            Nat.toNat_digitChar_sub_48_of_lt_ten hq,
            Nat.toNat_digitChar_sub_48_of_lt_ten hm]
          omega
      · simp [hlast, Nat.toNat_digitChar_sub_48_of_lt_ten hq,
          Nat.toNat_digitChar_sub_48_of_lt_ten hm,
          Nat.toNat_digitChar_sub_48_of_lt_ten hr]
        omega

public theorem Color.milli_inj (a b : UInt8) (h : milli a = milli b) : a = b := by
  simp only [milli] at h
  exact UInt8.toNat_inj.mp (by omega)

public theorem Color.milli_lt (a : UInt8) : milli a < 1001 := by
  have := a.toNat_lt
  simp only [milli]
  omega

/-- The colour printer's marks paint in: the `All` colorant, DeviceCMYK
1,1,1,1, when the document declares print colours, else black ink. -/
public def Color.registration (printModel : Bool) : Color :=
  if printModel then Color.ofInk Ink.all 1 else Color.blackInk

/-- Replace-on-redeclare: a later declaration of a key overrides, keeping one entry per key. -/
public abbrev redeclare {κ α : Type} [BEq κ] (xs : Array (κ × α)) (k : κ) (v : α) :
    Array (κ × α) :=
  (xs.filter (·.1 != k)).push (k, v)

/-- Named lengths declared by `\tokens`, in declaration order. -/
public structure Tokens where
  entries : Array (String × SymGlue) := #[]
  deriving Repr, BEq, Inhabited

public def Tokens.find? (t : Tokens) (name : String) : Option SymGlue :=
  (t.entries.find? (·.1 == name)).map (·.2)

/-- A resolved value beside the declaration it was resolved from. -/
public structure Sourced (α : Type) where
  value : α
  token : Option String
  deriving Repr, BEq, Inhabited

@[expose] public def Sourced.bare {α : Type} (v : α) : Sourced α := { value := v, token := none }

/-- A token lookup whose answer carries the name it was asked for, for a value a backend shows. -/
public def Tokens.findSourced? (t : Tokens) (name : String) : Option (Sourced SymGlue) :=
  (t.find? name).map fun g => { value := g, token := some name }

public theorem findSourced?_names (t : Tokens) (name : String) :
    (t.findSourced? name).map (·.value) = t.find? name ∧
      ∀ s ∈ t.findSourced? name, s.token = some name := by
  constructor
  · cases h : t.find? name <;> simp [Tokens.findSourced?, h]
  · intro s hs
    cases h : t.find? name <;> simp [Tokens.findSourced?, h] at hs
    exact hs ▸ rfl

/-- The tokens without a declaration of `key`. -/
public def Tokens.erase (t : Tokens) (key : String) : Tokens :=
  { entries := t.entries.filter (·.1 != key) }

/-- A later declaration of a name overrides, keeping one entry per name. -/
public def Tokens.declare (t : Tokens) (key : String) (g : SymGlue) : Tokens :=
  { entries := redeclare t.entries key g }

public theorem declare_find_eq {κ α : Type} [BEq κ] [LawfulBEq κ] (xs : Array (κ × α)) (k : κ) (v : α) :
    (redeclare xs k v).find? (·.1 == k) = some (k, v) := by
  have hnone : (xs.filter (·.1 != k)).find? (·.1 == k) = none := by
    rw [Array.find?_eq_none]
    intro x hx
    have hne := (Array.mem_filter.mp hx).2
    simpa using hne
  rw [Array.find?_push, hnone]
  simp

private theorem declare_collapse {κ α : Type} [BEq κ] [LawfulBEq κ] (xs : Array (κ × α)) (k : κ)
    (v v' : α) : redeclare (redeclare xs k v) k v' = redeclare xs k v' := by
  unfold redeclare
  rw [Array.filter_push]
  simp

public theorem declare_keeps {κ α : Type} [BEq κ] [LawfulBEq κ] (xs : Array (κ × α)) (k k' : κ) (v : α)
    (h : k' ≠ k) :
    (redeclare xs k v).find? (·.1 == k') = xs.find? (·.1 == k') := by
  rw [Array.find?_push, Array.find?_filter]
  have hpred : (fun a : κ × α => decide ((a.fst != k) = true ∧ (a.fst == k') = true))
      = (fun a : κ × α => a.fst == k') := by
    funext x
    by_cases hx : (x.1 == k') = true
    · have hxe : x.1 = k' := by simpa using hx
      simp [hxe, h]
    · simp [hx]
  rw [hpred]
  have hkk : (k == k') = false := by
    simpa using fun hk => h hk.symm
  simp [hkk]

public theorem Tokens.declare_last_wins (t : Tokens) (k : String) (g : SymGlue) :
    (t.declare k g).find? k = some g := by
  unfold declare find?
  rw [declare_find_eq]
  rfl

public theorem Tokens.declare_overwrite (t : Tokens) (k : String) (g g' : SymGlue) :
    (t.declare k g).declare k g' = t.declare k g' := by
  simp only [declare, declare_collapse]

public theorem Tokens.declare_keeps_others (t : Tokens) (k k' : String) (g : SymGlue)
    (h : k' ≠ k) : (t.declare k g).find? k' = t.find? k' := by
  unfold declare find?
  rw [declare_keeps _ _ _ _ h]

-- Table rule weights and paddings: booktabs.dtx defaults, resolved in the preamble's font.

/-- `\toprule`/`\bottomrule` weight: booktabs `\heavyrulewidth` (.08em). -/
public def heavyRuleWidth : Dim.SymLength := { em := 80 }
/-- `\midrule` weight: booktabs `\lightrulewidth` (.05em). -/
public def lightRuleWidth : Dim.SymLength := { em := 50 }
/-- `\cmidrule` weight: booktabs `\cmidrulewidth` (.03em). -/
public def cmidRuleWidth : Dim.SymLength := { em := 30 }
/-- Space under a rule, above the content it heads: booktabs
`\belowrulesep` (.65ex). -/
public def belowRuleSep : Dim.SymLength := { ex := 650 }
/-- Space over a rule, under the content above it: booktabs `\aboverulesep`
(.4ex). -/
public def aboveRuleSep : Dim.SymLength := { ex := 400 }
/-- Space over a `\toprule`: zero, as booktabs' `\abovetopsep`. -/
public def aboveTopSep : Dim.SymLength := {}
/-- Space under a `\bottomrule`: zero, as booktabs' `\belowbottomsep`. -/
public def belowBottomSep : Dim.SymLength := {}
/-- Default end-trim of a trimmed `\cmidrule`: booktabs `\cmidrulekern`
(.5em). -/
public def cmidRuleKern : Dim.SymLength := { em := 500 }
/-- `\addlinespace` default: booktabs `\defaultaddspace` (.5em). -/
public def defaultAddSpace : Dim.SymLength := { em := 500 }
/-- Half the gap between two table columns: LaTeX's `\tabcolsep`, 6pt. -/
public def tabColSep : Dim.SymLength := { fixed := Dim.pt 6 }
/-- The gap between text columns: LaTeX's `\columnsep`, 10pt. -/
public def columnSep : Dim.SymLength := { fixed := Dim.pt 10 }
/-- The gap between two stacked full rules: LaTeX's `\doublerulesep`, 2pt. -/
public def doubleRuleSep : Dim.SymLength := { fixed := Dim.pt 2 }

/-- The lengths a formal table reads, under their LaTeX names, each with its undeclared default. -/
public def tableLengths : List (String × Dim.SymLength) :=
  [("tabcolsep", tabColSep), ("doublerulesep", doubleRuleSep),
   ("heavyrulewidth", heavyRuleWidth), ("lightrulewidth", lightRuleWidth),
   ("cmidrulewidth", cmidRuleWidth), ("cmidrulekern", cmidRuleKern),
   ("aboverulesep", aboveRuleSep), ("belowrulesep", belowRuleSep),
   ("abovetopsep", aboveTopSep), ("belowbottomsep", belowBottomSep)]

/-- A table length's default; zero for a name `tableLengths` lacks. -/
public def tableLengthDefault (name : String) : Dim.SymLength :=
  (tableLengths.lookup name).getD {}

/-- The kernel values of latex.ltx's `\smallskipamount`, `\medskipamount` and `\bigskipamount`. -/
public def kernelSkip : String → Option SymGlue
  | "smallskipamount" =>
    some { width := .ofLength (Dim.pt 3), stretch := .ofLength (Dim.pt 1), shrink := .ofLength (Dim.pt 1) }
  | "medskipamount" =>
    some { width := .ofLength (Dim.pt 6), stretch := .ofLength (Dim.pt 2), shrink := .ofLength (Dim.pt 2) }
  | "bigskipamount" =>
    some { width := .ofLength (Dim.pt 12), stretch := .ofLength (Dim.pt 4), shrink := .ofLength (Dim.pt 4) }
  | "fboxsep" => some { width := .ofLength (Dim.pt 3) }
  | "fboxrule" => some { width := .ofLength (Dim.pt 2 / 5) }
  | _ => none

/-- A skip register's value: the document's setting where declared, else the kernel's. -/
public def skipAmount (tokens : Tokens) (name : String) : SymGlue :=
  (tokens.find? name).getD ((kernelSkip name).getD {})

public theorem rule_weights_ordered :
    0 < cmidRuleWidth.em ∧ cmidRuleWidth.em < lightRuleWidth.em ∧
    lightRuleWidth.em < heavyRuleWidth.em := by decide

public theorem rule_seps_ordered : 0 < aboveRuleSep.ex ∧ aboveRuleSep.ex < belowRuleSep.ex := by
  decide

/-- Gap between a float's object and its caption, on the object side only: one
rhythm quantum of the governing size. -/
@[expose] public def captionSepDefault (size : Length) : SymGlue :=
  { width := { fixed := rhythmQuantum size } }
/-- Gap between a float and the text around it: one full rhythm unit of the governing size. -/
@[expose] public def floatSepDefault (size : Length) : SymGlue :=
  { width := { fixed := 2 * rhythmQuantum size } }

/-- Gap between the last body line and the footnote region: `\skip\footins`,
quantized to one leading. -/
public def footinsDefault (size : Length) : SymGlue :=
  { width := { fixed := 2 * rhythmQuantum size } }

public theorem footins_within_glue :
    (footinsDefault baseFontSize).width.fixed = 2 * rhythmQuantum baseFontSize ∧
    Dim.pt 7 ≤ (footinsDefault baseFontSize).width.fixed ∧
    (footinsDefault baseFontSize).width.fixed ≤ Dim.pt 13 := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- The space a trivlist environment opens above and below: LaTeX's top-level
`\topsep`, quantized to one rhythm quantum. -/
@[expose] public def trivlistSkipDefault (size : Length) : SymGlue :=
  { width := { fixed := rhythmQuantum size }
    stretch := { fixed := size / 5 }
    shrink := { fixed := size * 2 / 5 } }

public def trivlistSkipName : String := "topsep"

/-- A trivlist's space: the document's token where declared, else the rhythm
default at the governing size. -/
public def trivlistSkip (tokens : Tokens) (size : Length) : SymGlue :=
  (tokens.find? trivlistSkipName).getD (trivlistSkipDefault size)

/-- natbib's hanging indent for an author-year reference list, `\bibhang`. -/
public def bibHangName : String := "bibhang"

public def bibHang (tokens : Tokens) : SymGlue :=
  (tokens.find? bibHangName).getD { width := { em := 1000 } }

/-- natbib's gap between reference-list entries, `\bibsep`. -/
public def bibSepName : String := "bibsep"

public def bibSepDefault (size : Length) : SymGlue :=
  let g (w s h : Length) : SymGlue :=
    { width := { fixed := w }, stretch := { fixed := s }, shrink := { fixed := h } }
  if size == Dim.pt 10 then g (Dim.pt 8) (Dim.pt 4) (Dim.pt 2)
  else if size == Dim.pt 11 then g (Dim.pt 9) (Dim.pt 4) (Dim.pt 2)
  else if size == Dim.pt 12 then g (Dim.pt 10) (Dim.pt 5) (Dim.pt 2)
  else g (size * 4 / 5) (size * 2 / 5) (size / 5)

/-- The gap between reference-list entries: the document's `\bibsep` where
declared, else natbib's default at the governing size. -/
public def bibSep (tokens : Tokens) (size : Length) : SymGlue :=
  (tokens.find? bibSepName).getD (bibSepDefault size)

/-- The role a trivlist environment's body rides in, marking the `\topsep` it opens. -/
public def trivlistRole : String := "trivlist-env"

/-- The role a list or quote rides in when it opens inside a paragraph, where
LaTeX adds no `\partopsep`. -/
public def inParagraphRole : String := "in-paragraph"

/-- The role `\vspace*` rides in: an empty marker that keeps the space after it at a page's top. -/
public def pageAnchorRole : String := "page-anchor"

/-- The role `\nointerlineskip` rides in: an empty marker after which the next
box takes no interline glue. -/
public def noInterlineRole : String := "no-interline"

/-- The role a primitive `\vskip` rides in: an empty marker after its skip,
which a following `\addvspace` combines with. -/
public def primitiveSkipRole : String := "primitive vskip"


/-- The role a frame's `[squeeze]` rides in: an empty marker opening the body,
for beamer's cramped list spacing. -/
public def squeezeRole : String := "frame squeeze"

/-- The mark opening a frame beamer's `[noframenumbering]` leaves out of the frame count. -/
public def unnumberedRole : String := "frame unnumbered"

/-- The mark opening a frame beamer's `[plain]` sets without its footline. -/
public def plainRole : String := "frame plain"

/-- The squeezed list spacing as the overflow ladder sets it on an overfull
frame, for the web deck alone. -/
public def squeezeFitRole : String := "frame squeeze fit"

public def fitMarkPrefix : String := "frame fit "

/-- The overflow ladder's first-pass mark: the page stands the frame overfull
to measure its overrun. -/
public def fitMeasureRole : String := fitMarkPrefix ++ "measure"

/-- The overflow ladder's decision that overlay step `step` stands overfull
within the gap above its footline. -/
public def fitOverhangRole (step : Nat) : String := fitMarkPrefix ++ s!"overhang {step}"

/-- The overflow ladder's decision that overlay step `step` continues on the next page. -/
public def fitContinuesRole (step : Nat) : String := fitMarkPrefix ++ s!"continues {step}"

/-- Whether a role is one of the overflow ladder's marks. -/
@[expose] public def fitMarkRole (n : String) : Bool := n.startsWith fitMarkPrefix

/-- A counter's numeral style: LaTeX's `\arabic`, `\alph`, `\Alph`, `\roman` or `\Roman`, or
`\pagenumbering{gobble}`'s, which sets none. -/
public inductive NumStyle where
  | arabic
  | alph
  | uAlph
  | roman
  | uRoman
  | gobble
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The numeral style a LaTeX style command names. -/
public def NumStyle.ofName? : String → Option NumStyle
  | "arabic" => some .arabic
  | "alph" => some .alph
  | "Alph" => some .uAlph
  | "roman" => some .roman
  | "Roman" => some .uRoman
  | _ => none

/-- The numeral style `\pagenumbering` names, `gobble` among them. -/
public def NumStyle.ofPageName? (n : String) : Option NumStyle :=
  if n == "gobble" then some .gobble else NumStyle.ofName? n

/-- A declaration at a page boundary, independent of the page's ground and vertical distribution:
a folio to count from, an empty running style, and the folio's numeral style. -/
public structure PageOpening where
  folio : Option Nat := none
  empty : Bool := false
  style : Option NumStyle := none
  deriving Repr, BEq, Inhabited

/-- The logical folio, its numeral style and the running style of the page being built. -/
public structure PageState where
  folio : Nat := 1
  furniture : Bool := true
  style : NumStyle := .arabic
  /-- Whether the page is set in the plain style, as a chapter's opening page is. -/
  plain : Bool := false
  deriving Repr, BEq, Inhabited

/-- Apply only the opening's declarations; a reset keeps an empty style that has not yet shipped. -/
public def PageState.applyOpening (s : PageState) (opening : PageOpening) : PageState :=
  { folio := opening.folio.getD s.folio
    furniture := s.furniture && !opening.empty
    style := opening.style.getD s.style
    plain := s.plain }

/-- Ship one physical page: advance its logical folio and restore the ordinary
running style, as `\@outputpage` does. -/
public def PageState.ship (s : PageState) : PageState :=
  { folio := s.folio + 1, furniture := true, style := s.style }

public theorem PageState.opening_contract (s : PageState) (opening : PageOpening) :
    (s.applyOpening opening).folio = opening.folio.getD s.folio ∧
      (s.applyOpening opening).furniture = (s.furniture && !opening.empty) ∧
      (s.applyOpening opening).style = opening.style.getD s.style :=
  ⟨rfl, rfl, rfl⟩

public theorem PageState.ship_contract (s : PageState) :
    s.ship.folio = s.folio + 1 ∧ s.ship.furniture = true ∧ s.ship.style = s.style := ⟨rfl, rfl, rfl⟩

/-- Reserved roles for article titlepage's two boundary declarations,
unspellable as control words. -/
public def titlePageBeginRole : String := "titlepage begin"
public def titlePageEndRole : String := "titlepage end"

/-- The reserved role `\pagenumbering{style}` declares: the folio counts from one in its numeral
style from the page it stands on. -/
public def pageNumberingRole (style : NumStyle) : String :=
  let name := match style with
    | .arabic => "arabic"
    | .alph => "alph"
    | .uAlph => "Alph"
    | .roman => "roman"
    | .uRoman => "Roman"
    | .gobble => "gobble"
  "pagenumbering " ++ name

/-- The page opening a titlepage boundary or a page numbering role declares. -/
public def pageOpeningOfRole? (n : String) : Option PageOpening :=
  if n == titlePageBeginRole then some { folio := some 1, empty := true }
  else if n == titlePageEndRole then some { folio := some 1 }
  else if n.startsWith "pagenumbering " then
    (NumStyle.ofPageName? (n.drop "pagenumbering ".length).toString).map fun s =>
      { folio := some 1, style := some s }
  else none

public theorem titlepage_empty_exact (s : PageState) :
    (s.applyOpening { folio := some 1, empty := true }).applyOpening
        { folio := some 1 } = { folio := 1, furniture := false, style := s.style, plain := s.plain } := by
  simp [PageState.applyOpening]

/-- The role an empty marker rides in after an environment whose paragraph goes on past it, as
`\@endpe` sets the text after it with no first-line indent. -/
public def parContinuesRole : String := "par continues"

/-- The role an empty marker rides in before an overlay step a quotation's or a verse's paragraph
runs on into, which stands with no paragraph gap above it. -/
public def parRunsOnRole : String := "par runs on"

/-- The role an empty marker rides in where a float's center closed after its caption, which the
float sets after the caption (latex.ltx `\endtrivlist`). -/
public def captionCloseRole : String := "caption close"

/-- The role an empty marker rides in where a float's caption below its object stood, the skips
after it set below the caption. -/
public def captionAtRole : String := "caption at"

/-- The role an empty marker rides in where a trivlist environment's next `\item` opens, which
spends the `\itemsep` in force (latex.ltx `\@item`). -/
public def trivItemRole : String := "trivlist item"

/-- The reserved role `\cleardoublepage` declares: a two-sided page's next folio falls odd, a
blank verso before it where needed. -/
public def rectoRole : String := "page recto"

/-- The reserved role `\thispagestyle{plain}` declares, as a chapter's opening and `\maketitle` do:
the page carries no running head and its folio in the foot. -/
public def plainPageRole : String := "page plain"

/-- The reserved role `\thispagestyle` with a running style declares: the page keeps its fields. -/
public def styledPageRole : String := "page styled"

/-- The reserved role a hand-written `\markboth` or `\markright` stands in, by its index among the
document's marks. -/
public def markRole (k : Nat) : String := s!"page mark {k}"

public def markRole? (n : String) : Option Nat :=
  if n.startsWith "page mark " then (n.drop "page mark ".length).toString.toNat? else none

/-- The inline roles `\leftmark` and `\rightmark` stand in, which a running field reads per page. -/
public def leftMarkRole : String := "page leftmark"
public def rightMarkRole : String := "page rightmark"

/-- The engine roles that mark a fact of the page model and carry no content. -/
@[expose] public def pageMarkerRole (n : String) : Bool :=
  n == pageAnchorRole || n == noInterlineRole || n == primitiveSkipRole ||
    (pageOpeningOfRole? n).isSome || n == squeezeRole || n == squeezeFitRole || fitMarkRole n ||
    n == parContinuesRole || n == parRunsOnRole || n == unnumberedRole || n == plainRole ||
    n == captionCloseRole || n == rectoRole || n == trivItemRole || n == captionAtRole ||
    n == plainPageRole || n == styledPageRole || (markRole? n).isSome

public theorem pageOpening_marker_exact (n : String) (opening : PageOpening)
    (h : pageOpeningOfRole? n = some opening) : pageMarkerRole n = true := by
  simp [pageMarkerRole, h]

/-- The inline role a description item's label rides in, first in the item's first paragraph. -/
public def descLabelRole : String := "description-label"

/-- The inline role url.sty's low tilde rides in, which a text reading spells as the address's `~`. -/
public def urlTildeRole : String := "url-tilde"

/-- The inline role an `\item[label]` of an itemize or enumerate rides in, first in the item's first
paragraph, which sets in the place of the level's marker. -/
public def itemLabelRole : String := "item-label"

/-- The inline role a run-in heading rides in at its paragraph's start in a quotation or a verse,
whose first line it opens with no indent, as `\@afterindentfalse` sets it. -/
public def runInHeadRole : String := "run-in-head"

/-- The inline role a starred `\nameref`'s title rides in, set without its link. -/
public def titleTextRole : String := "nameref-text"

public theorem trivlist_between :
    Dim.pt 4 ≤ (trivlistSkipDefault (Dim.pt 10)).width.fixed ∧
      (trivlistSkipDefault (Dim.pt 10)).width.fixed ≤ Dim.pt 10 ∧
    Dim.pt 4 ≤ (trivlistSkipDefault (Dim.pt 1095 / 100)).width.fixed ∧
      (trivlistSkipDefault (Dim.pt 1095 / 100)).width.fixed ≤ Dim.pt 12 ∧
    Dim.pt 4 ≤ (trivlistSkipDefault (Dim.pt 12)).width.fixed ∧
      (trivlistSkipDefault (Dim.pt 12)).width.fixed ≤ Dim.pt 14 := by
  decide

/-- Where a class's list spacing comes from: the standard classes' size file,
beamer's list family, or the web's. -/
public inductive ListLineage where
  | sizeFile
  | beamer
  | web
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One list level's vertical parameters, LaTeX's `\@list⟨n⟩`; `partopsep` is
`none` where the value in force stands. -/
public structure ListSkips where
  topsep : SymGlue
  itemsep : SymGlue
  parsep : SymGlue
  partopsep : Option SymGlue
  deriving Repr, BEq

/-- Glue spelled in hundredths of a point: natural, stretch, shrink. -/
private def ptsGlue (w st sh : Int) : SymGlue :=
  { width := { fixed := Dim.pt w / 100 }, stretch := { fixed := Dim.pt st / 100 },
    shrink := { fixed := Dim.pt sh / 100 } }

/-- The sourced list levels per lineage, size file and level one to three; a
deeper level keeps the third's values. -/
private def listSkipsTable : ListLineage → Nat → Nat → ListSkips
  -- size10.clo:216-233
  | .sizeFile, 10, 1 => ⟨ptsGlue 800 200 400, ptsGlue 400 200 100, ptsGlue 400 200 100, none⟩
  | .sizeFile, 10, 2 => ⟨ptsGlue 400 200 100, ptsGlue 200 100 100, ptsGlue 200 100 100, none⟩
  | .sizeFile, 10, _ =>
    ⟨ptsGlue 200 100 100, ptsGlue 200 100 100, {}, some (ptsGlue 100 0 100)⟩
  -- size11.clo:216-233
  | .sizeFile, 11, 1 => ⟨ptsGlue 900 300 500, ptsGlue 450 200 100, ptsGlue 450 200 100, none⟩
  | .sizeFile, 11, 2 => ⟨ptsGlue 450 200 100, ptsGlue 200 100 100, ptsGlue 200 100 100, none⟩
  | .sizeFile, 11, _ =>
    ⟨ptsGlue 200 100 100, ptsGlue 200 100 100, {}, some (ptsGlue 100 0 100)⟩
  -- size12.clo:216-233
  | .sizeFile, _, 1 => ⟨ptsGlue 1000 400 600, ptsGlue 500 250 100, ptsGlue 500 250 100, none⟩
  | .sizeFile, _, 2 => ⟨ptsGlue 500 250 100, ptsGlue 250 100 100, ptsGlue 250 100 100, none⟩
  | .sizeFile, _, _ =>
    ⟨ptsGlue 250 100 100, ptsGlue 250 100 100, {}, some (ptsGlue 100 0 100)⟩
  -- beamerbaselocalstructure.sty:152-163
  | .beamer, _, 1 => ⟨ptsGlue 300 200 250, ptsGlue 300 200 300, {}, none⟩
  | .beamer, _, _ => ⟨ptsGlue 200 100 200, ptsGlue 0 100 0, ptsGlue 0 100 0, none⟩
  | .web, _, _ => ⟨{}, {}, {}, none⟩

/-- The size file a body size reads: `10pt`, `11pt` or `12pt`, the nearest for any other size. -/
private def sizeFileOf (size : Length) : Nat :=
  if size < Dim.pt 21 / 2 then 10 else if size < Dim.pt 23 / 2 then 11 else 12

/-- A list level's spacing: the lineage's sourced values at the body size and
nesting level, `none` for the web's. -/
public def listSkips (l : ListLineage) (size : Length) (level : Nat) : Option ListSkips :=
  let lv := min (max level 1) 3
  match l with
  | .web => none
  | .beamer => some (listSkipsTable .beamer 0 lv)
  | .sizeFile =>
    let f := sizeFileOf size
    let s := listSkipsTable .sizeFile f lv
    let base := Dim.pt f
    if size == base then some s
    else some { topsep := s.topsep.scaleRatio size base
                itemsep := s.itemsep.scaleRatio size base
                parsep := s.parsep.scaleRatio size base
                partopsep := s.partopsep.map (·.scaleRatio size base) }

/-- The `\@listi` a size step's command redefines in the standard size files: its `\topsep`, and its
`\parsep` that `\itemsep` repeats (size1x.clo `\small`, `\footnotesize`). -/
private def stepListITable : Nat → String → Option (SymGlue × SymGlue)
  | 10, "small" => some (ptsGlue 400 200 200, ptsGlue 200 100 100)
  | 10, "footnotesize" => some (ptsGlue 300 100 100, ptsGlue 200 100 100)
  | 11, "small" => some (ptsGlue 600 200 200, ptsGlue 300 200 100)
  | 11, "footnotesize" => some (ptsGlue 400 200 200, ptsGlue 200 100 100)
  | 12, "small" => some (ptsGlue 900 300 500, ptsGlue 450 200 100)
  | 12, "footnotesize" => some (ptsGlue 600 200 200, ptsGlue 300 200 100)
  | _, _ => none

public theorem listSkips_web_exact (size : Length) (level : Nat) :
    listSkips .web size level = none := by
  simp only [listSkips]

/-- The class options a display's size file is read from, each with the
`\normalsize` its file sets. -/
private def displayOptions : List (Nat × Length) :=
  [(8, Dim.pt 8), (9, Dim.pt 9), (10, Dim.pt 10), (11, Dim.pt 1095 / 100), (12, Dim.pt 12),
   (14, Dim.pt 144 / 10), (17, Dim.pt 1728 / 100), (20, Dim.pt 2074 / 100)]

/-- The top-level `\topsep` each beamer class option's size file leaves in force. -/
private def beamerTopsepTable : List (Nat × SymGlue) :=
  [(8, ptsGlue 600 200 300), (9, ptsGlue 600 200 300), (10, ptsGlue 800 200 400),
   (11, ptsGlue 900 300 500), (12, ptsGlue 1000 400 600), (14, ptsGlue 1200 500 700),
   (17, ptsGlue 1400 600 800), (20, ptsGlue 1600 700 900)]

/-- The class option a beamer body declares, else beamer's default `11pt`. -/
private def beamerOptionOf (size : Length) : Nat :=
  ((displayOptions.find? fun o => Dim.pt o.1 == size || o.2 == size).map (·.1)).getD 11

/-- The `\topsep` in force at a list depth: outside every list the document's where declared, else
the size file's `\@listI` or beamer's option's; inside, the level's; the web's `trivlistSkip`. -/
public def trivlistSkipFor (l : ListLineage) (tokens : Tokens) (size : Length) (depth : Nat) :
    SymGlue :=
  match l with
  | .beamer =>
    let top := (beamerTopsepTable.lookup (beamerOptionOf size)).getD (trivlistSkipDefault size)
    if depth == 0 then (tokens.find? trivlistSkipName).getD top
    else ((listSkips .beamer size depth).map (·.topsep)).getD top
  | .sizeFile =>
    let level :=
      ((listSkips .sizeFile size (max depth 1)).map (·.topsep)).getD (trivlistSkipDefault size)
    if depth == 0 then (tokens.find? trivlistSkipName).getD level else level
  | .web => trivlistSkip tokens size

/-- A float's space against the text at its list depth, with whether the
paragraph gap stands on top of it. -/
public def floatSpaceFor (l : ListLineage) (tokens : Tokens) (size : Length) (depth : Nat) :
    SymGlue × Bool :=
  match tokens.find? "floatsep", l with
  | some g, _ => (g, false)
  | none, .beamer => (trivlistSkipFor l tokens size depth, true)
  | none, .sizeFile | none, .web => (floatSepDefault size, false)

/-- The class's `\partopsep` where no list level sets its own. -/
public def partopsepDefault (l : ListLineage) (size : Length) : SymGlue :=
  match l with
  | .sizeFile =>
    let f := sizeFileOf size
    let g := match f with
      | 10 => ptsGlue 200 100 100
      | 11 => ptsGlue 300 100 100
      | _ => ptsGlue 300 200 200
    if size == Dim.pt f then g else g.scaleRatio size (Dim.pt f)
  | .beamer | .web => {}

/-- A list's `\partopsep`, which `\@trivlist` adds to `\topsep` where the list
opens in vertical mode. -/
public def partopsepFor (l : ListLineage) (size : Length) (level : Nat) (tokens : Tokens) : SymGlue :=
  match (listSkips l size level).bind (·.partopsep) with
  | some g => g
  | none => (tokens.find? "partopsep").getD (partopsepDefault l size)

/-- A list's declared left margin (enumitem's `leftmargin`): a length, or its widest label's width
and `\labelsep` (`leftmargin=*`), that label's text where the list numbers its items, none where
its marker is the label. -/
public inductive ListMargin where
  | len (g : SymGlue)
  | widest (sample : Option String)
  deriving Repr, BEq, Inhabited, Hashable

/-- A list's declared spacing over its level's: enumitem's vertical keys, each `none` where the
level's value stands, and its left margin, which no list inside it keeps. -/
public structure ListSet where
  topsep : Option SymGlue := none
  partopsep : Option SymGlue := none
  itemsep : Option SymGlue := none
  parsep : Option SymGlue := none
  margin : Option ListMargin := none
  deriving Repr, BEq, Inhabited, Hashable

/-- The keys a list's spacing declares, as a style and a list's options spell them. -/
public def listSetKeys : List String := ["topsep", "partopsep", "itemsep", "parsep"]

/-- A spacing with one key declared, or undeclared at `none`; any other key leaves it as it is. -/
public def ListSet.put (s : ListSet) (key : String) (g : Option SymGlue) : ListSet :=
  match key with
  | "topsep" => { s with topsep := g }
  | "partopsep" => { s with partopsep := g }
  | "itemsep" => { s with itemsep := g }
  | "parsep" => { s with parsep := g }
  | _ => s

/-- `top`'s declared values over `s`'s, as a later scope's over an earlier one. -/
public def ListSet.over (s top : ListSet) : ListSet :=
  { topsep := top.topsep <|> s.topsep, partopsep := top.partopsep <|> s.partopsep
    itemsep := top.itemsep <|> s.itemsep, parsep := top.parsep <|> s.parsep
    margin := top.margin <|> s.margin }

public theorem ListSet.over_absorb (s t : ListSet) : (s.over t).over t = s.over t := by
  rcases s with ⟨a, b, c, d, m⟩
  rcases t with ⟨e, f, g, h, n⟩
  cases e <;> cases f <;> cases g <;> cases h <;> cases n <;> rfl

/-- The values a first-level list opening in a size step takes from the `\@listi` that step's
command redefines; none elsewhere. -/
public def stepListI (l : ListLineage) (size : Length) (step : Option String) (level : Nat) :
    ListSet :=
  match l, step with
  | .sizeFile, some n =>
    if level != 1 then {} else
    let f := sizeFileOf size
    match stepListITable f n with
    | some (t, p) =>
      let t := if size == Dim.pt f then t else t.scaleRatio size (Dim.pt f)
      let p := if size == Dim.pt f then p else p.scaleRatio size (Dim.pt f)
      { topsep := some t, itemsep := some p, parsep := some p }
    | none => {}
  | _, _ => {}

/-- What a list at `\@listdepth` `level` keeps of its enclosing list's declared values: those its
class's level macro does not set again, the three skips at every level a size file or beamer
defines and `\partopsep` where the level sets its own. -/
public def ListSet.within (l : ListLineage) (size : Length) (level : Nat) (outer : ListSet) :
    ListSet :=
  let resets : Bool := match l with
    | .sizeFile => level ≤ 3
    | .beamer => true
    | .web => false
  let partResets := level ≤ 3 && ((listSkips l size level).bind (·.partopsep)).isSome
  { topsep := if resets then none else outer.topsep
    itemsep := if resets then none else outer.itemsep
    parsep := if resets then none else outer.parsep
    partopsep := if partResets then none else outer.partopsep }

/-- A list's spacing and `\partopsep`: its level's, under its declared values; the web's lists
declare over zero. -/
public def listSpacing (l : ListLineage) (size : Length) (level : Nat) (tokens : Tokens)
    (set : ListSet) : Option (ListSkips × SymGlue) :=
  match listSkips l size level with
  | some sk =>
    some ({ sk with topsep := set.topsep.getD sk.topsep, itemsep := set.itemsep.getD sk.itemsep
                    parsep := set.parsep.getD sk.parsep },
      set.partopsep.getD (partopsepFor l size level tokens))
  | none =>
    if set == {} then none
    else some (⟨set.topsep.getD {}, set.itemsep.getD {}, set.parsep.getD {}, none⟩,
      set.partopsep.getD {})

public theorem listSpacing_undeclared_exact (l : ListLineage) (size : Length) (level : Nat)
    (tokens : Tokens) :
    listSpacing l size level tokens {} =
      (listSkips l size level).map (·, partopsepFor l size level tokens) := by
  unfold listSpacing
  cases listSkips l size level <;> rfl

public theorem listSpacing_declared_exact (l : ListLineage) (size : Length) (level : Nat)
    (tokens : Tokens) (set : ListSet) (sk : ListSkips) (p : SymGlue)
    (h : listSpacing l size level tokens set = some (sk, p)) :
    (∀ g, set.topsep = some g → sk.topsep = g) ∧ (∀ g, set.itemsep = some g → sk.itemsep = g) ∧
      (∀ g, set.parsep = some g → sk.parsep = g) ∧ (∀ g, set.partopsep = some g → p = g) := by
  unfold listSpacing at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro g hg <;> simp [hg]
  · split at h
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro g hg <;> simp [hg]

/-- How a class's list levels one to three read the `\parskip` in force where a list opens. -/
public inductive ListExtra where
  /-- Each level's own skips stand, as the standard classes' do. -/
  | none
  /-- KOMA-Script's `\@list@extra` (scrkernel-paragraphs.dtx), as the parskip package's levels:
  a positive `\parskip` becomes the level's `\parsep`, with no `\topsep` and no `\itemsep`. -/
  | koma
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a list level's macro sets over its size file's values from the `\parskip` in force where
the list opens, its natural width read at the body size. -/
public def ListExtra.over (e : ListExtra) (size : Length) (level : Nat) (inForce : SymGlue) : ListSet :=
  match e with
  | .none => {}
  | .koma =>
    if level ≤ 3 && 0 < inForce.width.resolve size (size / 2) then
      { topsep := some {}, itemsep := some {}, parsep := some inForce }
    else {}

public theorem ListExtra.koma_exact (l : ListLineage) (size : Length) (level : Nat) (tokens : Tokens)
    (inForce : SymGlue) (declared : ListSet) (sk : ListSkips) (p : SymGlue) (hl : level ≤ 3)
    (hpos : 0 < inForce.width.resolve size (size / 2))
    (h : listSpacing l size level tokens ((ListExtra.koma.over size level inForce).over declared) =
      some (sk, p)) :
    sk.topsep = declared.topsep.getD {} ∧ sk.itemsep = declared.itemsep.getD {} ∧
      sk.parsep = declared.parsep.getD inForce := by
  have e : ListExtra.koma.over size level inForce =
      { topsep := some {}, itemsep := some {}, parsep := some inForce } := by
    simp [ListExtra.over, hl, hpos]
  rw [e] at h
  obtain ⟨ht, hi, hp, -⟩ := listSpacing_declared_exact l size level tokens _ sk p h
  rcases declared with ⟨t, q, i, s⟩
  cases t <;> cases i <;> cases s <;> simp_all [ListSet.over]

/-- The `\topsep` and `\partopsep` in force where a trivlist opens, which `\@trivlist` spends. -/
public structure TrivIn where
  topsep : SymGlue
  partopsep : SymGlue
  /-- The `\itemsep` a trivlist's items stand apart by. -/
  itemsep : SymGlue
  deriving Repr, BEq, Inhabited

/-- The tokens the trivlist scope's keys (enumitem's `\setlist[trivlist]`) stand in, by key. -/
public def trivlistKeyNames : List (String × String) :=
  [("topsep", "trivlist-topsep"), ("partopsep", "trivlist-partopsep"),
   ("itemsep", "trivlist-itemsep")]

/-- A trivlist's spacing under the trivlist scope's own keys (enumitem's `\setlist[trivlist]`),
read wherever it opens. -/
public def TrivIn.declared (t : TrivIn) (tokens : Tokens) : TrivIn :=
  { topsep := (tokens.find? "trivlist-topsep").getD t.topsep
    partopsep := (tokens.find? "trivlist-partopsep").getD t.partopsep
    itemsep := (tokens.find? "trivlist-itemsep").getD t.itemsep }

/-- `\@topsepadd`: the `\topsep` in force, with the `\partopsep` where the trivlist opens in
vertical mode. -/
public def TrivIn.add (t : TrivIn) (vertical : Bool) : SymGlue :=
  if vertical then t.topsep.add t.partopsep else t.topsep

/-- Outside every list: the document's `\topsep` and `\partopsep` where declared, else the
class's. -/
public def TrivIn.top (l : ListLineage) (tokens : Tokens) (size : Length) : TrivIn :=
  TrivIn.declared
    { topsep := trivlistSkipFor l tokens size 0
      partopsep := (tokens.find? "partopsep").getD (partopsepDefault l size)
      itemsep := (tokens.find? "itemsep").getD (((listSkips l size 1).map (·.itemsep)).getD {}) }
    tokens

/-- Inside a list at `level` spaced `sk`, `pts` (`listSpacing`): the level's `\topsep` or the zero
the class's extra leaves, which enumitem's `\trivlist` sets again over a declared one, and the
list's `\partopsep`; a lineage without levels keeps `outer`. -/
public def TrivIn.within (l : ListLineage) (extra : ListExtra) (size : Length) (level : Nat)
    (sk : ListSkips) (pts : SymGlue) (outer : TrivIn) : TrivIn :=
  match listSkips l size level with
  | none => outer
  | some lv =>
    { topsep := if sk.topsep == lv.topsep then lv.topsep
        else if extra == .koma && sk.topsep == {} then {}
        else ((extra.over size level sk.parsep).topsep).getD lv.topsep
      partopsep := pts
      itemsep := sk.itemsep }

/-- Where a lineage's trivlists take TeX's `\parskip` on their space; beamer's and the web's take
the page's own, beamer's TeX's in a frame. -/
public def ListLineage.trivTexParskip : ListLineage → Bool
  | .sizeFile => true
  | .beamer | .web => false

public theorem TrivIn.within_declared_exact (l : ListLineage) (size : Length) (level : Nat)
    (tokens : Tokens) (set : ListSet) (sk : ListSkips) (pts : SymGlue) (outer : TrivIn)
    (lv : ListSkips) (hl : listSkips l size level = some lv)
    (h : listSpacing l size level tokens set = some (sk, pts)) :
    (TrivIn.within l .none size level sk pts outer).topsep = lv.topsep ∧
      (TrivIn.within l .none size level sk pts outer).partopsep =
        set.partopsep.getD (partopsepFor l size level tokens) := by
  unfold listSpacing at h
  rw [hl] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have hk : (ListExtra.none == ListExtra.koma) = false := rfl
  simp only [TrivIn.within, hl, ListExtra.over, hk, Bool.false_and]
  split <;> simp_all

public theorem TrivIn.within_koma_exact (l : ListLineage) (size : Length) (level : Nat)
    (sk : ListSkips) (pts : SymGlue) (outer : TrivIn) (lv : ListSkips)
    (hl : listSkips l size level = some lv) (hd : (sk.topsep == lv.topsep) = false)
    (hz : (sk.topsep == {}) = false) (hlv : level ≤ 3)
    (hp : 0 < sk.parsep.width.resolve size (size / 2)) :
    (TrivIn.within l .koma size level sk pts outer).topsep = {} := by
  simp [TrivIn.within, hl, hd, hz, ListExtra.over, hlv, hp]

public theorem trivIn_exact :
    ((TrivIn.top .sizeFile {} (Dim.pt 10)).add true).width.fixed = Dim.pt 10 ∧
    ((TrivIn.top .sizeFile {} (Dim.pt 10)).add false).width.fixed = Dim.pt 8 ∧
    ((TrivIn.top .sizeFile {} (Dim.pt 11)).add true).width.fixed = Dim.pt 12 ∧
    ((TrivIn.top .sizeFile {} (Dim.pt 12)).add true).width.fixed = Dim.pt 13 ∧
    ((TrivIn.top .beamer {} (Dim.pt 11)).add true).width.fixed = Dim.pt 9 := by
  decide

/-- The four glues a size file's `\normalsize` sets around display math. -/
public structure DisplaySkips where
  above : SymGlue
  below : SymGlue
  aboveShort : SymGlue
  belowShort : SymGlue
  deriving Repr, BEq

/-- The size files' display skips, verbatim, keyed by the class option's point size. -/
private def displaySkipsTable : Nat → DisplaySkips
  | 8 | 9 => ⟨ptsGlue 800 400 400, ptsGlue 800 400 400, ptsGlue 0 300 0, ptsGlue 500 300 300⟩
  | 10 => ⟨ptsGlue 1000 200 500, ptsGlue 1000 200 500, ptsGlue 0 300 0, ptsGlue 600 300 300⟩
  | 11 => ⟨ptsGlue 1100 300 600, ptsGlue 1100 300 600, ptsGlue 0 300 0, ptsGlue 650 350 300⟩
  | 12 => ⟨ptsGlue 1200 300 700, ptsGlue 1200 300 700, ptsGlue 0 300 0, ptsGlue 650 350 300⟩
  | 14 => ⟨ptsGlue 1400 300 700, ptsGlue 1400 300 700, ptsGlue 0 400 0, ptsGlue 700 400 300⟩
  | 17 => ⟨ptsGlue 1500 400 800, ptsGlue 1500 400 800, ptsGlue 0 400 0, ptsGlue 800 400 300⟩
  | _ => ⟨ptsGlue 1700 500 800, ptsGlue 1700 500 800, ptsGlue 0 500 0, ptsGlue 1000 500 400⟩

/-- The `\normalsize` a class option's size file sets for a body at that
option's point size; any other size is its own. -/
public def optionNormalSize (size : Length) : Length :=
  ((displayOptions.find? fun o => Dim.pt o.1 == size).map (·.2)).getD size


/-- The option whose point size stands nearest a body size. -/
private def displaySizeFileOf (size : Length) : Nat :=
  (displayOptions.foldl (fun (best : Nat × Length) (o : Nat × Length) =>
    if (size - Dim.pt o.1).abs < (size - Dim.pt best.1).abs then (o.1, o.2) else best)
    (10, Dim.pt 10)).1

/-- The display skips at a body size: the size file's own at an option's size,
else the nearest file's scaled with the type. -/
public def displaySkipsAt (size : Length) : DisplaySkips :=
  let f := displaySizeFileOf size
  let s := displaySkipsTable f
  let body := ((displayOptions.lookup f).getD (Dim.pt f))
  if size == Dim.pt f || size == body then s
  else
    let base := Dim.pt f
    ⟨s.above.scaleRatio size base, s.below.scaleRatio size base, s.aboveShort.scaleRatio size base,
     s.belowShort.scaleRatio size base⟩

/-- `\abovedisplayskip` at a body size, the long skip. -/
public def displaySkipDefault (size : Length) : SymGlue := (displaySkipsAt size).above

public theorem displaySkipDefault_base_exact :
    (displaySkipDefault baseFontSize).width.fixed = Dim.pt 10 := by
  decide

public def displaySkipAbove : String := "abovedisplayskip"
public def displaySkipBelow : String := "belowdisplayskip"
public def displaySkipAboveShort : String := "abovedisplayshortskip"
public def displaySkipBelowShort : String := "belowdisplayshortskip"

/-- The display skips: each the document's token where declared, else the size
file's at the governing size. -/
public def displaySkipsFor (tokens : Tokens) (size : Length) : DisplaySkips :=
  let d := displaySkipsAt size
  { above := (tokens.find? displaySkipAbove).getD d.above
    below := (tokens.find? displaySkipBelow).getD d.below
    aboveShort := (tokens.find? displaySkipAboveShort).getD d.aboveShort
    belowShort := (tokens.find? displaySkipBelowShort).getD d.belowShort }

private theorem displaySkips_default_exact :
    displaySkipsFor {} (Dim.pt 10) = displaySkipsTable 10 ∧
    displaySkipsFor {} (Dim.pt 11) = displaySkipsTable 11 ∧
    displaySkipsFor {} (Dim.pt 12) = displaySkipsTable 12 := ⟨rfl, rfl, rfl⟩

/-- Where a display stands in its paragraph: the facts TeX's display placement
reads that the block's shape does not carry. -/
public structure DisplayCtx where
  inPar : Bool := true
  parEnd : Bool := false
  align : Bool := false
  afterEnv : Bool := false
  /-- A paragraph break inside the display's own carrier stands before it,
  so no carrier around that one reaches it with its paragraph
  (`carrierDisplays`). Placement reads nothing of it. -/
  afterBreak : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The role a display's context rides in, a name no document command can spell. -/
public def DisplayCtx.role (c : DisplayCtx) : String :=
  "display-" ++ (if c.inPar then "p" else "v") ++ (if c.parEnd then "e" else "c") ++
    (if c.align then "a" else "f") ++ (if c.afterEnv then "n" else "o") ++
    (if c.afterBreak then "b" else "")

public def DisplayCtx.all : List DisplayCtx :=
  [false, true].flatMap fun p => [false, true].flatMap fun e => [false, true].flatMap fun a =>
    [false, true].flatMap fun v => [false, true].map fun b =>
      { inPar := p, parEnd := e, align := a, afterEnv := v, afterBreak := b }

public def DisplayCtx.ofRole? (n : String) : Option DisplayCtx :=
  DisplayCtx.all.find? (·.role == n)

public theorem DisplayCtx.ofRole?_role_exact (c : DisplayCtx) : DisplayCtx.ofRole? c.role = some c := by
  cases c with
  | mk p e a v b => cases p <;> cases e <;> cases a <;> cases v <;> cases b <;> decide

public theorem partopsep_exact :
    (partopsepFor .sizeFile (Dim.pt 10) 1 {}).width.fixed = Dim.pt 2 ∧
    (partopsepFor .sizeFile (Dim.pt 11) 1 {}).width.fixed = Dim.pt 3 ∧
    (partopsepFor .sizeFile (Dim.pt 12) 1 {}).width.fixed = Dim.pt 3 ∧
    (partopsepFor .sizeFile (Dim.pt 10) 3 {}).width.fixed = Dim.pt 1 ∧
    (partopsepFor .beamer (Dim.pt 11) 1 {}).width.fixed = 0 := by
  decide

public theorem listSkips_exact :
    ((listSkips .sizeFile (Dim.pt 10) 1).map fun s =>
      (s.topsep.width.fixed, s.itemsep.width.fixed + s.parsep.width.fixed)) = some (Dim.pt 8, Dim.pt 8) ∧
    ((listSkips .sizeFile (Dim.pt 11) 1).map fun s =>
      (s.topsep.width.fixed, s.itemsep.width.fixed + s.parsep.width.fixed)) = some (Dim.pt 9, Dim.pt 9) ∧
    ((listSkips .sizeFile (Dim.pt 12) 1).map fun s =>
      (s.topsep.width.fixed, s.itemsep.width.fixed + s.parsep.width.fixed)) = some (Dim.pt 10, Dim.pt 10) ∧
    ((listSkips .beamer (Dim.pt 11) 1).map fun s =>
      (s.topsep.width.fixed, s.itemsep.width.fixed, s.parsep.width.fixed)) = some (Dim.pt 3, Dim.pt 3, 0) := by
  decide

/-- How a theorem-like block spends its space: the trivlist its spelling opens
and the lengths it sets before its `\item`. -/
public inductive ThmSpace where
  /-- latex.ltx `\@begintheorem`: `\topsep`, with `\partopsep` in vertical
  mode and `\parskip` on top. -/
  | kernel
  /-- amsthm under plain and definition: `\topsep` above and below, no
  `\partopsep`, and no `\parskip` above. -/
  | ams
  /-- amsthm's remark style, which halves both. -/
  | amsHalf
  /-- amsthm's `proof`: `\topsep6\p@\@plus6\p@` over `\partopsep`, always. -/
  | proof
  deriving Repr, BEq, DecidableEq, Inhabited

public def ThmSpace.all : List ThmSpace := [.kernel, .ams, .amsHalf, .proof]

/-- The engine role a theorem-like block rides in, one per `ThmSpace`. -/
public def thmSpaceRole : ThmSpace → String
  | .kernel => "trivlist-kernel"
  | .ams => "trivlist-ams"
  | .amsHalf => "trivlist-remark"
  | .proof => "trivlist-proof"

public def thmSpaceOf? (n : String) : Option ThmSpace :=
  ThmSpace.all.find? (thmSpaceRole · == n)

/-- A theorem-like block's space above its head and below its last line, and
whether `\parskip` stands on top of the space above. -/
public structure ThmSkips where
  above : SymGlue
  below : SymGlue
  parskipAbove : Bool
  deriving Repr, BEq

/-- amsthm's proof `\topsep` (amsthm.sty:433), whatever the body size. -/
public def proofTopsep : SymGlue := { width := { fixed := Dim.pt 6 }, stretch := { fixed := Dim.pt 6 } }

/-- A theorem-like block's space: the `\topsep` in force where it stands,
spent as its spelling spends it. -/
public def thmSkips (l : ListLineage) (size : Length) (level : Nat) (tokens : Tokens)
    (k : ThmSpace) (vertical : Bool) : Option ThmSkips :=
  (listSkips l size level).map fun sk =>
    let pts := partopsepFor l size level tokens
    match k with
    | .kernel =>
      let g := if vertical then sk.topsep.add pts else sk.topsep
      ⟨g, g, true⟩
    | .ams => ⟨sk.topsep, sk.topsep, false⟩
    | .amsHalf =>
      let g := sk.topsep.scale 1 2
      ⟨g, g, false⟩
    | .proof =>
      let g := proofTopsep.add pts
      ⟨g, g, true⟩

public theorem thmSkips_exact :
    ((thmSkips .sizeFile (Dim.pt 10) 1 {} .kernel true).map (·.above.width.fixed)) = some (Dim.pt 10) ∧
    ((thmSkips .sizeFile (Dim.pt 11) 1 {} .kernel true).map (·.above.width.fixed)) = some (Dim.pt 12) ∧
    ((thmSkips .sizeFile (Dim.pt 12) 1 {} .kernel true).map (·.above.width.fixed)) = some (Dim.pt 13) ∧
    ((thmSkips .sizeFile (Dim.pt 10) 1 {} .kernel false).map (·.below.width.fixed)) = some (Dim.pt 8) ∧
    ((thmSkips .sizeFile (Dim.pt 10) 1 {} .ams true).map fun s =>
      (s.above.width.fixed, s.below.width.fixed, s.parskipAbove)) = some (Dim.pt 8, Dim.pt 8, false) ∧
    ((thmSkips .sizeFile (Dim.pt 12) 1 {} .ams true).map (·.above.width.fixed)) = some (Dim.pt 10) ∧
    ((thmSkips .sizeFile (Dim.pt 10) 1 {} .amsHalf true).map (·.above.width.fixed)) = some (Dim.pt 4) ∧
    ((thmSkips .sizeFile (Dim.pt 11) 1 {} .amsHalf true).map (·.above.width.fixed)) =
      some (Dim.pt 9 / 2) ∧
    ((thmSkips .sizeFile (Dim.pt 10) 1 {} .proof false).map (·.above.width.fixed)) = some (Dim.pt 8) ∧
    ((thmSkips .sizeFile (Dim.pt 11) 1 {} .proof false).map (·.below.width.fixed)) = some (Dim.pt 9) ∧
    ((thmSkips .sizeFile (Dim.pt 12) 1 {} .proof false).map (·.above.width.fixed)) = some (Dim.pt 9) ∧
    thmSkips .web (Dim.pt 10) 1 {} .ams true = none := by
  decide

/-- A list level's `\leftmargin⟨n⟩` in thousandths of an em, the web's 1.5 em at every level. -/
public def leftMarginMilli : ListLineage → Nat → Nat
  | .sizeFile, 1 => 2500
  | .sizeFile, 2 => 2200
  | .sizeFile, 3 => 1870
  | .sizeFile, 4 => 1700
  | .sizeFile, _ => 1000
  | .beamer, _ => 2000
  | .web, _ => 1500

/-- The length a level's margin is declared in: `\leftmargini` to
`\leftmarginvi`, a deeper level reading the sixth. -/
public def leftMarginName (level : Nat) : String :=
  "leftmargin" ++ (match min (max level 1) 6 with
    | 1 => "i" | 2 => "ii" | 3 => "iii" | 4 => "iv" | 5 => "v" | _ => "vi")

/-- Whether a length is a level's `\leftmargin⟨n⟩`. -/
public def leftMarginNamed (name : String) : Bool :=
  (List.range 6).any fun k => leftMarginName (k + 1) == name

/-- A list or quotation level's `\leftmargin⟨n⟩`: the document's declared length, else the
lineage's ems. -/
public def leftMarginFor (l : ListLineage) (tokens : Tokens) (level : Nat) : SymGlue :=
  (tokens.find? (leftMarginName level)).getD
    { width := { em := (leftMarginMilli l (max level 1) : Int) } }

/-- The heading's default space above: one full rhythm unit, a token of its
own rather than a multiple of the parskip. -/
public def headingBeforeDefault (size : Length) : SymGlue :=
  { width := { fixed := 2 * rhythmQuantum size } }
/-- The heading's default space below: the half-unit. -/
public def headingAfterDefault (size : Length) : SymGlue :=
  { width := { fixed := rhythmQuantum size } }

public theorem heading_space_above_ge_below (size : Length) (h : Dim.pt 1 ≤ size) :
    (headingAfterDefault size).width.fixed ≤ (headingBeforeDefault size).width.fixed ∧
    (headingAfterDefault size).width.fixed = rhythmQuantum size ∧
    0 < (headingAfterDefault size).width.fixed :=
  ⟨Length.le_of_lt (rhythmQuantum_lt_double size h), rfl, rhythmQuantum_pos size h⟩

public theorem default_rhythm_multiples (size : Length) (h : Dim.pt 1 ≤ size) :
    (parskipDefault size).width.fixed = rhythmQuantum size ∧
    0 < (parskipDefault size).width.fixed :=
  ⟨rfl, rhythmQuantum_pos size h⟩

public theorem parskip_is_quantum (size : Length) :
    (parskipDefault size).width.fixed = rhythmQuantum size := by rfl

public theorem parskip_halves_leading_at_bases :
    2 * (parskipDefault baseFontSize).width.fixed = leadingFor baseFontSize := by
  decide

public theorem caption_gaps_rhythm (size : Length) (h : Dim.pt 1 ≤ size) :
    (captionSepDefault size).width.fixed = rhythmQuantum size ∧
    (floatSepDefault size).width.fixed = 2 * rhythmQuantum size ∧
    (captionSepDefault size).width.fixed < (floatSepDefault size).width.fixed :=
  ⟨rfl, rfl, rhythmQuantum_lt_double size h⟩

/-- The title block's author strut: two rhythm units of line box for the author's name. -/
public def titleAuthorStrut : SymGlue := { width := { em := 2 * leadingMilli } }

/-- The gap after the whole title block: two rhythm units, shrinkable by the half-unit. -/
public def titleBlockAfter : SymGlue :=
  { width := { em := 2 * leadingMilli }, shrink := { em := leadingMilli / 2 } }

/-- The gap between a title bar and the type it cuts: three rhythm quanta, the
same on both sides. -/
public def titleBarGap : SymGlue := { width := { em := 3 * leadingMilli / 2 } }

/-- LaTeX's `\strutbox` height at a size: 0.7 of its baselineskip. -/
public def frameTitleStrut (titleSize : Length) : Length := leadingFor titleSize * 7 / 10

/-- The frametitle padding: `\ht\strutbox` of the title's font, in em of the title's size. -/
public def frameTitlePadding : SymGlue := { width := { em := 7 * leadingMilli / 10 } }

/-- The frame title's side margins: 0.85 of `\ht\strutbox` in the frametitle font. -/
public def frameTitleInset (titleSize : Length) : Length := frameTitleStrut titleSize * 85 / 100

/-- The step a frame title with no bar sets at: beamer's default font theme's `\Large`. -/
public def plainFrameTitleStep : String := "Large"

/-- Where beamer's default frametitle box ends below the title's last
baseline: a strut's depth, less 1ex. -/
public def defaultFrameTitleBelow (titleSize : Length) (leading : Nat) (ex : Length) : Length :=
  leadingFor titleSize leading * 3 / 10 - ex


/-- The skip outside a title bar, above the top one and below the bottom one: one rhythm quantum. -/
public def titleBarSkip : SymGlue := { width := { em := leadingMilli / 2 } }

public theorem title_author_rhythm :
    titleAuthorStrut.width.resolve baseFontSize 0 = 4 * rhythmQuantum baseFontSize ∧
    titleBlockAfter.width.resolve baseFontSize 0 = 4 * rhythmQuantum baseFontSize ∧
    titleBlockAfter.shrink.resolve baseFontSize 0 = rhythmQuantum baseFontSize := by
  decide

public theorem title_bar_rhythm :
    titleBarGap.width.resolve baseFontSize 0 = 3 * rhythmQuantum baseFontSize ∧
    titleBarSkip.width.resolve baseFontSize 0 = rhythmQuantum baseFontSize := by
  decide

/-- The rhythm multiple of each kind of default block boundary, the one table
both backends realize. -/
@[expose] public def rhythmGapQuanta : List (String × Nat) :=
  [("peer", 1), ("heading", 2), ("caption", 1), ("float", 2), ("trivlist", 2)]

public theorem rhythm_table_exact (size : Length) :
    ((rhythmGapQuanta.lookup "peer").getD 0 : Int) * rhythmQuantum size
      = (parskipDefault size).width.fixed ∧
    ((rhythmGapQuanta.lookup "caption").getD 0 : Int) * rhythmQuantum size
      = (captionSepDefault size).width.fixed ∧
    ((rhythmGapQuanta.lookup "float").getD 0 : Int) * rhythmQuantum size
      = (floatSepDefault size).width.fixed ∧
    ((rhythmGapQuanta.lookup "heading").getD 0 : Int) * rhythmQuantum size
      = (headingBeforeDefault size).width.fixed ∧
    ((rhythmGapQuanta.lookup "trivlist").getD 0 : Int) * rhythmQuantum size
      = (parskipDefault size).width.fixed + (trivlistSkipDefault size).width.fixed ∧
    (rhythmGapQuanta.lookup "heading").getD 0
      = 2 * (rhythmGapQuanta.lookup "peer").getD 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide⟩ <;>
    simp [rhythmGapQuanta, parskipDefault, captionSepDefault, floatSepDefault,
      headingBeforeDefault, trivlistSkipDefault, Dim.SymLength.ofLength,
      List.lookup] <;> length_omega

/-- The key a pairing is reported under: its name, colour and ground, as its
contrast warning's `subject`. -/
public def inkKey (role : String) (declared ground : Color) : String :=
  s!"{role}:{declared.hex}@{ground.hex}"

/-- The colours a document and its bundles declare, in declaration order:
author colours and roles, one kind each. -/
public structure Palette where
  entries : Array (ColorRef × Color) := #[]
  /-- `covered = <n>%`: each covered run's ink fraction over the surface,
  beamer's `\setbeamercovered{transparent=<n>}`. -/
  coveredFraction : Option Nat := none
  /-- Entries declared under `\palette[decorative]{...}`, exempt from the pairing diagnostic. -/
  decorative : Array ColorRef := #[]
  /-- The generated palette its roles were installed from (`\palette[seeds]`). -/
  seeded : Option SeedPalette.SeedState := none
  /-- The class's defaults where nothing declares a role. -/
  classColors : ClassColors := {}
  /-- The declared output profile's transform, through which a CMYK colour shows on screen. -/
  profile : Option Icc.Transform := none
  deriving Repr, BEq, Inhabited

/-- A colour as the palette's output profile shows it on screen: a CMYK colour through the
profile, any other colour, and any colour under no profile, as it stands. -/
public def Palette.shown (p : Palette) (c : Color) : Color :=
  match p.profile with
  | some t => c.through t
  | none => c

/-- The colour a palette declares under one name, of either kind. -/
public def Palette.lookup (p : Palette) (ref : ColorRef) : Option Color :=
  (p.entries.find? (·.1 == ref)).map (·.2)

/-- The author colours, in declaration order. -/
public def Palette.colors (p : Palette) : Array (String × Color) :=
  p.entries.filterMap fun
    | (.color n, c) => some (n, c)
    | (.role _, _) => none

section DesignResolve

/-- What a name in a colour expression reads: an author colour of that name,
else the declared role whose key it is. -/
public def Palette.refOf? (p : Palette) (name : String) : Option ColorRef :=
  if (p.lookup (.color name)).isSome then some (.color name)
  else (Role.ofKey? name).bind fun r =>
    if (p.lookup (.role r)).isSome then some (.role r) else none

/-- A name in a colour expression: an author colour, else a role. -/
public def Palette.find? (p : Palette) (name : String) : Option Color :=
  (p.lookup (.color name)).or ((Role.ofKey? name).bind fun r => p.lookup (.role r))

end DesignResolve

/-- A later declaration of a name overrides, keeping one entry per name. -/
@[expose] public def Palette.declare (p : Palette) (ref : ColorRef) (c : Color)
    (decorative : Bool := false) : Palette :=
  { p with
    entries := redeclare p.entries ref c
    decorative := if decorative then
        if p.decorative.contains ref then p.decorative
        else p.decorative.push ref
      else p.decorative.filter (· != ref) }

/-- The `\palette{<key> = …}` door: a role's key declares the role, any
other key an author colour. -/
public def Palette.declareKey (p : Palette) (key : String) (c : Color)
    (decorative : Bool := false) : Palette :=
  p.declare (ColorRef.ofKey key) c decorative

/-- Remove one name, leaving every other declaration as it stands. -/
public def Palette.erase (p : Palette) (ref : ColorRef) : Palette :=
  { p with entries := p.entries.filter (·.1 != ref)
           decorative := p.decorative.filter (· != ref) }

/-- Restore one name from an opening palette: its original value and
classification when present, else its absence. -/
public def Palette.restore (p opening : Palette) (ref : ColorRef) : Palette :=
  match opening.lookup ref with
  | some c => p.declare ref c (opening.decorative.contains ref)
  | none => p.erase ref

/-- Two palettes that resolve every name alike, whatever their declaration
order, with the same decorative names and cover. -/
@[expose] public def Palette.sameAs (a b : Palette) : Bool :=
  -- Equal entry order is the fast path; only a reordered palette pays the quadratic reading.
  (a.entries == b.entries && a.decorative == b.decorative ||
    (a.entries ++ b.entries).all (fun (k, _) => a.lookup k == b.lookup k) &&
      (a.decorative ++ b.decorative).all (fun k => a.decorative.contains k == b.decorative.contains k)) &&
    a.coveredFraction == b.coveredFraction

/-- The palette without its covering: its share and covered colour, which only steps read. -/
@[expose] public def Palette.uncovered (p : Palette) : Palette :=
  { p with coveredFraction := none, entries := p.entries.filter (·.1 != .role .covered)
           decorative := p.decorative.filter (· != .role .covered) }

/-- The palette with `q`'s covered share. -/
@[expose] public def Palette.coveredAs (p q : Palette) : Palette :=
  { p with coveredFraction := q.coveredFraction }

public theorem Palette.erase_exact (p : Palette) (ref : ColorRef) :
    (p.erase ref).lookup ref = none := by
  simp only [Palette.erase, Palette.lookup]
  have hnone : (p.entries.filter (·.1 != ref)).find? (·.1 == ref) = none := by
    rw [Array.find?_eq_none]
    intro x hx
    have hne := (Array.mem_filter.mp hx).2
    simpa using hne
  simp [hnone]

public theorem Palette.erase_keeps_others (p : Palette) (ref other : ColorRef)
    (h : other ≠ ref) : (p.erase ref).lookup other = p.lookup other := by
  unfold Palette.erase Palette.lookup
  rw [Array.find?_filter]
  have hpred :
      (fun a : ColorRef × Color => decide ((a.fst != ref) = true ∧ (a.fst == other) = true))
        = (fun a : ColorRef × Color => a.fst == other) := by
    funext x
    by_cases hx : (x.1 == other) = true
    · have hxe : x.1 = other := by simpa using hx
      simp [hxe, h]
    · simp [hx]
  rw [hpred]

public theorem Palette.restore_exact (p opening : Palette) (ref : ColorRef) :
    (p.restore opening ref).lookup ref = opening.lookup ref := by
  cases h : opening.lookup ref with
  | none => simpa [Palette.restore, h] using Palette.erase_exact p ref
  | some c =>
    simp only [Palette.restore, h]
    unfold Palette.declare Palette.lookup
    rw [declare_find_eq]
    rfl

public theorem Palette.declare_last_wins (p : Palette) (ref : ColorRef) (c : Color) :
    (p.declare ref c).lookup ref = some c := by
  unfold declare lookup
  rw [declare_find_eq]
  rfl

public theorem Palette.declare_find_exact (p : Palette) (ref : ColorRef)
    (color : Color) (decorative : Bool) :
    (p.declare ref color decorative).lookup ref = some color := by
  unfold Palette.declare Palette.lookup
  rw [declare_find_eq]
  rfl

public theorem Palette.declare_overwrite (p : Palette) (ref : ColorRef) (c c' : Color) :
    (p.declare ref c).declare ref c' = p.declare ref c' := by
  simp [declare, declare_collapse]

public theorem Palette.declare_keeps_others (p : Palette) (ref other : ColorRef) (c : Color)
    (d : Bool) (h : other ≠ ref) : (p.declare ref c d).lookup other = p.lookup other := by
  unfold declare lookup
  rw [declare_keeps _ _ _ _ h]

public theorem Palette.restore_keeps_others (p opening : Palette) (ref other : ColorRef)
    (h : other ≠ ref) : (p.restore opening ref).lookup other = p.lookup other := by
  unfold Palette.restore
  cases opening.lookup ref with
  | none => exact p.erase_keeps_others ref other h
  | some c => exact p.declare_keeps_others ref other c _ h

public theorem Palette.restore_decorative_exact (p opening : Palette) (ref : ColorRef) :
    (p.restore opening ref).decorative.contains ref =
      ((opening.lookup ref).isSome && opening.decorative.contains ref) := by
  cases h : opening.lookup ref with
  | none => simp [Palette.restore, h, Palette.erase]
  | some c =>
    by_cases hd : ref ∈ opening.decorative
    · by_cases hp : ref ∈ p.decorative <;>
        simp [Palette.restore, h, Palette.declare, hd, hp]
    · simp [Palette.restore, h, Palette.declare, hd]

public theorem declare_decorative_rides (p : Palette) (ref : ColorRef) (c : Color) :
    (p.declare ref c false).decorative.contains ref = false := by
  simp [Palette.declare]

public theorem declare_decorative_names (p : Palette) (ref : ColorRef) (c : Color) :
    (p.declare ref c true).decorative.contains ref = true := by
  simp only [Palette.declare, ite_true]
  by_cases h : ref ∈ p.decorative <;> simp [h]

/-- `pct`% of `x` over the rest of `y`, rounded half up. -/
private def Color.mixStep (x y pct : Nat) : Nat := (x * pct + y * (100 - pct) + 50) / 100

/-- A colour's components in the CMYK model: its own when declared there, else
xcolor's rgb→cmy→cmyk conversion. -/
private def Color.toCmyk (c : Color) : Nat × Nat × Nat × Nat :=
  match c.cmyk with
  | some q => q
  | none =>
    let cy := 1000 - milli c.r
    let m := 1000 - milli c.g
    let y := 1000 - milli c.b
    let k := min cy (min m y)
    (cy - k, m - k, y - k, k)

/-- xcolor's `!` mix in CMYK: per declared component, the second operand converted by `toCmyk`. -/
private def Color.mixCmyk (a : Nat × Nat × Nat × Nat) (pct : Nat) (b : Color) : Color :=
  let q := b.toCmyk
  Color.ofCmyk (mixStep a.1 q.1 pct) (mixStep a.2.1 q.2.1 pct)
    (mixStep a.2.2.1 q.2.2.1 pct) (mixStep a.2.2.2 q.2.2.2 pct)

/-- An ink's tint mixed with `b`: over the paper or another tint of the ink it stays a tint of the
ink, over anything else it is the process mix of its alternate. -/
private def Color.mixInk (a : Color) (i : Ink) (t : Rat) (pct : Nat) (b : Color) : Color :=
  let p : Rat := (pct : Rat) / 100
  if 100 ≤ pct then a
  else if b.isPaper then Color.ofInk i (t * p)
  else match b.ink? with
    | some (j, u) => if i == j then Color.ofInk i (t * p + u * (1 - p))
      else mixCmyk (a.cmyk.getD (0, 0, 0, 0)) pct b
    | none => mixCmyk (a.cmyk.getD (0, 0, 0, 0)) pct b

/-- A colour's DeviceGray value, where it is declared in gray. -/
private def Color.grayOf? (c : Color) : Option Decl.ColorComponent :=
  match c.pdfModel with
  | some (.gray v) => (Decl.parseDecimal v).bind fun (m, scale) =>
    if m < 0 then none else some { num := m.toNat, scale }
  | some (.rgb ..) | some (.cmyk ..) | some (.separation ..) | none => none

/-- xcolor's `!` mix of two gray colours, in gray. -/
private def Color.mixGray (x y : Decl.ColorComponent) (pct : Nat) : Color :=
  Color.ofGray { num := x.num * y.scale * pct + y.num * x.scale * (100 - pct)
                 scale := x.scale * y.scale * 100 }

/-- One step of xcolor's `!` mix in `a`'s model, before it takes `a`'s origin. -/
private def Color.mixed (a : Color) (pct : Nat) (b : Color) : Color :=
  match a.ink?, b.ink? with
  | some (i, t), _ => a.mixInk i t pct b
  | none, some (j, u) =>
    if a.isPaper then Color.ofInk j (u * (1 - (pct : Rat) / 100))
    else match a.cmyk with
      | some q => mixCmyk q pct b
      | none => mixSrgb a pct b.xcolorRgb
  | none, none => match a.cmyk with
    | some q => mixCmyk q pct b
    | none => match a.grayOf?, b.grayOf? with
      | some x, some y => mixGray x y pct
      | _, _ => mixSrgb a pct b.xcolorRgb

/-- One step of xcolor's `!` mix: `pct`% of `a` over the rest of `b`, in `a`'s model and chosen as
`a` was; the paper over an ink is a tint of the ink, as the ink over the paper is. -/
public def Color.mix (a : Color) (pct : Nat) (b : Color) : Color :=
  { a.mixed pct b with origin := a.origin }

private theorem Color.ofInk_model (i : Ink) (t : Rat) : (Color.ofInk i t).model = .cmyk := rfl

private theorem Color.mixCmyk_model (q : Nat × Nat × Nat × Nat) (pct : Nat) (b : Color) :
    (mixCmyk q pct b).model = .cmyk := rfl

public theorem Color.mix_model_exact (a b : Color) (pct : Nat) :
    (a.mix pct b).model =
      if a.ink?.isNone && a.isPaper && b.ink?.isSome then .cmyk else a.model := by
  show (a.mixed pct b).model = _
  unfold Color.mixed
  cases hi : a.ink? with
  | some it =>
    obtain ⟨i, t⟩ := it
    have ha : a.model = .cmyk := by
      unfold Color.model; rw [hi]; cases a.cmyk <;> rfl
    simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, ha]
    simp only [Color.mixInk]
    split
    · exact ha
    · split
      · exact Color.ofInk_model _ _
      · split
        · split
          · exact Color.ofInk_model _ _
          · exact Color.mixCmyk_model _ _ _
        · exact Color.mixCmyk_model _ _ _
  | none =>
    cases hb : b.ink? with
    | some ju =>
      obtain ⟨j, u⟩ := ju
      simp only [Option.isNone_none, Option.isSome_some, Bool.true_and, Bool.and_true]
      by_cases hp : a.isPaper = true
      · simp only [hp, ↓reduceIte]
        exact Color.ofInk_model _ _
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
        cases hc : a.cmyk with
        | some q =>
          have ha : a.model = .cmyk := by unfold Color.model; rw [hc]
          rw [ha]
          exact Color.mixCmyk_model _ _ _
        | none =>
          have ha : a.model = .srgb := by unfold Color.model; rw [hc, hi]
          rw [ha]
          rfl
    | none =>
      simp only [Option.isNone_none, Option.isSome_none, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte]
      cases hc : a.cmyk with
      | some q =>
        have ha : a.model = .cmyk := by unfold Color.model; rw [hc]
        rw [ha]
        exact Color.mixCmyk_model _ _ _
      | none =>
        have ha : a.model = .srgb := by unfold Color.model; rw [hc, hi]
        rw [ha]
        simp only
        split <;> rfl

private theorem Color.mix_srgb_id (a b : Color) (pct : Nat) (h : a.cmyk = none)
    (hi : a.ink? = none) (hb : b.ink? = none) (hg : a.grayOf? = none) :
    a.mix pct b = a.mixSrgb pct b.xcolorRgb := by
  simp [Color.mix, Color.mixed, Color.mixSrgb, h, hi, hb, hg]

public def asciiBlank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- A colour name an expression reads as itself: no `!` mix operator and no
blank at either end. -/
public def plainName (n : String) : Bool :=
  !n.toList.contains '!' && (n.toList.head?.all fun c => !asciiBlank c) &&
    (n.toList.getLast?.all fun c => !asciiBlank c)

/-- The `!`-separated parts of a palette expression, each trimmed of ASCII whitespace. -/
private def bangParts (cur : List Char) : List Char → List String
  | [] => [trimmed cur]
  | c :: rest =>
    if c == '!' then trimmed cur :: bangParts [] rest
    else bangParts (c :: cur) rest
where
  /-- `cur` holds the segment reversed. -/
  trimmed (cur : List Char) : String :=
    String.ofList (((cur.dropWhile asciiBlank).reverse).dropWhile asciiBlank)

/-- A decimal fraction `num / scale` as a colour component. -/
private def part (num scale : Nat) : Decl.ColorComponent := { num, scale }

/-- xcolor's base colours (manual §4.1, Table 1) in the models xcolor declares them in: the grays
in gray, cyan, magenta, yellow and olive in CMYK, the rest in RGB. -/
private def xcolorBase (s : String) : Option Color :=
  let one := part 1 1
  let zero := part 0 1
  let half := part 5 10
  let rgb (r g b : Decl.ColorComponent) : Option Color := some (Color.ofRgbUnit r g b)
  let cmyk (c m y k : Decl.ColorComponent) : Option Color := some (Color.ofCmykSource c m y k)
  match s with
  | "black" => some (Color.ofGray zero)
  | "white" => some (Color.ofGray one)
  | "red" => rgb one zero zero
  | "green" => rgb zero one zero
  | "blue" => rgb zero zero one
  | "cyan" => cmyk one zero zero zero
  | "magenta" => cmyk zero one zero zero
  | "yellow" => cmyk zero zero one zero
  | "brown" => rgb (part 75 100) half (part 25 100)
  | "lime" => rgb (part 75 100) one zero
  | "olive" => cmyk zero zero one half
  | "orange" => rgb one half zero
  | "pink" => rgb one (part 75 100) (part 75 100)
  | "purple" => rgb (part 75 100) zero (part 25 100)
  | "teal" => rgb zero half half
  | "violet" => rgb half zero half
  | "gray" => some (Color.ofGray half)
  | "darkgray" => some (Color.ofGray (part 25 100))
  | "lightgray" => some (Color.ofGray (part 75 100))
  | _ => none

/-- xcolor's `!` mix (`Color.mix`) as the palette shows colours. -/
public def Palette.mix (p : Palette) (a : Color) (pct : Nat) (b : Color) : Color :=
  p.shown (a.mix pct b)

/-- One atom of a palette expression: a declared entry first, then xcolor's base colours as the
palette shows them. -/
private def Palette.atom (p : Palette) (s : String) : Option Color :=
  (p.find? s).orElse fun _ => (xcolorBase s).map p.shown

/-- A palette expression: a name, or xcolor's `!` mix folding left, where a
trailing `a!30` mixes toward white. -/
public def Palette.resolve (p : Palette) (expr : String) : Option Color :=
  let rec go (c : Color) : List String → Option Color
    | [] => some c
    | pctS :: rest =>
      match pctS.toNat? with
      | none => none
      | some pct =>
        if pct > 100 then none
        else match rest with
          | [] => some (p.mix c pct (Color.ofGray (part 1 1)))
          | name :: rest' =>
            match p.atom name with
            | some b => go (p.mix c pct b) rest'
            | none => none
  match bangParts [] expr.toList with
  | [] => none
  | first :: rest =>
    match p.atom first with
    | some c => go c rest
    | none => none

/-- The first ink an expression names that its value does not paint with. -/
public def Palette.lostInk? (p : Palette) (expr : String) : Option Ink := do
  let c ← p.resolve expr
  (bangParts [] expr.toList).findSome? fun a =>
    if a.toNat?.isSome then none
    else (p.atom a).bind fun x => x.ink?.bind fun (i, _) =>
      if (c.ink?.map (·.1)) == some i then none else some i

/-- Each colour expression a source spells that mixes an ink away, with that ink, once: the
maximal runs of name characters and `!` that the palette resolves losing an ink. -/
public def Palette.lostInkExprs (p : Palette) (src : String) : Array (String × Ink) :=
  let exprChar (c : Char) : Bool := c.isAlphanum || c == '!' || c == '.' || c == '-' || c == '_'
  let flush (cur : String) (acc : Array (String × Ink)) : Array (String × Ink) :=
    if !cur.contains '!' || acc.any (·.1 == cur) then acc
    else match p.lostInk? cur with
      | some i => acc.push (cur, i)
      | none => acc
  let (cur, acc) := src.toList.foldl (init := ("", #[])) fun (cur, acc) c =>
    if exprChar c then (cur.push c, acc) else ("", flush cur acc)
  flush cur acc

/-- An exact rational of a decimal component. -/
private def ratOf (c : Decl.ColorComponent) : Rat := (c.num : Rat) / (max 1 c.scale : Nat)

/-- The ink a `spot(...)` source declares, its alternate as written. -/
public def Ink.ofSource (name : String) (c m y k : Decl.ColorComponent) : Ink :=
  { name, c := ratOf c, m := ratOf m, y := ratOf y, k := ratOf k }

/-- Resolve one typed colour specification to the `Color` both backends consume. -/
public def Palette.resolveSpec (p : Palette) : Decl.ColorSpec → Option Color
  | .named expr => p.resolve expr
  | .html r g b => some (Color.ofHtml r g b)
  | .rgbByte r g b => some (Color.ofRgbByte r g b)
  | .rgbUnit r g b => some (Color.ofRgbUnit r g b)
  | .gray v => some (Color.ofGray v)
  | .cmyk c m y k => some (p.shown (Color.ofCmykSource c m y k))
  | .spot n c m y k => some (p.shown (Color.ofInk (Ink.ofSource n c m y k) 1))
  | .oklab L a b => (Decl.ColorSpec.oklab L a b).okLab?.map fun lab => (Oklab.ofLab lab).declared
  | .oklch L C H => (Decl.ColorSpec.oklch L C H).okLab?.map fun lab => (Oklab.ofLab lab).declared

/-- Parse and resolve a colour given in source syntax, optionally under a model. -/
public def Palette.resolveSource (p : Palette) (model : Option String) (src : String) :
    Except Decl.ColorSpecError (Option Color) := do
  return p.resolveSpec (← Decl.parseColorSpec model src)

public theorem Palette.resolveSpec_models_exact (p : Palette) (r g b : UInt8)
    (x y z c m k : Decl.ColorComponent) :
    p.resolveSpec (.html r g b) = some (Color.ofHtml r g b) ∧
    p.resolveSpec (.rgbByte x y z) = some (Color.ofRgbByte x y z) ∧
    p.resolveSpec (.rgbUnit x y z) = some (Color.ofRgbUnit x y z) ∧
    p.resolveSpec (.gray x) = some (Color.ofGray x) ∧
    p.resolveSpec (.cmyk c m y k) = some (p.shown (Color.ofCmykSource c m y k)) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Font families a document asks for, as declared by `\fonts`. -/
public structure FontSpec where
  body : Option String := none
  sans : Option String := none
  mono : Option String := none
  /-- The math face (`\fonts{ math = ... }`, fontspec's `\setmathfont`), which
  must carry an OpenType MATH table. -/
  math : Option String := none
  /-- unicode-math's option-driven alphabet sources. -/
  mathSources : Math.MathAlphabetSources := {}
  dirs : Array String := #[]
  /-- Families the document names beside the three slots (fontspec's
  `\newfontfamily\cmd{Family}`), in declaration order. -/
  families : Array (String × String) := #[]
  /-- Per-variant faces the document named: `(slot, weight, italic)` to a face name. -/
  faces : Array ((Nat × Nat × Bool) × String) := #[]
  deriving Repr, BEq, Inhabited

/-- The first slot past the body, sans and mono slots: a declared family's. -/
public def familySlotBase : Nat := 3

/-- The slot a declared family's command selects. -/
public def FontSpec.familySlot (s : FontSpec) (name : String) : Option Nat :=
  (s.families.findIdx? (·.1 == name)).map (· + familySlotBase)

public def FontSpec.slotFamily (s : FontSpec) (slot : Nat) : Option String :=
  if slot < familySlotBase then none else (s.families[slot - familySlotBase]?).map (·.2)

/-- Declare a family by its command: a redeclaration keeps the command's slot
and replaces the family. -/
public def FontSpec.declareFamily (s : FontSpec) (name family : String) : FontSpec :=
  if s.families.any (·.1 == name) then
    { s with families := s.families.map fun (n, f) => if n == name then (n, family) else (n, f) }
  else { s with families := s.families.push (name, family) }

/-- A later declaration of a variant overrides, keeping one entry per `(slot, weight, italic)`. -/
public def FontSpec.declareFace (s : FontSpec) (variant : Nat × Nat × Bool)
    (face : String) : FontSpec :=
  { s with faces := redeclare s.faces variant face }

public def FontSpec.faceFor (s : FontSpec) (slot weight : Nat) (italic : Bool) : Option String :=
  (s.faces.find? (·.1 == (slot, weight, italic))).map (·.2)

public theorem FontSpec.faceFor_last_declared (s : FontSpec) (v : Nat × Nat × Bool)
    (f : String) : (s.declareFace v f).faceFor v.1 v.2.1 v.2.2 = some f := by
  unfold declareFace faceFor
  rw [show ((v.1, v.2.1, v.2.2) : Nat × Nat × Bool) = v from rfl, declare_find_eq]
  rfl

/-- What the reader must be able to reach in place of a non-text element. -/
public inductive AltPolicy where
  | judged
  | required
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The policy's `\output` spelling. -/
@[expose] public def AltPolicy.name : AltPolicy → String
  | .judged => "judged"
  | .required => "required"

/-- Each policy by its `\output` spelling. -/
@[expose] public def AltPolicy.byName : List (String × AltPolicy) :=
  [AltPolicy.judged, .required].map fun p => (p.name, p)

public theorem AltPolicy.byName_complete (p : AltPolicy) :
    AltPolicy.byName.lookup p.name = some p := by
  cases p <;> rfl

/-- The colour the reader is meant to see: `device` leaves the numbers to the
device, `srgb` defines them as sRGB. -/
public inductive ColorIntent where
  | device
  | srgb
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The intent's `\output` spelling. -/
@[expose] public def ColorIntent.name : ColorIntent → String
  | .device => "device"
  | .srgb => "srgb"

/-- Each intent by its `\output` spelling. -/
@[expose] public def ColorIntent.byName : List (String × ColorIntent) :=
  [ColorIntent.device, .srgb].map fun c => (c.name, c)

public theorem ColorIntent.byName_complete (c : ColorIntent) :
    ColorIntent.byName.lookup c.name = some c := by
  cases c <;> rfl

/-- Whether the artifact carries the faces it was set in: `embedded` travels
with the artifact, `none` leaves them to something else. -/
public inductive FontPolicy where
  | embedded
  | none
  deriving Repr, @[expose] BEq, DecidableEq, Inhabited

/-- The policy's `\output` spelling. -/
@[expose] public def FontPolicy.name : FontPolicy → String
  | .embedded => "embedded"
  | .none => "none"

/-- Each policy by its `\output` spelling. -/
@[expose] public def FontPolicy.byName : List (String × FontPolicy) :=
  [FontPolicy.embedded, .none].map fun p => (p.name, p)

public theorem FontPolicy.byName_complete (p : FontPolicy) :
    FontPolicy.byName.lookup p.name = some p := by
  cases p <;> rfl

/-- The semantic output contract: facts about the artifact the reader must
get, declared in `\output` and read by every backend. -/
public structure OutputContract where
  alternatives : AltPolicy := .judged
  color : ColorIntent := .device
  fonts : Option FontPolicy := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a backend carries alternatives: `none`, or `attribute` (HTML's `alt`). -/
public inductive AltReal where
  | none
  | attribute
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a backend carries colour: `device`, or `srgbByDefinition` (CSS colours are sRGB). -/
public inductive ColorReal where
  | device
  | srgbByDefinition
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a backend carries faces: `embeds` (in the file), `ships` (beside
the page, when the document's policy asks). -/
public inductive FontReal where
  | embeds
  | ships
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a backend uses script: `never`; `constantGated` (one constant
script, gated on a class, with a declared floor when scripting is off). -/
public inductive ScriptReal where
  | never
  | constantGated
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a backend carries mathematics: `layout` (glyphs placed by the
engine), `mathmlCore` (MathML Core, the browser lays out). -/
public inductive MathReal where
  | layout
  | mathmlCore
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One backend's realization record: values only. -/
public structure Realization where
  alternatives : AltReal
  color : ColorReal
  fonts : FontReal
  scripting : ScriptReal
  math : MathReal
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A declared contract fact an artifact does not realize: the fact's key,
what was declared, what the artifact does instead. -/
public structure Unmet where
  fact : String
  declared : String
  realized : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The closed key list of the contract: the facts `unmet` can name and the
keys `\output` accepts. -/
public def OutputContract.facts : List String := ["alternatives", "color", "fonts"]

/-- One fact judged: unmet when the realization cannot honour the declaration. -/
private def OutputContract.judge (fact declared realized : String) (met : Bool) :
    Option Unmet :=
  if met then none else some { fact, declared, realized }

private theorem OutputContract.judge_fact {fact declared realized : String} {met : Bool}
    {u : Unmet} (h : OutputContract.judge fact declared realized met = some u) :
    u.fact = fact := by
  unfold judge at h
  split at h
  · exact absurd h (by simp)
  · cases h; rfl

/-- The facts this artifact does not realize, one entry per unmet key. -/
public def OutputContract.unmet (c : OutputContract) (r : Realization) : Array Unmet :=
  #[judge "alternatives" AltPolicy.required.name "no alternative channel"
      (match c.alternatives, r.alternatives with
        | .judged, _ => true
        | .required, .attribute => true
        | .required, .none => false),
    judge "color" ColorIntent.srgb.name "device colour"
      (match c.color, r.color with
        | .device, _ => true
        | .srgb, .srgbByDefinition => true
        | .srgb, .device => false),
    judge "fonts" FontPolicy.embedded.name "no faces carried"
      (match c.fonts, r.fonts with
        | none, _ => true
        | some .none, _ => true
        | some .embedded, .embeds => true
        | some .embedded, .ships => true)].filterMap id

public theorem OutputContract.unmet_default_exact (r : Realization) :
    ({} : OutputContract).unmet r = #[] := by
  simp [unmet, judge]

public theorem OutputContract.unmet_covers (c : OutputContract) (r : Realization) :
    ∀ u ∈ c.unmet r, u.fact ∈ OutputContract.facts := by
  intro u hu
  simp only [unmet, Array.mem_filterMap, id] at hu
  obtain ⟨j, hj, hju⟩ := hu
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;> rw [judge_fact hju] <;> simp [facts]

/-- One W0701 per unmet fact, with the fact's key as its `subject`. -/
public def contractDiags (us : Array Unmet) : Array Diag :=
  us.map fun u =>
    Diag.of .W0701
      (Diag.say .W0701 .value (Diag.Name.value s!"{u.fact} = {u.declared}") (some (none, "\\output")))
      (detail := some s!"this artifact carries {u.realized}")
      (help := some s!"drop '{u.fact} = {u.declared}' from '\\output', or build a format that carries it")
      (subject := some u.fact)

public theorem contract_accounts (us : Array Unmet) : (contractDiags us).size = us.size :=
  Array.size_map ..

/-- The colour schemes a class's page offers where its document names none:
every scheme, or its print, its own screen and that screen's more contrast. -/
public inductive ClassSchemes where
  | every
  | own
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What to build, as declared by `\output`. -/
public structure OutputSpec where
  formats : Array String := #[]
  /-- The colour schemes the HTML page offers
  (`schemes = print, light, dark`); `none` takes the class's. -/
  schemes : Option (Array Scheme) := none
  contract : OutputContract := {}
  /-- The conformance profiles the PDF is held to
  (`profiles = pdf/a-4, pdf/ua-2`), each implying a `pdf.profile`
  assertion. -/
  profiles : Array String := #[]
  css : Option String := none
  /-- A local stylesheet the driver captures relative to the document, whose
  rules win ties with the engine's styles. -/
  stylesheet : Option String := none
  /-- The markdown twin's file name as served (`md = "llms.txt"`). -/
  md : Option String := none
  deriving Repr, BEq, Inhabited

/-- One format onto the list, dedup by name. -/
public def OutputSpec.addFormat (o : OutputSpec) (f : String) : OutputSpec :=
  { o with formats := if o.formats.contains f then o.formats else o.formats.push f }

public theorem OutputSpec.addFormat_nodup (o : OutputSpec) (f : String)
    (h : o.formats.toList.Nodup) : (o.addFormat f).formats.toList.Nodup := by
  unfold addFormat
  split
  · exact h
  · next hc =>
    rw [Array.toList_push]
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_singleton] at hy
    apply hc
    subst hy
    subst hxy
    simpa [Array.contains_iff_mem] using hx

/-- One profile onto the set, dedup by name. -/
public def OutputSpec.addProfile (o : OutputSpec) (p : String) : OutputSpec :=
  { o with profiles := if o.profiles.contains p then o.profiles else o.profiles.push p }

public theorem OutputSpec.addProfile_nodup (o : OutputSpec) (p : String)
    (h : o.profiles.toList.Nodup) : (o.addProfile p).profiles.toList.Nodup := by
  unfold addProfile
  split
  · exact h
  · next hc =>
    rw [Array.toList_push]
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_singleton] at hy
    apply hc
    subst hy
    subst hxy
    simpa [Array.contains_iff_mem] using hx

/-- A declared output intent: its ICC profile file and the registry entry naming the printing
condition the profile characterizes. -/
public structure OutputIntent where
  profile : String := ""
  condition : Option String := none
  info : Option String := none
  registry : Option String := none
  components : Option Nat := none
  /-- Where the document names the profile. -/
  span : Option Span := none
  deriving Repr, BEq, Inhabited

/-- The class label macro of an itemize level, `labelitemi` for the first. -/
public def itemLabelName (level : Nat) : String :=
  let numeral := match level with
    | 1 => "i"
    | 2 => "ii"
    | 3 => "iii"
    | _ => "iv"
  "labelitem" ++ numeral

/-- The description l3pdfmeta gives a profile of the colorprofiles package that a document names
without describing it (l3pdfmeta.dtx, `c__pdfmeta_colorprofile_…`). -/
public def OutputIntent.builtin? (file : String) : Option OutputIntent :=
  match file with
  | "sRGB.icc" =>
    some { profile := file, condition := some "IEC sRGB"
           info := some "IEC 61966-2.1 Default RGB colour space - sRGB"
           registry := some "http://www.iec.ch", components := some 3 }
  | "FOGRA39L_coated.icc" =>
    some { profile := file, condition := some "FOGRA39L Coated"
           info := some ("Offset printing, according to ISO 12647-2:2004/Amd 1, OFCOM, paper type " ++
             "1 or 2 = coated art, 115 g/m2, tone value increase curves A (CMY) and B (K)")
           registry := some "http://www.fogra.org", components := some 4 }
  | _ => none

/-- An intent as the file describes it: what the document declares, the rest of a profile
l3pdfmeta describes from its description. -/
public def OutputIntent.described (oi : OutputIntent) : OutputIntent :=
  match OutputIntent.builtin? oi.profile with
  | some b => { oi with condition := oi.condition <|> b.condition, info := oi.info <|> b.info
                        registry := oi.registry <|> b.registry
                        components := oi.components <|> b.components }
  | none => oi

/-- Document metadata, as declared by `\pdfmeta`: the one record every surface derives from. -/
public structure Meta where
  title : Option String := none
  author : Option String := none
  subject : Option String := none
  keywords : Option String := none
  /-- The document's canonical URL: `<link rel="canonical">` and `og:url` in
  HTML, `dc:identifier` in the PDF's XMP. -/
  url : Option String := none
  /-- A representative image for link previews: `og:image`. -/
  image : Option String := none
  /-- The page icon: `<link rel="icon">`. -/
  favicon : Option String := none
  /-- The document's main language, a BCP 47 tag, from babel's options or
  `\pdfmeta{ language = .. }`. -/
  language : Option String := none
  /-- The PDF version the document declares
  (`\DocumentMetadata{ pdfversion = 1.7 }` or
  `\pdfmeta{ version = "1.7" }`). -/
  pdfVersion : Option String := none
  /-- Where the document declares its PDF version. -/
  versionSpan : Option Span := none
  /-- Where the document declares its trapping unknown, which PDF/X does not admit. -/
  trappedUnknownAt : Option Span := none
  /-- The PDF/X standard the document declares, which the file claims only where it meets it. -/
  pdfx : Option String := none
  /-- The printing condition the document's colours are meant for (ISO 32000-2 §14.11.5). -/
  intent : Option OutputIntent := none
  /-- The file's creation and modification dates, as declared. -/
  created : Option String := none
  modified : Option String := none
  /-- Whether the document declares itself trapped for press. -/
  trapped : Option Bool := none
  /-- Whether the PDF outline bookmarks the headings (hyperref's `bookmarks`). -/
  outline : Option Bool := none
  /-- Whether the outline's subtrees stand open (hyperref's `bookmarksopen`). -/
  outlineOpen : Option Bool := none
  /-- Whether a bookmark leads with its heading's number (hyperref's `bookmarksnumbered`). -/
  outlineNumbered : Option Bool := none
  /-- The page mode a viewer opens the file in (ISO 32000-2 Table 29; hyperref's `pdfpagemode`). -/
  pageMode : Option String := none
  deriving Repr, BEq, Inhabited

/-- The page modes a catalog may name (ISO 32000-2 Table 29). -/
public def pageModes : List String :=
  ["UseNone", "UseOutlines", "UseThumbs", "FullScreen", "UseOC", "UseAttachments"]

/-- The PDF version the file is written in: the 1.6 a PDF/X standard is defined on under its
claim, else as declared. -/
@[expose] public def Meta.writtenVersion (m : Meta) : Option String :=
  if m.pdfx.isSome then some "1.6" else m.pdfVersion

/-- The document's main locale: the declared language when a record ships for
it, English otherwise. -/
public def Meta.locale (m : Meta) : Locale :=
  (m.language.bind Locale.forTag).getD Locale.en

/-- The OpenType features both backends apply, one record. -/
public structure Features where
  kern : Bool := true
  deriving Repr, BEq, Inhabited

public def features : Features := {}

public inductive CmpOp where
  | eq
  | ne
  | le
  | lt
  | ge
  | gt
  deriving Repr, BEq, Inhabited

public def CmpOp.label : CmpOp → String
  | .eq => "=="
  | .ne => "!="
  | .le => "<="
  | .lt => "<"
  | .ge => ">="
  | .gt => ">"

public def CmpOp.holds : CmpOp → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .le, a, b => a ≤ b
  | .lt, a, b => a < b
  | .ge, a, b => a ≥ b
  | .gt, a, b => a > b

/-- A layout invariant the engine checks against what it actually shipped. -/
public inductive AssertKind where
  | pages (op : CmpOp) (n : Int)
  | fontsAllEmbedded
  /-- Every piece of ink inside the margins. -/
  | textInArea
  /-- The smallest x-height set anywhere is at least this, judged from each
  run's font at its size. -/
  | minXHeight (min : Length)
  /-- The document conforms to the engine's judged WCAG 2.2 AA rows and declares a language. -/
  | accessibilityAA
  /-- The PDF satisfies the named conformance profile, judged on the census of
  the built bytes; implied by `\output{ profiles = <name> }`. -/
  | pdfProfile (name : String)
  deriving Repr, BEq, Inhabited

public def AssertKind.source : AssertKind → String
  | .pages op n => s!"pages {op.label} {n}"
  | .fontsAllEmbedded => "fonts.all_embedded"
  | .textInArea => "text.in_area"
  | .minXHeight m => s!"text.xheight >= {m.toPtString}pt"
  | .accessibilityAA => "accessibility = AA"
  | .pdfProfile name => s!"pdf.profile = {name}"

/-- The emitted artifacts an assertion is judged on, in `OutputSpec.formats`'
vocabulary; empty reads no artifact. -/
public def AssertKind.reads : AssertKind → Array String
  | .pages _ _ => #[]
  | .fontsAllEmbedded => #["pdf", "html"]
  | .textInArea => #[]
  | .minXHeight _ => #[]
  | .accessibilityAA => #[]
  | .pdfProfile _ => #["pdf"]

public theorem assert_reads_shipped :
    (∀ k : AssertKind, k.reads ≠ #[] ↔ k = .fontsAllEmbedded ∨ ∃ n, k = .pdfProfile n) ∧
    AssertKind.reads .fontsAllEmbedded = #["pdf", "html"] ∧
    ∀ n, AssertKind.reads (.pdfProfile n) = #["pdf"] := by
  refine ⟨fun k => ?_, rfl, fun _ => rfl⟩
  cases k <;> simp [AssertKind.reads]

public structure Assertion where
  kind : AssertKind
  span : Option Span := none
  /-- Guidance shown when the assertion fails. -/
  help : Option String := none
  /-- The census key of the setting that implies it. -/
  subject : Option String := none
  deriving Repr, BEq, Inhabited

/-- The weight axis: the nine NFSS series values. -/
public inductive Weight where
  | ul | el | l | sl | m | sb | b | eb | ub
  deriving Repr, BEq, DecidableEq

public instance : Inhabited Weight := ⟨.m⟩

/-- The CSS/OpenType numeric value of each series (CSS Fonts 4 §2.2, OS/2 `usWeightClass`). -/
public def Weight.css : Weight → Nat
  | .ul => 100
  | .el => 200
  | .l => 300
  | .sl => 350
  | .m => 400
  | .sb => 600
  | .b => 700
  | .eb => 800
  | .ub => 900

/-- Every series, in weight order. -/
public def Weight.all : List Weight := [.ul, .el, .l, .sl, .m, .sb, .b, .eb, .ub]

/-- The series nearest a numeric weight, ties to the lighter. -/
public def Weight.ofCss (n : Nat) : Weight :=
  (Weight.all.foldl (init := Weight.ul) fun best w =>
    let d := fun v : Weight => max v.css n - min v.css n
    if d w < d best then w else best)

/-- The NFSS spelling of each series, `\fontseries`'s vocabulary. -/
public def Weight.series : Weight → String
  | .ul => "ul"
  | .el => "el"
  | .l => "l"
  | .sl => "sl"
  | .m => "m"
  | .sb => "sb"
  | .b => "b"
  | .eb => "eb"
  | .ub => "ub"

/-- The NFSS width codes, the width half of a series value (fntguide §2.2). -/
private def seriesWidthCodes : List String :=
  ["uc", "ec", "sc", "c", "sx", "ex", "ux", "x"]

/-- Parse an NFSS series value into its weight and width halves, longest weight code first. -/
public def Weight.parseSeries (s : String) : Option (Weight × String) :=
  if s == "m" then some (.m, "") else
  let codes : List Weight := [.ul, .el, .sl, .sb, .eb, .ub, .l, .b]
  match codes.find? fun w => s.startsWith w.series with
  | some w =>
    let rest := (s.drop w.series.length).toString
    if rest.isEmpty || seriesWidthCodes.contains rest then some (w, rest)
    else none
  | none =>
    if seriesWidthCodes.contains s then some (.m, s) else none

public def Weight.isBold (w : Weight) : Bool := 700 ≤ w.css

public theorem Weight.ofCss_css_id : ∀ w : Weight, ofCss w.css = w := by
  intro w; cases w <;> rfl

public inductive Style where
  | bold
  | italic
  | mono
  | smallcaps
  | emph
  | sans
  | normal
  /-- The roman family: NFSS's `\rmfamily`/`\textrm`; series and shape stand. -/
  | roman
  /-- The medium series: `\mdseries`/`\textmd`, turning bold off. -/
  | medium
  /-- A series other than bold or medium, as `\fontseries{l}` selects. -/
  | series (w : Weight)
  /-- The upright shape: `\upshape`/`\textup`, clearing italic and small caps. -/
  | upright
  /-- A family the document declared beside the three slots, by its slot; series and shape stand. -/
  | family (slot : Nat)
  | size (name : String)
  /-- `\fontsize{size}{leading}\selectfont`, both dimensions affine until the
  run's measure and font metrics are known. -/
  | fontSize (size leading : Affine Measure)
  /-- A language switch (BCP 47 tag): `\foreignlanguage`, `\selectlanguage`,
  babel's `otherlanguage`. -/
  | lang (tag : String)
  deriving Repr, BEq

/-- The LaTeX 10pt size scale (size10.clo), per mille of the surrounding size. -/
@[expose] public def sizeScale : List (String × Nat) :=
  [("tiny", 500), ("scriptsize", 700), ("footnotesize", 800), ("small", 900),
   ("normalsize", 1000), ("large", 1200), ("Large", 1440), ("LARGE", 1728),
   ("huge", 2074), ("Huge", 2488)]

public theorem sizeScale_LARGE_exact : (sizeScale.lookup "LARGE").getD 1000 = 1728 := by decide

/-- A named step of a size ladder applied to a base size; a name off the ladder is the base
itself. -/
@[expose] public def scaleStepIn (scale : List (String × Nat)) (base : Length) (name : String) : Length :=
  base * ((scale.lookup name).getD 1000) / 1000

/-- Each named step's `\baselineskip`, per mille of the body size:
size10.clo's `\@setfontsize` second arguments. -/
@[expose] public def sizeSkipScale : List (String × Nat) :=
  [("tiny", 600), ("scriptsize", 800), ("footnotesize", 950), ("small", 1100),
   ("normalsize", 1200), ("large", 1400), ("Large", 1800), ("LARGE", 2200),
   ("huge", 2500), ("Huge", 3000)]

/-- The `\normalsize` row of a skip column, per mille of the body size: 1200
off the column, and never below one. -/
@[expose] public def skipBody (skips : List (String × Nat)) : Nat :=
  max 1 ((skips.lookup "normalsize").getD 1200)

/-- A named step's leading at a base: the base's leading in the proportion the
skip column gives the step's row to its `\normalsize` row. -/
@[expose] public def stepLead (skips : List (String × Nat)) (step : String) (base : Length) :
    Option Length :=
  (skips.lookup step).map fun (l : Nat) => leadingFor base * (l : Int) / (skipBody skips : Int)

/-- The baseline distance a run sets at: its named step's leading, else the
6⁄5 rule of its own size. -/
@[expose] public def stepSkip (lead : Option Length) (size : Length) (factor : Nat := 1000) : Length :=
  match lead with
  | some l => l * factor / 1000
  | none => leadingFor size factor

@[simp] public theorem stepSkip_none_exact (size : Length) (factor : Nat) :
    stepSkip none size factor = leadingFor size factor := rfl

/-- The leading a run's line box takes: its paragraph's leading, in the run's
proportion to the paragraph's size. -/
@[expose] public def runLead (lead : Option Length) (nominal size : Length) (factor : Nat := 1000) :
    Length :=
  match lead with
  | some l => l.mulDiv size (max nominal Length.quantum) * (factor : Int) / (1000 : Int)
  | none => leadingFor size factor

public theorem runLead_exact (lead : Option Length) (nominal : Length) (h : 0 < nominal)
    (factor : Nat) : runLead lead nominal nominal factor = stepSkip lead nominal factor := by
  cases lead with
  | none => rfl
  | some l =>
    have hm : max nominal Length.quantum = nominal := by length_omega
    have hn : nominal.units ≠ 0 := by length_omega
    simp only [runLead, stepSkip, hm]
    length_units
    rw [Int.mul_ediv_cancel _ hn]
    rfl

public theorem runLead_monotone (lead : Option Length) (nominal : Length) (factor : Nat)
    (a b : Length) (hl : ∀ l, lead = some l → 0 ≤ l) (hab : a ≤ b) :
    runLead lead nominal a factor ≤ runLead lead nominal b factor := by
  have hf : (0 : Int) ≤ (factor : Int) := Int.natCast_nonneg _
  cases lead with
  | none =>
    simp only [runLead, leadingFor]
    length_units
    apply Int.ediv_le_ediv (by decide)
    apply Int.mul_le_mul_of_nonneg_right _ hf
    apply Int.ediv_le_ediv (by decide)
    exact Int.mul_le_mul_of_nonneg_right hab (by decide)
  | some l =>
    have h0 := hl l rfl
    simp only [runLead]
    length_units
    apply Int.ediv_le_ediv (by decide)
    apply Int.mul_le_mul_of_nonneg_right _ hf
    apply Int.ediv_le_ediv (by omega)
    exact Int.mul_le_mul_of_nonneg_left hab h0

public theorem runLead_between (lead : Option Length) (nominal : Length) (factor : Nat)
    (s : Length)
    (hn : 0 < nominal) (hl : ∀ l, lead = some l → 0 ≤ l) (hs : 0 ≤ s) (hsn : s ≤ nominal) :
    0 ≤ runLead lead nominal s factor ∧
      runLead lead nominal s factor ≤ stepSkip lead nominal factor := by
  have h0 : runLead lead nominal 0 factor = 0 := by
    cases lead <;> simp [runLead, leadingFor, Length.ext_iff']
  refine ⟨?_, ?_⟩
  · rw [← h0]
    exact runLead_monotone lead nominal factor 0 s hl hs
  · rw [← runLead_exact lead nominal hn factor]
    exact runLead_monotone lead nominal factor s nominal hl hsn

public theorem sizeSkipScale_names_exact :
    sizeSkipScale.map (·.1) = sizeScale.map (·.1) := by decide

public theorem sizeSkipScale_between :
    ∀ p ∈ sizeScale, ∀ q ∈ sizeSkipScale, p.1 = q.1 →
      8 * p.2 ≤ 7 * q.2 ∧ 7 * q.2 ≤ 9 * p.2 := by decide

public theorem stepLead_ratio_between (skips : List (String × Nat)) (step : String)
    (base : Length) (k : Nat) (hk : skips.lookup step = some k) :
    ∃ l, stepLead skips step base = some l ∧
      l * (skipBody skips : Int) ≤ leadingFor base * (k : Int) ∧
      leadingFor base * (k : Int) < (l + Length.quantum) * (skipBody skips : Int) := by
  have hn : (0 : Int) < (skipBody skips : Int) := by
    have : 1 ≤ skipBody skips := Nat.le_max_left _ _
    omega
  refine ⟨leadingFor base * (k : Int) / (skipBody skips : Int), ?_, ?_, ?_⟩
  · simp [stepLead, hk]
  · length_units; exact Int.ediv_mul_le _ (Int.ne_of_gt hn)
  · length_units; exact Int.lt_ediv_add_one_mul_self _ hn

public theorem stepLead_between (base : Length) (hb : 100 * Length.quantum ≤ base) :
    ∀ p ∈ sizeScale, ∃ l, stepLead sizeSkipScale p.1 base = some l ∧
      scaleStepIn sizeScale base p.1 < l ∧
        7 * l ≤ 9 * scaleStepIn sizeScale base p.1 + 9 * Length.quantum := by
  intro p hp
  have hb' : 100 ≤ base.units := by length_omega
  simp only [sizeScale, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp only [stepLead, scaleStepIn, skipBody, sizeSkipScale, sizeScale, List.lookup,
      leadingFor, leadingMilli] <;> simp <;> length_units <;> omega

public theorem stepSkip_normalsize_exact (skips : List (String × Nat)) (n : Nat)
    (hn : skips.lookup "normalsize" = some n) (hpos : 1 ≤ n) (body : Length) (factor : Nat) :
    stepSkip (stepLead skips "normalsize" body) body factor = leadingFor body factor := by
  have hb : skipBody skips = n := by
    simp only [skipBody, hn, Option.getD_some]
    omega
  have hn0 : (n : Int) ≠ 0 := by omega
  have hl : stepLead skips "normalsize" body = some (leadingFor body) := by
    simp only [stepLead, hn, hb, Option.map, Option.some.injEq]
    length_units
    rw [Int.mul_ediv_cancel _ hn0]
  rw [hl]
  simp only [stepSkip, leadingFor, leadingMilli]
  length_units
  have h1000 : ∀ b : Int, b * ((1200 : Nat) : Int) / 1000 * ((1000 : Nat) : Int) / 1000 =
      b * ((1200 : Nat) : Int) / 1000 := by intro b; omega
  rw [h1000]
  rfl

/-- A skip column with one row replaced; a name off the column leaves it as it was. -/
public def setSkip (skips : List (String × Nat)) (name : String) (row : Nat) :
    List (String × Nat) :=
  skips.map fun p => if p.1 == name then (p.1, row) else p

/-- A declared length's per-mille share of the body size, rounded, the length
given a thousandfold. -/
public def skipRowOf (milli body : Length) : Nat :=
  ((milli + body / 2) / max body Length.quantum).toNat

public theorem skipRowOf_between (milli body : Length) (hs : 0 ≤ milli) (hb : 0 < body) :
    (skipRowOf milli body : Int) * body ≤ milli + body / 2 ∧
      milli + body / 2 < ((skipRowOf milli body : Int) + 1) * body := by
  have hm : max body Length.quantum = body := by length_omega
  have hb' : 0 < body.units := hb
  have hq : (0 : Int) ≤ (milli + body / 2) / body := by
    length_units; exact Int.ediv_nonneg (by omega) (by omega)
  simp only [skipRowOf, hm, Int.toNat_of_nonneg hq]
  length_units
  exact ⟨Int.ediv_mul_le _ (Int.ne_of_gt hb'), Int.lt_ediv_add_one_mul_self _ hb'⟩

/-- The size a document title sets at when no `titlepage` font template
declares one: `\LARGE` on a flow page, `\Large` on a deck, on the document's ladder. -/
@[expose] public def titleSize (scale : List (String × Nat)) (base : Length) (slides : Bool) : Length :=
  scaleStepIn scale base (if slides then "Large" else "LARGE")

@[expose] public def inkClearance : Length := Dim.pt 1 -- TeXbook p.78: `\lineskip=1pt`, TeX's own floor

/-- Heading display sizes from the type scale: `\section` in `\Large`,
`\subsection` in `\large`, `\subsubsection` in `\normalsize`. -/
@[expose] public def headingSize (scale : List (String × Nat)) (base : Length) : HeadingLevel → Length
  | .title | .h1 => scaleStepIn scale base "LARGE"
  | .h2 => scaleStepIn scale base "Large"
  | .h3 => scaleStepIn scale base "large"
  | .h4 | .h5 | .h6 => base

/-- The reach below its bar's top of the section-page template's last line,
the subsection title's strut, at the document's `\large`. -/
public def sectionPageStrut (scale : List (String × Nat)) (size : Length) (factor : Nat := 1000) :
    Length :=
  leadingFor (scaleStepIn scale size "large") factor * 13 / 10

public theorem sectionPageStrut_between (size : Length) :
    size.mulDiv (sectionPageStrut sizeScale (1000 * Length.quantum)) (1000 * Length.quantum)
        - 4 * Length.quantum ≤ sectionPageStrut sizeScale size ∧
      sectionPageStrut sizeScale size ≤
        size.mulDiv (sectionPageStrut sizeScale (1000 * Length.quantum)) (1000 * Length.quantum) := by
  have hL : ((sizeScale.lookup "large").getD 1000 : Nat) = 1200 := by decide
  have hs : ∀ x : Length, (sectionPageStrut sizeScale x).units =
      x.units * 1200 / 1000 * 1200 / 1000 * 1000 / 1000 * 13 / 10 := by
    intro x
    simp only [sectionPageStrut, leadingFor, scaleStepIn, leadingMilli, hL]
    length_units
    rfl
  length_units
  rw [hs, hs]
  simp only [Length.units_nmul, Length.units_quantum]
  omega

/-- Adjacent steps of the scale, in order. -/
public def sizeScaleSteps : List (Nat × Nat) :=
  (sizeScale.map (·.2)).zip (sizeScale.map (·.2)).tail

public theorem sizeScale_monotone : ∀ p ∈ sizeScaleSteps, p.1 < p.2 := by decide

public theorem sizeScale_ratio_band :
    ∀ p ∈ sizeScaleSteps, 10 * p.1 ≤ 9 * p.2 ∧ 5 * p.2 ≤ 7 * p.1 := by decide

public theorem sizeScale_normalsize : sizeScale.lookup "normalsize" = some 1000 := by decide

public theorem sizeScale_display_geometric :
    ∀ p ∈ sizeScaleSteps, 1000 ≤ p.1 →
      6 * p.1 ≤ 5 * p.2 + 4 ∧ 5 * p.2 ≤ 6 * p.1 + 4 := by decide

public theorem card_floor_within_scale :
    ∀ p ∈ sizeScale, 800 ≤ p.2 →
      baseFontSize * (p.2 : Int) / 1000 / 2 ≥ cardXHeightFloor := by decide

public theorem poster_floor_within_scale :
    ∀ p ∈ sizeScale, 900 ≤ p.2 →
      posterFontSize * (p.2 : Int) / 1000 / 2 ≥ posterXHeightFloor := by decide

/-- Whether a ladder never decreases in its named order. -/
public def stepsOrdered (scale : List (String × Nat)) : Bool :=
  ((scale.map (·.2)).zip (scale.map (·.2)).tail).all fun p => p.1 ≤ p.2

public theorem sizeScale_stepsOrdered : stepsOrdered sizeScale = true := by decide

/-- Replace one named step of a ladder, per mille of the body; `none` when the
name is off the ladder or the ladder would no longer be ordered. -/
public def setStep (scale : List (String × Nat)) (name : String) (f : Nat) :
    Option (List (String × Nat)) :=
  if (scale.lookup name).isNone then none
  else
    let s' := scale.map fun p => if p.1 == name then (p.1, f) else p
    if stepsOrdered s' then some s' else none

public theorem size_ladder_monotone (scale : List (String × Nat)) (name : String)
    (f : Nat) (s' : List (String × Nat)) (h : setStep scale name f = some s') :
    stepsOrdered s' = true := by
  unfold setStep at h
  split at h
  · exact absurd h (by simp)
  · dsimp only at h
    split at h
    next hm => injection h with h'; subst h'; exact hm
    next => exact absurd h (by simp)

/-- Replace several named steps at once, judged as one ladder. -/
public def setStepsAll (scale : List (String × Nat)) (steps : List (String × Nat)) :
    Option (List (String × Nat)) :=
  let s' := scale.map fun q => match steps.lookup q.1 with
    | some f => (q.1, f)
    | none => q
  if stepsOrdered s' then some s' else none

public theorem size_ladder_monotone_all (scale steps : List (String × Nat))
    (s' : List (String × Nat)) (h : setStepsAll scale steps = some s') :
    stepsOrdered s' = true := by
  unfold setStepsAll at h
  dsimp only at h
  split at h
  next hm => injection h with h'; subst h'; exact hm
  next => exact absurd h (by simp)

/-- The size ladder in force for a document: its own, read from a venue's size
commands, or the engine's scale. -/
public def PageSpec.scale (p : PageSpec) : List (String × Nat) :=
  p.sizes.getD sizeScale

/-- The skip column in force for a document: its own, or size10.clo's. -/
public def PageSpec.skipScale (p : PageSpec) : List (String × Nat) :=
  p.skips.getD sizeSkipScale

public def Style.label : Style → String
  | .bold => "bold"
  | .italic => "italic"
  | .mono => "mono"
  | .smallcaps => "smallcaps"
  | .emph => "emph"
  | .sans => "sans"
  | .normal => "normal"
  | .roman => "roman"
  | .medium => "medium"
  | .series w => s!"series:{w.series}"
  | .upright => "upright"
  | .family n => s!"family:{n}"
  | .size n => s!"size:{n}"
  | .fontSize _ _ => "fontsize"
  | .lang tag => s!"lang:{tag}"


/-- What a resolved cross-reference renders: `\ref`'s bare number, `\eqref`'s
parenthesised one, a cleveref form, or a blueprint's statement heading and number. -/
public inductive RefForm where
  | plain
  | paren
  | cref (cap : Bool)
  | crefRange (cap : Bool)
  | labelOnly
  | name (cap : Bool)
  | headed
  /-- hyperref's `\nameref`: the title of what the label names. -/
  | title
  /-- `\pageref`: the folio of the page its label lands on, once a setting places it. -/
  | page
  /-- hyperref's starred form: as its form, without the link. -/
  | starred (form : RefForm)
  deriving Repr, BEq

/-- Whether a reference form prints a title, starred or not. -/
public def RefForm.titled : RefForm → Bool
  | .title => true
  | .starred f => f.titled
  | .plain | .paren | .cref _ | .crefRange _ | .labelOnly | .name _ | .headed | .page => false

/-- Whether a reference form prints its label's page, starred or not. -/
public def RefForm.paged : RefForm → Bool
  | .page => true
  | .starred f => f.paged
  | .plain | .paren | .cref _ | .crefRange _ | .labelOnly | .name _ | .headed | .title => false

/-- Whether a reference form links to its target: every form but a starred one. -/
public def RefForm.linked : RefForm → Bool
  | .starred _ => false
  | .plain | .paren | .cref _ | .crefRange _ | .labelOnly | .name _ | .headed | .title | .page => true

/-- A reference form as the IR dump spells it, a starred one with its star. -/
public def RefForm.spelling : RefForm → String
  | .plain => "ref"
  | .paren => "eqref"
  | .cref false => "cref"
  | .cref true => "Cref"
  | .crefRange false => "crefrange"
  | .crefRange true => "Crefrange"
  | .labelOnly => "labelcref"
  | .name false => "namecref"
  | .name true => "nameCref"
  | .headed => "headed"
  | .title => "nameref"
  | .page => "pageref"
  | .starred f => f.spelling ++ "*"

/-- What a field citation prints of its entry instead of its label (biblatex manual §3.8.4). -/
public inductive CiteField where
  | title
  | url
  | date
  | full
  deriving Repr, BEq, Inhabited

/-- The natbib command a citation was written with, which sets the parts that
print and whether brackets wrap them. -/
public inductive CiteCmd where
  | textual
  | paren
  | auto
  | alt
  | alp
  | author
  | year
  | yearPar
  | num
  | text
  | nocite
  /-- One citation bracket: natbib's `\NAT@open` when `opening`, else `\NAT@close`. -/
  | bracket (opening : Bool)
  /-- natbib's `\NAT@cmt`: the separator before a post-note set apart from its works. -/
  | noteSep
  | field (f : CiteField)
  deriving Repr, BEq, Inhabited

/-- What a citation declares beside its keys: the command, the starred and
capitalized forms, and the optional notes. -/
public structure CiteForm where
  cmd : CiteCmd
  full : Bool := false
  up : Bool := false
  pre : String := ""
  post : String := ""
  deriving Repr, BEq, Inhabited

/-- Where a key is first cited, shown or listed only (`\nocite`), and the surface whose spelling
cited it, which the reporting layer reads beside the span-free document. -/
public structure CiteSite where
  key : String
  span : Span
  surface : Surface
  nocite : Bool
  deriving Repr, BEq

/-- natbib's citation commands, each with the form it selects. -/
public def natbibCites : List (String × CiteForm) :=
  [("citet", { cmd := .textual }), ("citep", { cmd := .paren }),
   ("cite", { cmd := .auto }), ("citealt", { cmd := .alt }),
   ("citealp", { cmd := .alp }), ("citeauthor", { cmd := .author }),
   ("citefullauthor", { cmd := .author, full := true }),
   ("citeyear", { cmd := .year }), ("citeyearpar", { cmd := .yearPar }),
   ("citenum", { cmd := .num }), ("citetext", { cmd := .text }),
   ("nocite", { cmd := .nocite }),
   ("Citet", { cmd := .textual, up := true }), ("Citep", { cmd := .paren, up := true }),
   ("Citealt", { cmd := .alt, up := true }), ("Citealp", { cmd := .alp, up := true }),
   ("Citeauthor", { cmd := .author, up := true }),
   ("citetitle", { cmd := .field .title }), ("citeurl", { cmd := .field .url }),
   ("citedate", { cmd := .field .date }), ("fullcite", { cmd := .field .full })]

/-- The command a form spells back as; a bracket mark as the natbib macro it
is. -/
public def CiteForm.command (f : CiteForm) : String :=
  if let .bracket o := f.cmd then (if o then "NAT@open" else "NAT@close")
  else if f.cmd == .noteSep then "NAT@cmt"
  else ((natbibCites.find? fun (_, g) => g.cmd == f.cmd && g.up == f.up).map (·.1)).getD "cite"

/-- The weight a style selects, when it touches the axis. -/
@[expose] public def Style.weight? : Style → Option Weight
  | .bold => some .b
  | .medium => some .m
  | .series w => some w
  | .normal => some .m
  | _ => none

/-- What an unresolved citation shows for each key, as LaTeX renders an undefined citation. -/
public def citeMark : String := "?"

/-- The text an unresolved citation shows: one mark per key, comma separated. -/
public def citeMarks (keys : Array String) : String :=
  String.intercalate ", " (keys.toList.map fun _ => citeMark)

/-- One run of a text alternative: words, or a citation its bibliography sets, with the text its
style prints once the list is read. -/
public inductive AltRun where
  | text (s : String)
  | cite (form : CiteForm) (keys : Array String) (ink : Option String)
  deriving Repr, BEq, Inhabited

/-- What a run of an alternative says: its words, or its citation's text, its marks unset. -/
public def AltRun.said : AltRun → String
  | .text s => s
  | .cite _ keys ink => ink.getD (citeMarks keys)

/-- The text alternative a non-text object declares (WCAG 2.2 SC 1.1.1, ISO 32000-2 §14.9.3). -/
public inductive Alt where
  | undeclared
  | decorative
  | described (text : String)
  /-- An alternative holding citations, which the reference list sets. -/
  | citing (runs : Array AltRun)
  deriving Repr, BEq, Inhabited

/-- A described alternative from text; blank text stays `.undeclared`. -/
public def Alt.declare (s : String) : Alt :=
  if s.trimAscii.toString.isEmpty then .undeclared else .described s.trimAscii.toString

/-- The text an alternative carries: a described one's, a citing one's runs as they stand, `""` for
an undeclared or decorative one. -/
public def Alt.text : Alt → String
  | .described t => t
  | .citing runs => String.join (runs.toList.map AltRun.said)
  | .undeclared | .decorative => ""

/-- The citations an alternative holds, each with its form and keys. -/
public def Alt.cites : Alt → Array (CiteForm × Array String)
  | .citing runs => runs.filterMap fun r => match r with
    | .cite form keys _ => some (form, keys)
    | .text _ => none
  | .undeclared | .decorative | .described _ => #[]

/-- The keys of a run's citation whose text no list has set. -/
@[expose] public def AltRun.pending : AltRun → Array String
  | .cite _ keys none => keys
  | .cite _ _ (some _) | .text _ => #[]

/-- The keys of an alternative's citations whose text no list has set. -/
@[expose] public def Alt.pendingKeys : Alt → Array String
  | .citing runs => runs.flatMap AltRun.pending
  | .undeclared | .decorative | .described _ => #[]

/-- An alternative as the IR dump spells it after its node: nothing when undeclared. -/
public def Alt.dumpSuffix : Alt → String
  | .undeclared => ""
  | .decorative => " artifact"
  | .described t => s!" alt {t.quote}"
  | .citing runs => s!" alt {(String.join (runs.toList.map AltRun.said)).quote} citing"

public theorem Alt.declare_nonempty (s t : String) (h : Alt.declare s = .described t) :
    ¬ t.isEmpty := by
  unfold Alt.declare at h
  split at h
  · cases h
  · rename_i hne
    injection h with h
    subst h
    exact hne

/-- Whether a step's content is pending on page `k`: before its range starts
or past its declared end. -/
@[expose] public def stepPending (n : Nat) (last : Option Nat) (k : Nat) : Bool :=
  k < n || (match last with | some u => k > u | none => false)

/-- A nonempty union of numbered intervals; `none` is an open end. -/
public structure OverlaySpec where
  first : Nat
  last : Option Nat
  more : List (Nat × Option Nat) := []
  /-- Off its steps the carried content is invisible, its space kept, rather than covered. -/
  invisible : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

namespace OverlaySpec

@[expose] public def ranges (s : OverlaySpec) : List (Nat × Option Nat) :=
  (s.first, s.last) :: s.more

/-- Membership is disjunction, not the hull of the declared intervals. -/
@[expose] public def selects (s : OverlaySpec) (k : Nat) : Bool :=
  s.ranges.any fun (n, last) => !stepPending n last k

@[expose] public def pending (s : OverlaySpec) (k : Nat) : Bool := !s.selects k

/-- Alternation stores the step-one reading first, on either side of a union. -/
@[expose] public def showsFirst (s : OverlaySpec) (k : Nat) : Bool := s.pending k == s.pending 1

public def reachesOther (s : OverlaySpec) (steps : Nat) : Bool :=
  (List.range steps).any fun i => !s.showsFirst (i + 1)

public def start (s : OverlaySpec) : Nat := s.more.foldl (fun n r => min n r.1) s.first

/-- The frame's extent from the explicit numbered endpoints; an open end adds no page. -/
public def maxStep (s : OverlaySpec) : Nat :=
  s.more.foldl (fun n r => max n (max r.1 (r.2.getD r.1)))
    (max s.first (s.last.getD s.first))

public def union (s t : OverlaySpec) : OverlaySpec := { s with more := s.more ++ t.ranges }

/-- The selector showing where `s` shows from step `n` on: each range starting no earlier. -/
@[expose] public def fromStep (s : OverlaySpec) (n : Nat) : OverlaySpec :=
  { s with first := max s.first n, more := s.more.map fun r => (max r.1 n, r.2) }

/-- The frame's numbered steps that satisfy `p`, each once. -/
public def numberedSteps (steps : Nat) (p : Nat → Bool) : List Nat :=
  ((List.range steps).map (· + 1)).filter p

public def selectedSteps (s : OverlaySpec) (steps : Nat) : List Nat :=
  numberedSteps steps s.selects

/-- Whether invisible content hides on step `k` of a `steps`-step frame: off its steps, and never
outside a frame, where no step is set. -/
public def hidesAt (s : OverlaySpec) (k steps : Nat) : Bool := s.invisible && 0 < steps && s.pending k

/-- The numbered steps on which one arm of an alternation shows, in page-order storage. -/
public def pageSteps (s : OverlaySpec) (steps : Nat) (first : Bool) : List Nat :=
  numberedSteps steps fun k => s.showsFirst k == first

public theorem selects_exact (s : OverlaySpec) (k : Nat) :
    s.selects k = true ↔ ∃ r ∈ s.ranges, stepPending r.1 r.2 k = false := by
  simp [selects]

public theorem union_selects_exact (s t : OverlaySpec) (k : Nat) :
    (s.union t).selects k = (s.selects k || t.selects k) := by
  simp [selects, union, ranges, List.any_append, Bool.or_assoc]

private theorem fromStep_range (a n k : Nat) (b : Option Nat) :
    (!stepPending (max a n) b k) = ((!stepPending a b k) && decide (n ≤ k)) := by
  unfold stepPending
  have hm : (k < max a n) = (k < a ∨ k < n) := by
    apply propext; rw [Nat.max_def]; split <;> omega
  cases b with
  | none =>
    simp only [hm, Bool.or_false]
    by_cases h2 : k < a <;> by_cases h3 : n ≤ k <;> (simp [h2, h3]; try omega)
  | some u =>
    simp only [hm]
    by_cases h2 : k < a <;> by_cases h3 : n ≤ k <;> by_cases h4 : k > u <;>
      (simp [h2, h3, h4]; try omega)

public theorem fromStep_selects_exact (s : OverlaySpec) (n k : Nat) :
    (s.fromStep n).selects k = (s.selects k && decide (n ≤ k)) := by
  have hl : ∀ l : List (Nat × Option Nat),
      (l.map fun r => (max r.1 n, r.2)).any (fun r => !stepPending r.1 r.2 k) =
        (l.any (fun r => !stepPending r.1 r.2 k) && decide (n ≤ k)) := by
    intro l
    induction l with
    | nil => simp
    | cons r rest ih =>
      rw [List.map_cons, List.any_cons, List.any_cons, ih, fromStep_range]
      cases (!stepPending r.1 r.2 k) <;> cases decide (n ≤ k) <;> simp
  have hf := fromStep_range s.first n k s.last
  simp only [selects, ranges, fromStep, List.any_cons] at hl ⊢
  rw [hf, hl]
  cases (!stepPending s.first s.last k) <;> cases decide (n ≤ k) <;> simp

public theorem union_self_id (s : OverlaySpec) (k : Nat) :
    (s.union s).selects k = s.selects k := by
  simp [union_selects_exact]

public theorem union_comm_agree (s t : OverlaySpec) (k : Nat) :
    (s.union t).selects k = (t.union s).selects k := by
  simp [union_selects_exact, Bool.or_comm]

public theorem pending_nested_exact (s t : OverlaySpec) (k : Nat) :
    (s.pending k || t.pending k) = !(s.selects k && t.selects k) := by
  simp [pending, Bool.not_and]

@[simp] public theorem singleton_pending_exact (n : Nat) (last : Option Nat) (k : Nat) :
    (OverlaySpec.mk n last [] false).pending k = stepPending n last k := by
  simp [pending, selects, ranges]

public theorem showsFirst_id (s : OverlaySpec) : s.showsFirst 1 = true := by
  simp [showsFirst]

/-- Alternatives in first-page order, whichever side of the selector contains step one. -/
public def pageOrder {α : Type} (s : OverlaySpec) (active otherwise : α) : α × α :=
  if s.pending 1 then (otherwise, active) else (active, otherwise)

public theorem pageOrder_select_exact {α : Type} (s : OverlaySpec) (k : Nat)
    (active otherwise : α) :
    (if s.showsFirst k then (s.pageOrder active otherwise).1
      else (s.pageOrder active otherwise).2) =
      (if s.selects k then active else otherwise) := by
  by_cases hk : s.selects k = true <;> by_cases hfirst : s.selects 1 = true <;>
    simp_all [pageOrder, showsFirst, pending]

public theorem numberedSteps_mem (steps k : Nat) (p : Nat → Bool) :
    k ∈ numberedSteps steps p ↔ 1 ≤ k ∧ k ≤ steps ∧ p k = true := by
  simp only [numberedSteps, List.mem_filter, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hs⟩
    exact ⟨by omega, by omega, hs⟩
  · rintro ⟨h1, h2, hs⟩
    exact ⟨⟨k - 1, by omega, by omega⟩, hs⟩

public theorem numberedSteps_contract (steps : Nat) (p : Nat → Bool) :
    (numberedSteps steps p).Nodup := by
  apply List.Pairwise.filter
  apply List.Pairwise.map (R := fun a b : Nat => a ≠ b) (fun n : Nat => n + 1)
  · intro a b h
    omega
  · exact List.nodup_range

public theorem selectedSteps_mem (s : OverlaySpec) (steps k : Nat) :
    k ∈ s.selectedSteps steps ↔ 1 ≤ k ∧ k ≤ steps ∧ s.selects k = true :=
  numberedSteps_mem steps k s.selects

public theorem pageSteps_mem (s : OverlaySpec) (steps k : Nat) (first : Bool) :
    k ∈ s.pageSteps steps first ↔
      1 ≤ k ∧ k ≤ steps ∧ s.showsFirst k = first := by
  simp [pageSteps, numberedSteps_mem]

public theorem pageSteps_partition_contract (s : OverlaySpec) (steps k : Nat)
    (hk : 1 ≤ k) (hsteps : k ≤ steps) :
    ((s.pageSteps steps true).contains k || (s.pageSteps steps false).contains k) = true ∧
    ((s.pageSteps steps true).contains k && (s.pageSteps steps false).contains k) = false := by
  simp only [List.contains_eq_mem, pageSteps_mem, hk, hsteps, true_and]
  cases s.showsFirst k <;> decide

end OverlaySpec

public inductive Decoration where
  | underline
  | lineThrough
  /-- A mark behind the text, breaking with it across lines: the ground's colour and its palette
  name. -/
  | highlight (color : Color) (name : Option ColorRef)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Whether a decoration is a mark, painted under its text rather than over
it. -/
@[expose] public def Decoration.isMark : Decoration → Bool
  | .underline | .lineThrough => false
  | .highlight _ _ => true

/-- A length a box's dimension may name: a page measure, or its content's natural height, depth,
width or total height (LaTeX's `\height`, `\depth`, `\width`, `\totalheight`). -/
public inductive BoxMeasure where
  | page (m : Measure)
  | height
  | depth
  | width
  | totalHeight
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The paint of a box's frame: the text's colour, or a declared colour and its palette name. -/
public inductive BoxPaint where
  | ink
  | color (c : Color) (name : Option ColorRef)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The box commands, each setting its content in one `InlineBox`. -/
public def boxCommands : List String := ["raisebox", "colorbox", "fcolorbox", "fbox"]

/-- The box LaTeX's `\raisebox`, `\colorbox`, `\fcolorbox` and `\fbox` set their content in:
unbreakable at its natural width, `raise` above the baseline, its height and depth the declared ones
where given, padded by `pad` on a `ground` and inside a `frame` `rule` wide where declared. -/
public structure InlineBox where
  raise : Affine BoxMeasure
  height : Option (Affine BoxMeasure)
  depth : Option (Affine BoxMeasure)
  ground : Option (Color × Option ColorRef)
  frame : Option BoxPaint
  pad : SymGlue
  rule : SymGlue
  deriving Repr, BEq, DecidableEq, Inhabited

public inductive Inline where
  | text (s : String)
  | math (display : Bool) (src : String)
  /-- An elaborated formula: atoms with TeX's classes and scripts, with its
  source `src` carried whole. -/
  | formula (display : Bool) (src : String) (body : Math.MList)
  | styled (style : Style) (body : Array Inline)
  /-- `name` is the palette entry the colour came from, when it had one. -/
  | colored (color : Color) (name : Option ColorRef) (body : Array Inline)
  /-- Diagnostic provenance only: every semantic reading traverses `body` unchanged. -/
  | located (span : Span) (body : Array Inline)
  /-- An authored role: the expansion of a document-defined command with a
  parameter, wrapped so its name survives into the artifact. -/
  | role (name : String) (body : Array Inline)
  /-- `\href{url}{body}`: a hyperlink. -/
  | link (url : String) (body : Array Inline)
  /-- `\label{key}`: the anchor a cross-reference lands on. -/
  | label (key : String)
  /-- `\ref{key}`, `\eqref{key}` or cleveref's family: a cross-reference,
  emitted as `text = "??"` and `target = none` until `resolveRefs` fills
  both. -/
  | ref (key : String) (form : RefForm) (text : String) (target : Option String)
  /-- A drawn text decoration, its geometry resolved from the active face by layout. -/
  | decorated (kind : Decoration) (body : Array Inline)
  /-- Content set in one unbreakable box, raised, grounded or framed as `box` declares. -/
  | boxed (box : InlineBox) (body : Array Inline)
  /-- `\hfill`: stretch that pushes what follows to the far margin. -/
  | fill
  /-- `\hspace{...}`: affine horizontal glue; the starred form survives a
  line break. -/
  | hspace (glue : Affine Measure) (keep : Bool)
  /-- `\rule[raise]{width}{height}`: a painted inline rectangle. -/
  | rule (width height raise : Affine Measure)
  /-- Running-content placeholders, resolved once page count is known. -/
  | pageNumber
  | pageCount
  /-- `\\`, carrying LaTeX's optional extra space: `\\[1ex]`. -/
  | linebreak (extra : SymGlue)
  /-- A strut, LaTeX's `\rule{\z@}{h}`: a zero-width prop that makes its
  line's box at least `h` tall above the baseline. -/
  | strut (height : SymGlue)
  /-- TeX's italic correction, `\/`; `maybe` is ltfntcmd's `\maybe@ic`, made
  only where the face in force is upright. -/
  | italicCorr (maybe : Bool)
  /-- Overlay content crisp exactly on the selector's steps (`\uncover<2>`, `<2->`, `<2-3>`,
  `<1,4>`), elsewhere dimmed, or invisible in its place where `spec.invisible`. -/
  | onSteps (spec : OverlaySpec) (body : Array Inline)
  /-- Overlay alternation (`\alt<2>{a}{b}`): exactly one of the two groups is
  inked per step page, stored in page order. -/
  | altSteps (spec : OverlaySpec) (firstPage : Array Inline)
      (otherPage : Array Inline)
  /-- An external image (`\includegraphics`); `src` is the path as written. -/
  | image (src : String) (size : Image.Spec) (alt : Alt)
  /-- An icon (`\faGithub`, `\faIcon{arrow-up}`): one glyph in an icon face, with its text label. -/
  | icon (scalar : Char) (label : String)
  /-- A citation (`\cite`, natbib's `\citep`/`\citet` and family): one
  citation group's keys as written, and its form. -/
  | cite (form : CiteForm) (keys : Array String)
  /-- A citation the bibliography resolved: its form and keys, and the ink its style sets. -/
  | cited (form : CiteForm) (keys : Array String) (ink : Array Inline)
  /-- `\footnote{...}`: a note set at the foot of the page its mark lands on;
  `num` is the resolved mark number. -/
  | footnote (num : Option Nat) (body : Array Inline)
  deriving Repr, Inhabited

deriving_structural_beq Inline

/-- Single-interval construction; union nodes use `onSteps` directly. -/
@[match_pattern, expose] public def Inline.step (n : Nat) (last : Option Nat) (body : Array Inline) : Inline :=
  .onSteps ⟨n, last, [], false⟩ body

/-- Single-interval alternation, with the same page-order storage. -/
@[match_pattern, expose] public def Inline.alt (n : Nat) (last : Option Nat)
    (firstPage otherPage : Array Inline) : Inline :=
  .altSteps ⟨n, last, [], false⟩ firstPage otherPage


/-- An alternation in source order, stored in page order. -/
public def Inline.alternate (spec : OverlaySpec) (active otherwise : Array Inline) : Inline :=
  let (firstPage, otherPage) := spec.pageOrder active otherwise
  .altSteps spec firstPage otherPage

/-- Which edges of a text-font command get an italic correction, over the
surface's token predicates. -/
public def fontCmdEdges {α : Type} (isSpace isNocorr : α → Bool)
    (reads : Option α → Bool) (body : List α) (next? : Option α) : Bool × Bool :=
  match body.dropWhile isSpace with
  | [] => (false, false)
  | first :: rest => (!isNocorr first && reads body.head?,
      !rest.any isNocorr && reads next?)

/-- The inlines one text-font command contributes: its face, the argument-side
correction, and the trailing correction under the surrounding face. -/
@[expose] public def fontCmdInlines (style : Style) (edges : Bool × Bool)
    (inner : Array Inline) : Array Inline :=
  let run : Inline := .styled style (if edges.1 then #[.italicCorr true] ++ inner else inner)
  if edges.2 then #[run, .italicCorr true] else #[run]

/-- The anchor a reference-list entry carries and its citations link to. -/
public def bibAnchor (key : String) : String := "ref-" ++ key

/-- The link a resolved reference is: its text, linked to its label's anchor unless its form is
starred. -/
@[expose] public def Inline.refLink? : Inline → Option Inline
  | .ref _ form shown (some a) => if form.linked then some (.link ("#" ++ a) #[.text shown]) else none
  | _ => none

/-- The in-page fragment a link's URL names, where it names one. -/
@[expose] public def linkFragment? (url : String) : Option String :=
  if url.startsWith "#" then some (url.drop 1).toString else none

/-- Whether an in-page fragment no anchor claims names the document's top: the empty fragment, or
`top` in any ASCII case (HTML §7.4.6.4). -/
@[expose] public def fragmentTop (frag : String) : Bool :=
  frag.isEmpty || frag.map Char.toLower == "top"


/-- How far a footnote mark's baseline stands above its line's, per mille of
the surrounding size. -/
public def markRaise : Nat := 333

/-- How a frame distributes its leftover vertical space: beamer's
`[t]`/`[c]`/`[b]`, or `golden`, the title page's. -/
public inductive VAlign where
  | top
  | center
  | bottom
  | golden
  deriving Repr, BEq, Inhabited

/-- The fixed opening skip before a frame's body, separate from its distributable space. -/
public def frameBodySkip (hasTitle : Bool) (valign : VAlign) : SymLength :=
  { fixed := if valign matches .top then Dim.mm 2 else 0
    em := if hasTitle then 250 else 0 }

public theorem frameBodySkip_exact (hasTitle : Bool) (valign : VAlign)
    (size : Length) :
    (frameBodySkip hasTitle valign).resolve size 0 =
      (if hasTitle then size / 4 else 0) +
        (if valign matches .top then Dim.mm 2 else 0) := by
  cases hasTitle <;> cases valign <;>
    simp [frameBodySkip, SymLength.resolve] <;> length_omega

/-- The title-page template's glue above and below the title matter, in
thousandths of a fil unit. -/
@[expose] public def titlePageTemplateGlue : Nat × Nat := (2618, 1000)

/-- A frame's own distribution composed with a template's glue, both in
thousandths of a fil unit: the units add. -/
@[expose] public def composeGlue (frame template : Nat × Nat) : Nat × Nat :=
  (frame.1 + template.1, frame.2 + template.2)

/-- Whose frame-alignment keys a deck's frames read: the glue
`\beamer@frametopskip` and `\beamer@framebottomskip` hold. -/
public inductive FrameKeys where
  /-- beamer's own keys (beamerbaseframe.sty:256-272): `[c]` sets
  `0pt plus 1fill` above against `0pt plus 1.5fill` below. -/
  | beamer
  /-- moloch's inner theme, which redefines `[c]` to `0pt plus 1fil` on either side and
  `\maketitle` outside a frame to a plain uncounted frame. -/
  | moloch
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A frame's own leftover-space glue above and below its body, in thousandths
of `\vfill`'s stretch, and whether it is of `\vfill`'s order. -/
public structure FrameGlue where
  above : Nat
  below : Nat
  joins : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The measure a section page centres its title and progress bar in: `0.7875\linewidth`. -/
public def sectionPageMeasure (textWidth : Length) : Length := textWidth * 7875 / 10000

/-- The skip beamer's default `section page` sets between its `\sectionname` line and its title's
line past their leading: `\vskip1em` at the body size `size`, `\lineskip` and the title box's 12pt
`sep`, over the title's cap height in the face of size `large` (beamerinnerthemedefault.sty). -/
public def sectionNameSkip (size large : Length) : Length :=
  size + Dim.pt 13 + large * 7 / 10 - leadingFor large

/-- `\vfill`'s stretch, `0pt plus 1fill`, in `FrameGlue`'s thousandths. -/
@[expose] public def fillUnit : Nat := 1000

/-- The glue a declared alignment sets under a deck's keys. -/
@[expose] public def VAlign.glue (keys : FrameKeys) : VAlign → FrameGlue
  | .top => ⟨0, fillUnit, true⟩
  | .center => match keys with
    | .beamer => ⟨fillUnit, fillUnit * 3 / 2, true⟩
    | .moloch => ⟨fillUnit, fillUnit, false⟩
  | .bottom => ⟨fillUnit, 0, true⟩
  | .golden =>
    let g := composeGlue (fillUnit, fillUnit) titlePageTemplateGlue
    ⟨g.1, g.2, false⟩

/-- A breakable `[c]` frame's glue: beamer's autobreak skips, `.4\paperheight`
above against `.6\paperheight` below. -/
@[expose] public def autobreakCentre : FrameGlue := ⟨fillUnit, fillUnit * 3 / 2, false⟩

/-- The glue a frame spends: its alignment's under its keys, or beamer's
autobreak skips for a breakable centred frame. -/
@[expose] public def frameGlue (keys : FrameKeys) (breakable : Bool) (v : VAlign) : FrameGlue :=
  if breakable && (v matches .center) then autobreakCentre else v.glue keys

/-- The keys a frame reads: the deck's, except a standout frame's, which sets moloch's own `[c]`. -/
@[expose] public def frameKeysOf (keys : FrameKeys) (standout : Bool) : FrameKeys :=
  if standout then .moloch else keys

/-- The shares of a page's leftover vertical space above and below its
content: the ratio form of `VAlign.glue`. -/
@[expose] public def VAlign.shares (keys : FrameKeys) (v : VAlign) (breakable : Bool := false) :
    Nat × Nat :=
  ((frameGlue keys breakable v).above, (frameGlue keys breakable v).below)

public theorem golden_composes_center (keys : FrameKeys) :
    VAlign.golden.shares keys =
      composeGlue (VAlign.center.shares .moloch) titlePageTemplateGlue := by
  rfl

namespace Pic

/-- The line widths the subset strokes (pgf manual §15.3.1): `thin`, every
path's default, and `thick`. -/
public def thinWidth : Length := Dim.pt 2 / 5
public def thickWidth : Length := Dim.pt 4 / 5

/-- A dash pattern by name: `dashed` is on 3 pt off 3 pt, `dotted` on the line
width off 1 pt (pgf manual §15.3.2). -/
public inductive Dash where
  | solid
  | dashed
  | dotted
  deriving Repr, BEq, Inhabited

/-- How a border or an edge strokes: colour, width, dash. -/
public structure Stroke where
  color : Color := Color.black
  width : Length := thinWidth
  dash : Dash := .solid
  deriving Repr, BEq, Inhabited

/-- One segment of a stroked edge, endpoints explicit: a straight line or a
cubic Bézier with its two control points. -/
public inductive PathSeg where
  | line (x1 y1 x2 y2 : Length)
  | cubic (x1 y1 c1x c1y c2x c2y x2 y2 : Length)
  deriving Repr, BEq, Inhabited

/-- The declared box of a segment, which bounds the drawn curve: a cubic lies
in its control points' convex hull. -/
public def PathSeg.box : PathSeg → (Length × Length) × (Length × Length)
  | .line x1 y1 x2 y2 => ((min x1 x2, min y1 y2), (max x1 x2, max y1 y2))
  | .cubic x1 y1 c1x c1y c2x c2y x2 y2 =>
    ((min (min x1 c1x) (min c2x x2), min (min y1 c1y) (min c2y y2)),
     (max (max x1 c1x) (max c2x x2), max (max y1 c1y) (max c2y y2)))

/-- An arrow tip as three corner points: a filled triangle standing in for pgf's `latex` tip. -/
public structure Tip where
  x1 : Length
  y1 : Length
  x2 : Length
  y2 : Length
  x3 : Length
  y3 : Length
  deriving Repr, BEq, Inhabited

/-- Where a label stands relative to its point: centred, TikZ's default
anchor, or with its named side against the point. -/
public inductive LabelAlign where
  | center
  /-- `right`: the label's west edge on the point. -/
  | west
  /-- `left`. -/
  | east
  /-- `above`: the label's south edge on the point. -/
  | south
  /-- `below`. -/
  | north
  deriving Repr, BEq, Inhabited

/-- One shape of an elaborated picture, in picture coordinates: sp with y
growing upward, as TikZ has it. -/
public inductive Shape where
  /-- A text label standing at `(x, y)` by its `align` anchor, at `scale` per
  mille of the body size. -/
  | label (x y : Length) (content : Array Inline) (color : Color) (scale : Nat)
      (align : LabelAlign)
  /-- One node of the vector model, which both backends emit as the figure's own. -/
  | ink (n : Gfx.Node Empty)
  deriving Repr, BEq, Inhabited

/-- A solid opaque fill under the nonzero rule: every TikZ fill. -/
@[expose] public def solidFill (c : Color) : Gfx.Fill :=
  { paint := .solid c, rule := .nonzero, alpha := Gfx.Alpha.opaque }

/-- pgf's miter limit, PDF's initial value of 10 (pgf manual §15.3.1). -/
@[expose] public def pgfMiterLimit : Rat := 10

/-- A picture stroke in the model: pgf's butt caps, miter joins and miter
limit, with the declared colour, width and dash. -/
@[expose] public def strokeOf (k : Stroke) : Gfx.Stroke :=
  { paint := .solid k.color, width := k.width, cap := .butt, join := .miter
    miterLimit := pgfMiterLimit
    dash := match k.dash with
      | .solid => #[]
      | .dashed => #[Dim.pt 3, Dim.pt 3]
      | .dotted => #[k.width, Dim.pt 1]
    phase := 0, alpha := Gfx.Alpha.opaque }

/-- An edge's segments as subpaths: a segment that starts where the last ended
continues its subpath. -/
@[expose] public def edgeSubpaths (segs : Array PathSeg) : Array Gfx.Subpath :=
  let step (acc : Array Gfx.Subpath) (sg : PathSeg) : Array Gfx.Subpath :=
    let (start, seg) : Gfx.Pt × Gfx.Seg := match sg with
      | .line x1 y1 x2 y2 => ((x1, y1), .line (x2, y2))
      | .cubic x1 y1 c1x c1y c2x c2y x2 y2 => ((x1, y1), .cubic (c1x, c1y) (c2x, c2y) (x2, y2))
    match acc.back? with
    | some cur =>
      if cur.endPt == start then acc.pop.push { cur with segs := cur.segs.push seg }
      else acc.push { start := start, segs := #[seg], closed := false }
    | none => acc.push { start := start, segs := #[seg], closed := false }
  segs.foldl step #[]

/-- An arrow tip's triangle, closed. -/
@[expose] public def tipSubpath (t : Tip) : Gfx.Subpath :=
  { start := (t.x1, t.y1), segs := #[.line (t.x2, t.y2), .line (t.x3, t.y3)], closed := true }

/-- A filled rectangle with corners `(x, y)` and `(x + w, y + h)`. -/
@[expose] public def Shape.rect (x y w h : Length) (color : Color) : Shape :=
  .ink (.draw (.rect (min x (x + w)) (min y (y + h)) (max w (-w)) (max h (-h)))
    (some (solidFill color)) none)

/-- A node's circular outline: centre and radius, stroked and/or filled. -/
@[expose] public def Shape.circle (x y r : Length) (stroke : Option Stroke) (fill : Option Color) :
    Shape :=
  .ink (.draw (.ellipse x y (max r (-r)) (max r (-r))) (fill.map solidFill) (stroke.map strokeOf))

/-- A node's rectangular outline: `(x, y)` the min corner, `w × h` the
extents, stroked and/or filled. -/
@[expose] public def Shape.frame (x y w h : Length) (stroke : Option Stroke) (fill : Option Color) :
    Shape :=
  .ink (.draw (.rect (min x (x + w)) (min y (y + h)) (max w (-w)) (max h (-h)))
    (fill.map solidFill) (stroke.map strokeOf))

/-- A stroked edge (`\draw (a) -- (b)`): segments in order, optionally ending
in an arrow tip filled in the stroke's colour. -/
@[expose] public def Shape.edge (segs : Array PathSeg) (stroke : Stroke) (tip : Option Tip) :
    Shape :=
  .ink (.group Gfx.Affine.unit #[] Gfx.Alpha.opaque
    (#[.draw (.path (edgeSubpaths segs)) none (some (strokeOf stroke))] ++
      match tip with
      | some t => #[.draw (.path #[tipSubpath t]) (some (solidFill stroke.color)) none]
      | none => #[]))

private def paintDumpOf : Gfx.Paint → String
  | .solid c => c.hex
  | .gradient (.linear _ _ stops _) => s!"linear({stops.size} stops)"
  | .gradient (.radial _ _ _ _ stops _) => s!"radial({stops.size} stops)"

private def alphaDump (a : Gfx.Alpha) : String :=
  if a == Gfx.Alpha.opaque then "" else s!" alpha {a.val}"

/-- A fill as the IR goldens spell it. -/
public def fillDump : Option Gfx.Fill → String
  | some f =>
    s!" fill {paintDumpOf f.paint}" ++ (if f.rule == .evenOdd then " evenodd" else "") ++
      alphaDump f.alpha
  | none => ""

/-- A stroke as the IR goldens spell it: what differs from pgf's defaults, and
the dash as its pattern. -/
public def strokeDump : Option Gfx.Stroke → String
  | some k =>
    let dash := if k.dash.isEmpty then "" else
      " dash " ++ String.intercalate "," (k.dash.toList.map (·.toBpString))
    let cap := match k.cap with
      | .butt => ""
      | .round => " cap round"
      | .square => " cap square"
    let join := match k.join with
      | .miter => if k.miterLimit == pgfMiterLimit then "" else " miter"
      | .round => " join round"
      | .bevel => " join bevel"
    s!" stroke {paintDumpOf k.paint} {k.width.toBpString}" ++ dash ++ cap ++ join ++
      alphaDump k.alpha
  | none => ""

private def ptDump (p : Gfx.Pt) : String := s!"({p.1.toBpString},{p.2.toBpString})"

/-- A geometry as the IR goldens spell it: `--` a line, `~` a curve's end, `z` a closed subpath. -/
public def geomDump : Gfx.Geom → String
  | .rect x y w h => s!"rect {x.toBpString} {y.toBpString} {w.toBpString} {h.toBpString}"
  | .ellipse cx cy rx ry =>
    s!"ellipse {cx.toBpString} {cy.toBpString} {rx.toBpString} {ry.toBpString}"
  | .path subs => "path" ++ String.join (subs.toList.map fun sp =>
      let segs := String.join (sp.segs.toList.map fun sg => match sg with
        | .line q => s!"--{ptDump q}"
        | .cubic _ _ q => s!"~{ptDump q}")
      s!" {ptDump sp.start}{segs}{if sp.closed then " z" else ""}")

mutual

-- conserves: none — a debug dump.
/-- One ink node's lines in the IR goldens, a group's kids indented. -/
public def dumpNode (ind : String) (acc : String) : Gfx.Node Empty → String
  | .draw g fl st => acc ++ s!"{ind}draw {geomDump g}{fillDump fl}{strokeDump st}\n"
  | .group xf clips alpha kids =>
    let head := s!"{ind}group" ++ (if xf == Gfx.Affine.unit then "" else s!" cm {xf.operands}") ++
      (if clips.isEmpty then "" else s!" clip {clips.size}") ++ alphaDump alpha ++ "\n"
    dumpNodeList (ind ++ "  ") (acc ++ head) kids.toList
  | .use k _ => acc ++ s!"{ind}use {k}\n"
  | .stamp o _ fl st => acc ++ s!"{ind}stamp {o}{fillDump fl}{strokeDump st}\n"
  | .image k _ => acc ++ s!"{ind}image {k}\n"
  | .label l => nomatch l
  | .words w => acc ++ s!"{ind}words {w}\n"

public def dumpNodeList (ind : String) (acc : String) : List (Gfx.Node Empty) → String
  | [] => acc
  | n :: rest => dumpNodeList ind (dumpNode ind acc n) rest

end

/-- Repaint a shape, keeping its geometry and text. -/
@[expose] public def Shape.recolor (f : Color → Color) : Shape → Shape
  | .label x y t c sc al => .label x y t (f c) sc al
  | .ink n => .ink (Gfx.Node.recolorOne f id n)

/-- A box in picture coordinates: min corner, then max corner. -/
public abbrev Box := Gfx.Box


/-- Translate a measured interval beside an anchor: a positive direction puts
its lower edge one gap beyond, a negative its upper edge one gap before, zero
centres it. -/
public def Box.axisOffset (anchor lo hi gap direction : Length) : Length :=
  if 0 < direction then anchor + gap - lo
  else if direction < 0 then anchor - gap - hi
  else anchor - (lo + hi) / 2

public theorem Box.axisOffset_contract (anchor lo hi gap direction : Length) :
    (0 < direction → lo + axisOffset anchor lo hi gap direction = anchor + gap) ∧
    (direction < 0 → hi + axisOffset anchor lo hi gap direction = anchor - gap) ∧
    (direction = 0 →
      2 * anchor ≤ lo + hi + 2 * axisOffset anchor lo hi gap direction ∧
      lo + hi + 2 * axisOffset anchor lo hi gap direction ≤ 2 * anchor + Length.quantum) := by
  by_cases hp : 0 < direction
  · simp only [axisOffset, ite_eq_left hp]
    length_omega
  · by_cases hn : direction < 0
    · simp only [axisOffset, ite_eq_right hp, ite_eq_left hn]
      length_omega
    · simp only [axisOffset, ite_eq_right hp, ite_eq_right hn]
      length_omega

/-- Attach a whole box beside an anchor by translation: corner placement
constrains both axes, side placement centres the other. -/
public def Box.attachOffset (box : Box) (anchor direction gap : Length × Length) : Length × Length :=
  (axisOffset anchor.1 box.1.1 box.2.1 gap.1 direction.1,
   axisOffset anchor.2 box.1.2 box.2.2 gap.2 direction.2)

public theorem Box.attachOffset_contract (box : Box) (anchor direction gap : Length × Length) :
    let offset := attachOffset box anchor direction gap
    let onAxis (a lo hi g d shift : Length) : Prop :=
      (0 < d → lo + shift = a + g) ∧
      (d < 0 → hi + shift = a - g) ∧
      (d = 0 → 2 * a ≤ lo + hi + 2 * shift ∧ lo + hi + 2 * shift ≤ 2 * a + Length.quantum)
    onAxis anchor.1 box.1.1 box.2.1 gap.1 direction.1 offset.1 ∧
    onAxis anchor.2 box.1.2 box.2.2 gap.2 direction.2 offset.2 :=
  ⟨axisOffset_contract anchor.1 box.1.1 box.2.1 gap.1 direction.1,
   axisOffset_contract anchor.2 box.1.2 box.2.2 gap.2 direction.2⟩

/-- A label line's measured ink: its set width and how far its glyphs reach
above and below its baseline. -/
public structure LabelInk where
  w : Length := 0
  height : Length := 0
  depth : Length := 0
  /-- How far the glyphs reach above and below the baseline: the TeX box the
  text makes, which a node's border holds. -/
  boxHeight : Length := 0
  boxDepth : Length := 0
  /-- The face's x-height at the label's size, what `ex` means in a node's options. -/
  ex : Length := 0
  /-- The math face's axis height, fraction rule thickness and script scale at
  the label's size, from its MATH table; zero without a math face. -/
  axis : Length := 0
  rule : Length := 0
  script : Nat := 0
  deriving Repr, BEq, Inhabited

/-- What a label's content sets to at a per-mille size, a measurement the IR cannot make. -/
public abbrev LabelMetric := Array Inline → Nat → LabelInk

/-- Where a label's ink stands around its anchor, given its extents: the
anchor decides which point of the box sits on `(x, y)`. -/
private def labelInkSpan (x y : Length) (align : LabelAlign) (w tall : Length) : Box :=
  match align with
  | .center => ((x - w / 2, y - tall / 2), (x - w / 2 + w, y - tall / 2 + tall))
  | .west => ((x, y - tall / 2), (x + w, y - tall / 2 + tall))
  | .east => ((x - w, y - tall / 2), (x, y - tall / 2 + tall))
  | .south => ((x - w / 2, y), (x - w / 2 + w, y + tall))
  | .north => ((x - w / 2, y - tall), (x - w / 2 + w, y))

private theorem labelInkSpan_covers_anchor (x y : Length) (align : LabelAlign) (w tall : Length)
    (hw : 0 ≤ w) (ht : 0 ≤ tall) :
    Gfx.Box.le ((x, y), (x, y)) (labelInkSpan x y align w tall) := by
  have half : ∀ a b : Length, 0 ≤ b → a - b / 2 ≤ a ∧ a ≤ a - b / 2 + b := by
    intro a b h; length_omega
  have full : ∀ a b : Length, 0 ≤ b → a - b ≤ a := by intro a b h; length_omega
  have grow : ∀ a b : Length, 0 ≤ b → a ≤ a + b := by intro a b h; length_omega
  cases align
  · exact ⟨(half x w hw).1, (half y tall ht).1, (half x w hw).2, (half y tall ht).2⟩
  · exact ⟨Length.le_refl x, (half y tall ht).1, grow x w hw, (half y tall ht).2⟩
  · exact ⟨full x w hw, (half y tall ht).1, Length.le_refl x, (half y tall ht).2⟩
  · exact ⟨(half x w hw).1, Length.le_refl y, (half x w hw).2, grow y tall ht⟩
  · exact ⟨(half x w hw).1, full y tall ht, (half x w hw).2, Length.le_refl y⟩

/-- Where a label's measured ink stands around its anchor, negative extents clamped away. -/
public def labelInkBox (x y : Length) (align : LabelAlign) (m : LabelInk) : Box :=
  labelInkSpan x y align (max m.w 0) (max (m.height + m.depth) 0)

/-- Where a label's baseline sits: the top of its ink box less its height. -/
public def labelBaseline (y : Length) (align : LabelAlign) (m : LabelInk) : Length :=
  (labelInkBox 0 y align m).2.2 - m.height

public theorem labelBaseline_box_exact (x y : Length) (align : LabelAlign) (m : LabelInk) :
    labelBaseline y align m = (labelInkBox x y align m).2.2 - m.height := by
  cases align <;> rfl

/-- The text's measured TeX box on its resolved baseline, without the anchor
or the font band in its vertical extent. -/
public def labelTextBox (x y : Length) (align : LabelAlign) (m : LabelInk) : Box :=
  let band := labelInkBox x y align m
  let b := labelBaseline y align m
  ((band.1.1, b - m.boxDepth), (band.2.1, b + m.boxHeight))

public theorem labelTextBox_translate_exact (x y : Length) (align : LabelAlign) (m : LabelInk)
    (offset : Length × Length) :
    let box := labelTextBox x y align m
    labelTextBox (x + offset.1) (y + offset.2) align m =
      ((box.1.1 + offset.1, box.1.2 + offset.2),
       (box.2.1 + offset.1, box.2.2 + offset.2)) := by
  cases align <;>
    simp [labelTextBox, labelBaseline, labelInkBox, labelInkSpan] <;> length_omega

/-- Where a label's glyphs stand: the TeX box its text makes, on the baseline the band places. -/
@[expose] public def labelGlyphBox (x y : Length) (align : LabelAlign) (m : LabelInk) : Box :=
  let box := labelTextBox x y align m
  ((box.1.1, min y box.1.2), (box.2.1, max y box.2.2))

public theorem labelGlyphBox_covers (x y : Length) (align : LabelAlign) (m : LabelInk) :
    Gfx.Box.le ((x, y), (x, y)) (labelGlyphBox x y align m) := by
  have hx := labelInkSpan_covers_anchor x y align (max m.w 0) (max (m.height + m.depth) 0)
    (Length.le_max_right _ _) (Length.le_max_right _ _)
  have lo : ∀ a b : Length, min a b ≤ a := by intro a b; length_omega
  have hi : ∀ a b : Length, a ≤ max a b := by intro a b; length_omega
  exact ⟨hx.1, lo _ _, hx.2.2.1, hi _ _⟩

public theorem labelGlyphBox_covers_extent (x y : Length) (align : LabelAlign) (m : LabelInk)
    (hi lo : Length) (hhi : hi ≤ m.boxHeight) (hlo : lo ≤ m.boxDepth) :
    (labelGlyphBox x y align m).1.2 ≤ labelBaseline y align m - lo ∧
    labelBaseline y align m + hi ≤ (labelGlyphBox x y align m).2.2 := by
  simp only [labelGlyphBox, labelTextBox]
  have bottom := Length.min_le_right y (labelBaseline y align m - m.boxDepth)
  have top := Length.le_max_right y (labelBaseline y align m + m.boxHeight)
  exact ⟨Length.le_trans bottom (Length.sub_le_sub_left hlo _),
    Length.le_trans (Length.add_le_add_left hhi _) top⟩

public theorem labelBaseline_width_id (y w : Length) (align : LabelAlign) (m : LabelInk) :
    labelBaseline y align { m with w := w } = labelBaseline y align m := by
  cases align <;> rfl

public theorem labelBaseline_between (y : Length) (m : LabelInk)
    (h : 0 ≤ m.height + m.depth) :
    y + (m.depth - m.height) / 2 ≤ labelBaseline y .center m ∧
      labelBaseline y .center m ≤ y + (m.depth - m.height) / 2 + Length.quantum := by
  show y + (m.depth - m.height) / 2
        ≤ y - (max (m.height + m.depth) 0) / 2 + max (m.height + m.depth) 0 - m.height ∧
      y - (max (m.height + m.depth) 0) / 2 + max (m.height + m.depth) 0 - m.height
        ≤ y + (m.depth - m.height) / 2 + Length.quantum
  have step : ∀ a b c : Length, 0 ≤ b + c →
      a + (c - b) / 2 ≤ a - (max (b + c) 0) / 2 + max (b + c) 0 - b ∧
      a - (max (b + c) 0) / 2 + max (b + c) 0 - b ≤ a + (c - b) / 2 + Length.quantum := by
    intro a b c hbc; length_omega
  exact step y m.height m.depth h

/-- The componentwise join of two measurements: what a line carrying both would set to. -/
public def LabelInk.join (a b : LabelInk) : LabelInk :=
  { w := max a.w b.w, height := max a.height b.height, depth := max a.depth b.depth
    boxHeight := max a.boxHeight b.boxHeight, boxDepth := max a.boxDepth b.boxDepth
    ex := max a.ex b.ex }

public theorem phantom_extent_between (x y : Length) (align : LabelAlign) (m p : LabelInk) :
    Gfx.Box.le (labelInkBox x y align m) (labelInkBox x y align (m.join p)) ∧
      (p.w ≤ m.w → p.height ≤ m.height → p.depth ≤ m.depth →
        labelInkBox x y align (m.join p) = labelInkBox x y align m) := by
  refine ⟨?_, ?_⟩
  · have mid : ∀ v s t : Length, s ≤ t →
        v - t / 2 ≤ v - s / 2 ∧ v - s / 2 + s ≤ v - t / 2 + t := by
      intro v s t h; length_omega
    have near : ∀ v s t : Length, s ≤ t → v ≤ v ∧ v + s ≤ v + t := by
      intro v s t h; length_omega
    have far : ∀ v s t : Length, s ≤ t → v - t ≤ v - s ∧ v ≤ v := by
      intro v s t h; length_omega
    have gw : max m.w 0 ≤ max (m.join p).w 0 := by
      have jw : ∀ a b : Length, max a 0 ≤ max (max a b) 0 := by intro a b; length_omega
      exact jw m.w p.w
    have gt : max (m.height + m.depth) 0 ≤ max ((m.join p).height + (m.join p).depth) 0 := by
      have jt : ∀ a b c d : Length, max (a + c) 0 ≤ max (max a b + max c d) 0 := by
        intro a b c d; length_omega
      exact jt m.height p.height m.depth p.depth
    cases align
    · exact ⟨(mid x _ _ gw).1, (mid y _ _ gt).1, (mid x _ _ gw).2, (mid y _ _ gt).2⟩
    · exact ⟨(near x _ _ gw).1, (mid y _ _ gt).1, (near x _ _ gw).2, (mid y _ _ gt).2⟩
    · exact ⟨(far x _ _ gw).1, (mid y _ _ gt).1, (far x _ _ gw).2, (mid y _ _ gt).2⟩
    · exact ⟨(mid x _ _ gw).1, (near y _ _ gt).1, (mid x _ _ gw).2, (near y _ _ gt).2⟩
    · exact ⟨(mid x _ _ gw).1, (far y _ _ gt).1, (mid x _ _ gw).2, (far y _ _ gt).2⟩
  · intro hw hh hd
    have dom : ∀ a b : Length, b ≤ a → max a b = a := by intro a b h; length_omega
    have ew : (m.join p).w = m.w := dom m.w p.w hw
    have eh : (m.join p).height = m.height := dom m.height p.height hh
    have ed : (m.join p).depth = m.depth := dom m.depth p.depth hd
    unfold labelInkBox
    rw [ew, eh, ed]

/-- The box a clipping group reaches: its clips' own geometry through its frame. -/
@[expose] public def clipHull : Gfx.Node Empty → Option Box
  | .group xf clips _ _ => Gfx.hullOf (fun (c : Gfx.Clip) => c.geom.hull.map (Gfx.Box.image xf)) clips
  | .draw .. | .use .. | .stamp .. | .image .. | .label _ | .words _ => none

public theorem clipHull_recolor_id (f : Color → Color) (n : Gfx.Node Empty) :
    clipHull (Gfx.Node.recolorOne f id n) = clipHull n := by
  cases n <;> rfl

/-- The declared box of a shape, corners sorted; a label's box is its anchor point. -/
public def Shape.box : Shape → Box
  | .label x y _ _ _ _ => ((x, y), (x, y))
  | .ink n =>
    ((clipHull n).orElse fun _ =>
      Gfx.hullOf (Gfx.Mark.geomBox Gfx.rasterUnit) (Gfx.Node.marksOne #[] Gfx.Ctx.root #[] n)).getD
      ((0, 0), (0, 0))

public structure Picture where
  shapes : Array Shape := #[]
  /-- The box `\useasboundingbox` declared, corners sorted: the picture's size
  whatever its marks do. -/
  declared : Option Box := none
  /-- Every node's border, its text extent plus `inner sep`, drawn or not. -/
  borders : Array Box := #[]
  /-- The height the surrounding line's baseline passes through, in picture
  coordinates, when the picture declares one (`baseline=`). -/
  baseline : Option Length := none
  /-- The alternative the author declared on the picture (`alt={...}` or `artifact`). -/
  alt : Alt := .undeclared
  deriving Repr, BEq, Inhabited

/-- The gradients a picture's shapes paint, in paint order. -/
@[expose] public def Picture.gradients (p : Picture) : Array Gfx.Gradient :=
  p.shapes.foldl (init := #[]) fun acc sh => match sh with
    | .ink n => Gfx.Node.gradientsOne acc n
    | .label .. => acc

@[expose] public def Picture.recolor (p : Picture) (f : Color → Color) : Picture :=
  { p with shapes := p.shapes.map (·.recolor f) }

/-- The solid colour a geometry's fill paints at a point, when the geometry
holds it; a path is not asked. -/
public def geomFillAt (x y : Length) (c : Color) : Gfx.Geom → Option Color
  | .rect rx ry w h => if rx ≤ x ∧ x ≤ rx + w ∧ ry ≤ y ∧ y ≤ ry + h then some c else none
  | .ellipse cx cy rx ry =>
    if rx == ry then
      if (x - cx) * (x - cx) + (y - cy) * (y - cy) ≤ rx * rx then some c else none
    else if (x - cx) * (x - cx) * (ry * ry) + (y - cy) * (y - cy) * (rx * rx) ≤
        rx * rx * (ry * ry) then some c
    else none
  | .path _ => none

/-- A paint over the ground it covers at the paint's alpha: source-over per
sRGB channel, rounded. -/
public def _root_.LeanTex.Core.Ir.Color.over (c : Color) (a : Gfx.Alpha) :
    Option Color → Option Color
  | some u =>
    if a = Gfx.Alpha.opaque then some c else
    let ch (x y : UInt8) : UInt8 :=
      UInt8.ofNat ((x.toNat * a.val + y.toNat * (1000 - a.val) + 500) / 1000)
    some { r := ch c.r u.r, g := ch c.g u.g, b := ch c.b u.b }
  | none => if a = Gfx.Alpha.opaque then some c else none

mutual

-- conserves: none — a point reading.
/-- The ground one node leaves at a point over the ground `under` it paints on. -/
public def inkGroundAt (x y : Length) (under : Option Color) : Gfx.Node Empty → Option Color
  | .draw g (some { paint := .solid c, alpha, .. }) _ =>
    match geomFillAt x y c g with
    | some c => c.over alpha under
    | none => under
  | .draw _ _ _ => under
  | .group xf clips alpha kids =>
    if xf == Gfx.Affine.unit && clips.isEmpty then
      let inner := inkGroundAtList x y under kids.toList
      if alpha == Gfx.Alpha.opaque || inner == under then inner
      else inner.bind fun k => k.over alpha under
    else under
  | .use _ _ => under
  | .stamp _ _ _ _ => under
  | .image _ _ => under
  | .label l => nomatch l
  | .words _ => under

public def inkGroundAtList (x y : Length) (under : Option Color) :
    List (Gfx.Node Empty) → Option Color
  | [] => under
  | n :: rest => inkGroundAtList x y (inkGroundAt x y under n) rest

end

/-- The ground a shape leaves at a point over `under`: a label's glyphs are
no one's ground. -/
public def Shape.groundAt (x y : Length) (under : Option Color) : Shape → Option Color
  | .label _ _ _ _ _ _ => under
  | .ink n => inkGroundAt x y under n

/-- The ground a label's ink stands on: `base` with every shape drawn before
the label composited over it at the label's anchor. -/
public def fillUnder (base : Option Color) (drawn : Array Shape) (x y : Length) : Option Color :=
  drawn.foldl (fun g s => s.groundAt x y g) base

/-- The inline content each label sets: every glyph a picture can ask a face for. -/
public def Picture.labelContents (p : Picture) : Array (Array Inline) :=
  p.shapes.filterMap fun s => match s with
    | .label _ _ content _ _ _ => some content
    | .ink _ => none

/-- A shape with its label content through `f`; everything else stays. -/
@[expose] public def Shape.mapLabel (f : Array Inline → Array Inline) : Shape → Shape
  | .label x y content c scale align => .label x y (f content) c scale align
  | .ink n => .ink n

/-- Every label's content through one inline rewrite. -/
@[expose] public def Picture.mapLabels (f : Array Inline → Array Inline) (p : Picture) :
    Picture :=
  { p with shapes := p.shapes.map (·.mapLabel f) }

private theorem Picture.labelContents_mapLabels (f : Array Inline → Array Inline)
    (p : Picture) : (p.mapLabels f).labelContents = p.labelContents.map f := by
  simp only [Picture.mapLabels, Picture.labelContents, Array.filterMap_map,
    Array.map_filterMap]
  congr 1
  funext s
  cases s <;> rfl

private theorem Picture.mapLabels_comp (f g : Array Inline → Array Inline) (p : Picture) :
    (p.mapLabels g).mapLabels f = p.mapLabels (f ∘ g) := by
  simp only [Picture.mapLabels, Array.map_map]
  congr 2
  funext s
  cases s <;> rfl

/-- The box a shape's ink occupies, given a measurement: the declared box for
every shape but a label. -/
@[expose] public def Shape.inkBox (m : LabelMetric) : Shape → Box
  | .label x y content _ scale align => labelGlyphBox x y align (m content scale)
  | s@(.ink _) => s.box

/-- The half-extents a label of this width and height asks of the node it
hangs on, read off `labelInkSpan`. -/
public def labelHalfExtent (align : LabelAlign) (w tall : Length) : Length × Length :=
  let ((x0, y0), (x1, y1)) := labelInkSpan 0 0 align w tall
  (max (-x0) x1, max (-y0) y1)

@[expose] public def nodeExtentBox (x y a b : Length) : Box := ((x - a, y - b), (x + a, y + b))

private theorem labelHalfExtent_covers (align : LabelAlign) (x y w tall : Length) :
    Gfx.Box.le (labelInkSpan x y align w tall)
      (nodeExtentBox x y (labelHalfExtent align w tall).1
        (labelHalfExtent align w tall).2) := by
  have mid : ∀ v d : Length,
      v - max (-(0 - d / 2)) (0 - d / 2 + d) ≤ v - d / 2 ∧
      v - d / 2 + d ≤ v + max (-(0 - d / 2)) (0 - d / 2 + d) := by
    intro v d; length_omega
  have near : ∀ v d : Length,
      v - max (-0) (0 + d) ≤ v ∧ v + d ≤ v + max (-0) (0 + d) := by
    intro v d; length_omega
  have far : ∀ v d : Length,
      v - max (-(0 - d)) 0 ≤ v - d ∧ v ≤ v + max (-(0 - d)) 0 := by
    intro v d; length_omega
  cases align
  · exact ⟨(mid x w).1, (mid y tall).1, (mid x w).2, (mid y tall).2⟩
  · exact ⟨(near x w).1, (mid y tall).1, (near x w).2, (mid y tall).2⟩
  · exact ⟨(far x w).1, (mid y tall).1, (far x w).2, (mid y tall).2⟩
  · exact ⟨(mid x w).1, (near y tall).1, (mid x w).2, (near y tall).2⟩
  · exact ⟨(mid x w).1, (far y tall).1, (mid x w).2, (far y tall).2⟩

public theorem nodeExtentBox_monotone (x y a b a' b' : Length) (ha : a ≤ a') (hb : b ≤ b') :
    Gfx.Box.le (nodeExtentBox x y a b) (nodeExtentBox x y a' b') := by
  have step : ∀ v p q : Length, p ≤ q → v - q ≤ v - p ∧ v + p ≤ v + q := by
    intro v p q h; length_omega
  exact ⟨(step x a a' ha).1, (step y b b' hb).1, (step x a a' ha).2, (step y b b' hb).2⟩

/-- The half-extents a node registers given a measurement: the declared
minimum, or the label's own reach where it stands proud of it. -/
@[expose] public def nodeExtent (m : LabelMetric) (content : Array Inline) (scale : Nat)
    (align : LabelAlign) (declA declB : Length) : Length × Length :=
  let ink := m content scale
  let (a, b) := labelHalfExtent align (max ink.w 0) (max (ink.height + ink.depth) 0)
  (max declA a, max declB b)

public theorem nodeExtent_covers (m : LabelMetric) (content : Array Inline) (scale : Nat)
    (align : LabelAlign) (declA declB x y : Length) :
    Gfx.Box.le (labelInkBox x y align (m content scale))
      (nodeExtentBox x y (nodeExtent m content scale align declA declB).1
        (nodeExtent m content scale align declA declB).2) := by
  have grow : ∀ p q : Length, p ≤ max q p := by intro p q; length_omega
  exact Gfx.Box.le_trans (labelHalfExtent_covers align x y _ _)
    (nodeExtentBox_monotone x y _ _ _ _ (grow _ declA) (grow _ declB))

public theorem centre_independent_of_growth (m : LabelMetric) (content : Array Inline)
    (scale : Nat) (align : LabelAlign) (declA declB declA' declB' x y : Length)
    (hA : declA ≤ declA') (hB : declB ≤ declB') :
    Gfx.Box.le (nodeExtentBox x y (nodeExtent m content scale align declA declB).1
             (nodeExtent m content scale align declA declB).2)
        (nodeExtentBox x y (nodeExtent m content scale align declA' declB').1
          (nodeExtent m content scale align declA' declB').2) ∧
      labelBaseline y align (m content scale) = labelBaseline y align (m content scale) ∧
      labelInkBox x y align (m content scale) = labelInkBox x y align (m content scale) := by
  refine ⟨?_, rfl, rfl⟩
  have step : ∀ p q r : Length, p ≤ q → max p r ≤ max q r := by intro p q r h; length_omega
  exact nodeExtentBox_monotone x y _ _ _ _ (step _ _ _ hA) (step _ _ _ hB)

public theorem nodeExtent_separates (m : LabelMetric) (ca cb : Array Inline)
    (sa sb : Nat) (alignA alignB : LabelAlign) (aA aB bA bB : Length)
    (x y sep : Length) (hsep : 0 < sep) :
    (labelInkBox x y alignA (m ca sa)).2.1 <
      (labelInkBox
        (x + (sep + (nodeExtent m ca sa alignA aA aB).1
          + (nodeExtent m cb sb alignB bA bB).1)) y alignB (m cb sb)).1.1 := by
  have ha := (nodeExtent_covers m ca sa alignA aA aB x y).2.2.1
  have hb := (nodeExtent_covers m cb sb alignB bA bB
    (x + (sep + (nodeExtent m ca sa alignA aA aB).1
      + (nodeExtent m cb sb alignB bA bB).1)) y).1
  simp only [nodeExtentBox] at ha hb
  have chain : ∀ p u q s b v a : Length,
      p ≤ u → v + (s + a + b) - b ≤ q → 0 < s → u = v + a → p < q := by
    intro p u q s b v a h1 h2 h3 h4; length_omega
  exact chain _ _ _ sep _ x _ ha hb hsep rfl

/-- The hull of a per-shape box over a picture. -/
public def Picture.boxFold (p : Picture) (f : Shape → Box) : Box :=
  Gfx.Box.hull (p.shapes.map f)

public def Picture.bbox (p : Picture) : Box := p.boxFold Shape.box

/-- Every label's ink box, in shape order, one measurement per label. -/
public def Picture.inkBoxes (p : Picture) (m : LabelMetric) : Array Box :=
  p.shapes.map (Shape.inkBox m)

/-- The picture's ink box under a measurement: the hull of its shapes' ink boxes. -/
public def Picture.inkBbox (p : Picture) (m : LabelMetric) : Box :=
  Gfx.Box.hull (p.inkBoxes m)

public theorem Picture.boxFold_covers (p : Picture) (f : Shape → Box) (s : Shape)
    (h : s ∈ p.shapes) : Gfx.Box.le (f s) (p.boxFold f) :=
  Gfx.Box.hull_covers _ (f s) (Array.mem_map_of_mem h)

public theorem Picture.box_in_bbox (p : Picture) (s : Shape) (h : s ∈ p.shapes) :
    Gfx.Box.le s.box p.bbox := p.boxFold_covers Shape.box s h

public theorem Picture.inkBbox_covers (p : Picture) (m : LabelMetric) (s : Shape)
    (h : s ∈ p.shapes) : Gfx.Box.le (s.inkBox m) (p.inkBbox m) :=
  Gfx.Box.hull_covers _ (s.inkBox m) (Array.mem_map_of_mem h)

/-- The natural box TikZ reserves when nothing is declared: every mark's ink
and every node's border. -/
public def Picture.natural (p : Picture) (m : LabelMetric) : Box :=
  Gfx.Box.hull (p.inkBoxes m ++ p.borders)

/-- The box a picture occupies: the declared box when `\useasboundingbox` gave
one, else the natural box. -/
public def Picture.box (p : Picture) (m : LabelMetric) : Box :=
  p.declared.getD (p.natural m)

public theorem Picture.box_declared_exact (p : Picture) (m : LabelMetric) (b : Box)
    (h : p.declared = some b) : p.box m = b := by
  simp [Picture.box, h]

public theorem Picture.mapLabels_box_id (m : LabelMetric) (f : Array Inline → Array Inline)
    (hm : ∀ content scale, m (f content) scale = m content scale) (p : Picture) :
    (p.mapLabels f).box m = p.box m := by
  have hboxes : (p.mapLabels f).inkBoxes m = p.inkBoxes m := by
    simp only [Picture.inkBoxes, Picture.mapLabels, Array.map_map]
    congr 1
    funext s
    cases s <;> simp [Shape.mapLabel, Shape.inkBox, hm]
  simp only [Picture.box, Picture.natural, hboxes]
  rfl

public theorem Picture.recolor_box_id (p : Picture) (f : Color → Color) (m : LabelMetric) :
    (p.recolor f).box m = p.box m := by
  have hs : ∀ s : Shape, (s.recolor f).inkBox m = s.inkBox m := by
    intro s
    cases s with
    | label => rfl
    | ink n => simp only [Shape.recolor, Shape.inkBox, Shape.box, Gfx.Node.recolor_geomBox_id,
        clipHull_recolor_id]
  have hb : (p.recolor f).inkBoxes m = p.inkBoxes m := by
    simp only [Picture.inkBoxes, Picture.recolor, Array.map_map]
    exact Array.map_congr_left fun s _ => hs s
  simp only [Picture.box, Picture.natural, hb]
  rfl

/-- How far above its box's bottom edge a picture's declared baseline runs,
held inside the box; zero when undeclared. -/
public def Picture.rise (p : Picture) (m : LabelMetric) : Length :=
  (p.baseline.map fun yb =>
    max 0 (min ((p.box m).2.2 - (p.box m).1.2) (yb - (p.box m).1.2))).getD 0

private theorem clampRise_between (lo hi yb : Int) (h : lo ≤ hi) :
    0 ≤ max 0 (min (hi - lo) (yb - lo)) ∧ max 0 (min (hi - lo) (yb - lo)) ≤ hi - lo := by
  omega

public theorem Picture.rise_between (p : Picture) (m : LabelMetric)
    (h : (p.box m).1.2 ≤ (p.box m).2.2) :
    0 ≤ p.rise m ∧ p.rise m ≤ (p.box m).2.2 - (p.box m).1.2 := by
  unfold Picture.rise
  cases p.baseline with
  | some yb => exact clampRise_between _ _ _ h
  | none => exact ⟨Length.le_refl 0, Int.sub_nonneg.mpr h⟩

public theorem Picture.box_covers (p : Picture) (m : LabelMetric) (h : p.declared = none) :
    (∀ s ∈ p.shapes, Gfx.Box.le (s.inkBox m) (p.box m)) ∧
      (∀ b ∈ p.borders, Gfx.Box.le b (p.box m)) := by
  simp only [Picture.box, h, Option.getD_none, Picture.natural]
  refine ⟨fun s hs => ?_, fun b hb => ?_⟩
  · exact Gfx.Box.hull_covers _ _ (Array.mem_append_left _ (Array.mem_map_of_mem hs))
  · exact Gfx.Box.hull_covers _ _ (Array.mem_append_right _ hb)

public theorem Shape.box_le_inkBox (m : LabelMetric) (s : Shape) : Gfx.Box.le s.box (s.inkBox m) := by
  cases s with
  | label x y content color scale align =>
    exact labelGlyphBox_covers x y align _
  | ink _ => exact Gfx.Box.le_refl _

/-- Where a picture lands on a page: the translation and y reflection from
picture coordinates (y up) to layout coordinates (y down). -/
public structure Place where
  /-- Page x where the picture's `xmin` lands (its left edge). -/
  x0 : Length
  /-- Page y where the picture's `ymax` lands (its top edge). -/
  yTop : Length
  xmin : Length
  ymax : Length
  deriving Repr, BEq, Inhabited

@[expose] public def Place.toPage (t : Place) (u : Length × Length) : Length × Length :=
  (t.x0 + (u.1 - t.xmin), t.yTop + (t.ymax - u.2))

/-- The placement as the vector model's integer isometry. -/
@[expose] public def Place.toIso (t : Place) : Gfx.Iso :=
  { flipY := true, dx := t.x0 - t.xmin, dy := t.yTop + t.ymax }

public theorem Place.affine_exact (t : Place) (u : Length × Length) : t.toPage u = t.toIso.apply u := by
  obtain ⟨ux, uy⟩ := u
  have hx : ∀ a b c : Length, a + (c - b) = c + (a - b) := by intro a b c; length_omega
  have hy : ∀ a b c : Length, a + (b - c) = a + b - c := by intro a b c; length_omega
  simp only [toPage, toIso, Gfx.Iso.apply, ↓reduceIte]
  exact Prod.ext (hx _ _ _) (hy _ _ _)

public def Place.ofPage (t : Place) (q : Length × Length) : Length × Length :=
  (t.xmin + (q.1 - t.x0), t.ymax - (q.2 - t.yTop))

public theorem Place.ofPage_iso_exact (t : Place) (q : Length × Length) : t.ofPage q = t.toIso.inv.apply q := by
  obtain ⟨qx, qy⟩ := q
  have hx : ∀ a b c : Length, a + (c - b) = c + -(b - a) := by intro a b c; length_omega
  have hy : ∀ m yT q : Length, m - (q - yT) = yT + m - q := by intro m yT q; length_omega
  simp only [ofPage, toIso, Gfx.Iso.inv, Gfx.Iso.apply, ↓reduceIte]
  exact Prod.ext (hx _ _ _) (hy _ _ _)

public theorem Place.ofPage_toPage (t : Place) (u : Length × Length) : t.ofPage (t.toPage u) = u := by
  rw [affine_exact, ofPage_iso_exact, Gfx.Iso.inv_apply_id]

public theorem Place.toPage_ofPage (t : Place) (q : Length × Length) : t.toPage (t.ofPage q) = q := by
  obtain ⟨qx, qy⟩ := q
  have hx : ∀ a b c : Length, b + (a + (c - b) - a) = c := by intro a b c; length_omega
  have hy : ∀ yT m q : Length, yT + (m - (m - (q - yT))) = q := by intro yT m q; length_omega
  simp only [toPage, ofPage, Prod.mk.injEq]
  exact ⟨hx _ _ _, hy _ _ _⟩

public theorem Place.toPage_box (t : Place) (b : Box) (u : Length × Length)
    (hx1 : b.1.1 ≤ u.1) (hx2 : u.1 ≤ b.2.1) (hy1 : b.1.2 ≤ u.2) (hy2 : u.2 ≤ b.2.2) :
    (t.toPage (b.1.1, b.2.2)).1 ≤ (t.toPage u).1
      ∧ (t.toPage u).1 ≤ (t.toPage (b.2.1, b.1.2)).1
      ∧ (t.toPage (b.1.1, b.2.2)).2 ≤ (t.toPage u).2
      ∧ (t.toPage u).2 ≤ (t.toPage (b.2.1, b.1.2)).2 := by
  have hx : ∀ d a b : Length, a ≤ b → a + d ≤ b + d := by intro d a b h; length_omega
  have hy : ∀ d a b : Length, a ≤ b → d - b ≤ d - a := by intro d a b h; length_omega
  simp only [affine_exact, toIso, Gfx.Iso.apply, ↓reduceIte]
  exact ⟨hx _ _ _ hx1, hx _ _ _ hx2, hy _ _ _ hy2, hy _ _ _ hy1⟩

end Pic

/-- Horizontal alignment of a table column's cells, and the side a scope sets its boxes on. -/
public inductive HAlign where
  | left
  | center
  | right
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The side as the `text-align` keyword the scope rules print. -/
@[expose] public def HAlign.align : HAlign → String
  | .left => "left"
  | .center => "center"
  | .right => "right"

/-- How many halves of a line's slack stand before a box its scope sets: none
flush left, one centred, both flush right. -/
@[expose] public def HAlign.slackHalves : HAlign → Nat
  | .left => 0
  | .center => 1
  | .right => 2

/-- A box's offset inside the measure it stands in: its side's share of the
slack the box leaves. -/
public def HAlign.boxOffset (h : HAlign) (slack : Length) : Length := slack * h.slackHalves / 2

public theorem HAlign.boxOffset_between (h : HAlign) (s : Length) (hs : 0 ≤ s) :
    0 ≤ h.boxOffset s ∧ h.boxOffset s ≤ s := by
  cases h <;> simp only [boxOffset, slackHalves] <;> length_omega

/-- Which edge of the measure a ragged scope's lines hang from: `\raggedright`
is flush left, `\raggedleft` flush right. -/
public inductive FlushSide where
  | left
  | right
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The declared side as the side its boxes stand on. -/
@[expose] public def FlushSide.halign : FlushSide → HAlign
  | .left => .left
  | .right => .right

/-- The declared side in the `ElementStyle.align` vocabulary both backends read. -/
@[expose] public def FlushSide.align (s : FlushSide) : String := s.halign.align

/-- The declared side as the page's line origin. -/
public def FlushSide.flushRight : FlushSide → Bool
  | .left => false
  | .right => true

public theorem ragged_sides_agree (s : FlushSide) :
    s.flushRight = true ↔ s.align = "right" := by
  cases s <;> simp [FlushSide.flushRight, FlushSide.align, FlushSide.halign, HAlign.align]

/-- LaTeX's four ragged-setting spellings and the side each makes flush. -/
public def raggedSideOf? : String → Option FlushSide
  | "raggedright" | "flushleft" => some .left
  | "raggedleft" | "flushright" => some .right
  | _ => none

/-- A percentage track spelling shared by table targets and box tracks. -/
public def percentCss (permille : Nat) : String :=
  (if permille % 10 == 0 then s!"{permille / 10}"
   else s!"{permille / 10}.{permille % 10}") ++ "%"

/-- The total affine width a flexible table targets in its enclosing measure. -/
public inductive TableTarget where
  | sized (width : Affine Measure)
  deriving Repr, BEq, Inhabited

@[match_pattern, expose] public def TableTarget.frac (permille : Nat) : TableTarget :=
  .sized (Affine.scaleQ permille 1000 (.ref .lineWidth))

@[match_pattern, expose] public def TableTarget.abs (w : Length) : TableTarget :=
  .sized (.lit { width := .ofLength w })

public def TableTarget.resolve (target : TableTarget) (measure : Length) : Length :=
  match target with
  | .sized e => max 0 (e.resolveWidth (MeasureValues.horizontal measure 0))

/-- A table column's declared width: `natural` to the widest cell, `sized` an
affine length, `flex` an equal share of what fixed columns and gaps leave. -/
public inductive ColWidth where
  | natural
  | sized (width : Affine Measure)
  | flex (target : TableTarget)
  deriving Repr, BEq, Inhabited

@[match_pattern, expose] public def ColWidth.frac (permille : Nat) : ColWidth :=
  .sized (Affine.scaleQ permille 1000 (.ref .lineWidth))

@[match_pattern, expose] public def ColWidth.abs (w : Length) : ColWidth :=
  .sized (.lit { width := .ofLength w })

/-- A box's declared width (`{minipage}`, `\parbox`, `{column}`): `share` an
equal part of what declared boxes leave, `sized` an affine length. -/
public inductive BoxSize where
  | share
  | sized (width : Affine Measure)
  deriving Repr, BEq, Inhabited

@[match_pattern, expose] public def BoxSize.frac (permille : Nat) : BoxSize :=
  .sized (Affine.scaleQ permille 1000 (.ref .lineWidth))

@[match_pattern, expose] public def BoxSize.abs (w : Length) : BoxSize :=
  .sized (.lit { width := .ofLength w })

/-- Which point of a box stands on the baseline of its row, the `[pos]` it
declares; an undeclared box stands `top`. -/
public inductive BoxPos where
  | top
  | first
  | center
  | last
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a box in a row declares: its width, the point it stands on the row's baseline by, and the
box command (`\fbox`, `\colorbox`, `\fcolorbox`, `\raisebox`) it is set in, if any. -/
public structure BoxWidth where
  size : BoxSize
  pos : BoxPos := .top
  box : Option InlineBox := none
  /-- Whether the box opens as a minipage does, its first list spending no `\topsep` (latex.ltx
  `\@setminipage`). -/
  minipage : Bool := false
  deriving Repr, BEq, Inhabited

@[match_pattern, expose] public def BoxWidth.share : BoxWidth := ⟨.share, .top, none, false⟩
@[match_pattern, expose] public def BoxWidth.sized (width : Affine Measure) : BoxWidth :=
  ⟨.sized width, .top, none, false⟩
@[match_pattern, expose] public def BoxWidth.frac (permille : Nat) : BoxWidth :=
  ⟨.frac permille, .top, none, false⟩
@[match_pattern, expose] public def BoxWidth.abs (w : Length) : BoxWidth :=
  ⟨.abs w, .top, none, false⟩

/-- The declared width against a known measure: the width the box is set at. -/
public def BoxWidth.resolve (w : BoxWidth) (measure : Length) : Option Length :=
  match w.size with
  | .share => none
  | .sized e =>
    let values := MeasureValues.horizontal measure 0
    some (min measure (max 0 (e.resolveWidth values)))

/-- The declared width as a CSS grid track, structured, before it is spelled. -/
public inductive Track where
  | free
  | percent (permille : Nat)
  | length (l : Length)
  | affine (e : Affine Measure)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The track a declared width takes: a fraction a percentage, a length
itself, a shared column a free fraction of the leftover. -/
public def BoxWidth.trackOf (w : BoxWidth) : Track :=
  match w.size with
  | .share => .free
  | .sized e => .affine e

/-- One normalized CSS term from an affine box track. -/
private inductive TrackTerm where
  | length (l : Dim.SymLength)
  | measure (m : Measure) (num : Int) (den : Nat)

private def affineTrackTerms (e : Affine Measure) : Array TrackTerm := Id.run do
  let rec go (num : Int) (den : Nat) (out : Array TrackTerm) :
      Affine Measure → Array TrackTerm
    | .lit g => out.push (.length (g.width.scale num den))
    | .ref m => out.push (.measure m num den)
    | .scale n d e => go (num * n) (den * d) out e
    | .add a b => go num den (go num den out a) b
    | .sub a b => go (-num) den (go num den out a) b
  return go 1 1 #[] e

private def milliDecimal (n : Int) : String :=
  let sign := if n < 0 then "-" else ""
  let n := n.natAbs
  let whole := n / 1000
  let wholeText := toString whole
  let frac := n % 1000
  if frac == 0 then sign ++ wholeText
  else
    let digits := ((toString (1000 + frac)).drop 1).toString
    let digits := if digits.endsWith "00" then (digits.dropEnd 2).toString
      else if digits.endsWith "0" then (digits.dropEnd 1).toString else digits
    sign ++ wholeText ++ "." ++ digits

private def TrackTerm.css (horizontalUnit : String) : TrackTerm → Array String
  | .length l =>
    (if l.fixed == 0 then #[] else #[l.fixed.toBpString ++ "pt"]) ++
    (if l.em == 0 then #[] else #[milliDecimal l.em ++ "em"]) ++
    (if l.ex == 0 then #[] else #[milliDecimal l.ex ++ "ex"])
  | .measure m num den =>
    let unit := if m == .textHeight then "dvh" else horizontalUnit
    #[milliDecimal (num * 100000 / den) ++ unit]

private def affineTrackCss (e : Affine Measure) (horizontalUnit : String) : String :=
  let terms := (affineTrackTerms e).flatMap (TrackTerm.css horizontalUnit)
  match terms[0]? with
  | none => "0pt"
  | some first =>
    let body := (terms.extract 1 terms.size).foldl (fun out term =>
      if term.startsWith "-" then out ++ " - " ++ (term.drop 1).toString
      else out ++ " + " ++ term) first
    if terms.size == 1 then body else "calc(" ++ body ++ ")"

/-- One grid track, spelled in CSS. -/
public def Track.css : Track → String
  | .free => "1fr"
  | .percent p => percentCss p
  | .length l => l.toBpString ++ "pt"
  | .affine e => affineTrackCss e "%"

/-- An affine local measure in a property whose percentages would use the
wrong axis: `cqi` is the nearest query container's inline measure. -/
public def Track.contextCss (e : Affine Measure) : String :=
  affineTrackCss e "cqi"

/-- Spell a flexible table target from the same affine value layout resolves. -/
public def TableTarget.css : TableTarget → String
  | .sized e => Track.css (.affine e)

/-- Whether the declaration names a width at all. -/
public def BoxWidth.declared (w : BoxWidth) : Bool :=
  match w.size with
  | .share => false
  | .sized _ => true

/-- Whether this is the leftover's track, whose width is what the declared boxes leave. -/
public def Track.isFree : Track → Bool
  | .free => true
  | .percent _ | .length _ | .affine _ => false

public theorem boxWidth_tracks_agree (w : BoxWidth) (measure : Length) :
    (w.resolve measure).isSome = w.declared ∧
      w.trackOf.isFree = !w.declared := by
  rcases w with ⟨s, _⟩
  cases s <;> exact ⟨rfl, rfl⟩

/-- One column of a table, from the `tabular` column spec: a `p` column wraps
at its width, `l`/`c`/`r` cells set as one line. -/
public structure ColSpec where
  width : ColWidth
  align : HAlign
  /-- A wrapping column's paragraphs set ragged on `align`'s side, as a `>{…}` modifier declared. -/
  ragged : Bool := false
  /-- A natural column that narrows as a web table's does: a markdown table's. -/
  narrows : Bool := false
  deriving Repr, BEq, Inhabited

/-- Relative table-track hints in permille of the flexible target; `none` for a natural column. -/
public def tableColShares (cols : Array ColSpec) (target : TableTarget) : Array (Option Nat) :=
  match target with
  | .sized te =>
    match te.refPermille with
    | none => cols.map fun _ => none
    | some (tm, tperm) =>
      if tperm == 0 then cols.map fun _ => none
      else
        let count := cols.foldl (fun n c =>
          if c.width matches .flex _ then n + 1 else n) 0
        let sizedSum := cols.foldl (fun s c => match c.width with
          | .sized e => match e.refPermille with
            | some (m, p) => if m == tm then s + p * 1000 / tperm else s
            | none => s
          | .natural | .flex _ => s) 0
        let flexShare := if count == 0 then 0 else (1000 - min 1000 sizedSum) / count
        cols.map fun c => match c.width with
          | .natural => none
          | .sized e => e.refPermille.bind fun (m, p) =>
            if m == tm then some (p * 1000 / tperm) else none
          | .flex _ => some flexShare

public theorem tableColShares_natural_exact (cols : Array ColSpec) (target : TableTarget)
    (j : Nat) (c : ColSpec) (hget : cols[j]? = some c) (hc : c.width = .natural) :
    (tableColShares cols target)[j]? = some none := by
  unfold tableColShares
  repeat' split
  all_goals simp [hget, hc]

public theorem tableColShares_flex_contract (cols : Array ColSpec) (target : TableTarget)
    (i j : Nat) (ci cj : ColSpec) (ti tj : TableTarget)
    (hi : cols[i]? = some ci) (hj : cols[j]? = some cj)
    (hwi : ci.width = .flex ti) (hwj : cj.width = .flex tj) :
    (tableColShares cols target)[i]? = (tableColShares cols target)[j]? := by
  unfold tableColShares
  repeat' split
  all_goals simp [hi, hj, hwi, hwj]

/-- A horizontal rule or declared row gap inside a table, in booktabs' vocabulary. -/
public inductive TableRule where
  | top
  | mid
  | bottom
  | cmid (a : Nat) (b : Nat) (trimL : Bool) (trimR : Bool)
  | gap (space : SymGlue)
  /-- The row at its index sets no ink and takes no space, its cells only widening their columns, as
  a tabbing line `\kill` ends does. -/
  | measured
  deriving Repr, BEq, Inhabited

/-- The control a table row opens with when only its widths count (`TableRule.measured`), unforgeable
because it holds a space. -/
public def measuredRowMark : String := "measured row"

/-- `\multicolumn{n}{spec}{…}`: the cell at `col` of row `row` spans `n`
columns and sets by its own `spec`. -/
public structure ColSpan where
  row : Nat
  col : Nat
  n : Nat
  spec : ColSpec
  deriving Repr, BEq, Inhabited

/-- The `\multicolumn` head standing at cell `(i, j)`, if any. -/
public def cellSpan? (spans : Array ColSpan) (i j : Nat) : Option ColSpan :=
  spans.find? fun s => s.row == i && s.col == j

/-- The spec a cell sets by: a `\multicolumn` head's own, else its column's,
else a natural left one. -/
public def cellSpec (cols : Array ColSpec) (spans : Array ColSpan) (i j : Nat) : ColSpec :=
  match cellSpan? spans i j with
  | some s => s.spec
  | none => cols[j]?.getD { width := .natural, align := .left }

/-- The row index of the first `mid` rule in document order, if any. -/
public def firstMidRow : List (Nat × TableRule) → Option Nat
  | [] => none
  | (k, .mid) :: _ => some k
  | _ :: rest => firstMidRow rest

/-- booktabs' head: the rows before the first `\midrule`; no mid rule, no header. -/
public def tableHeaderRows {β : Type} (rows : Array (Array (Array β)))
    (rules : Array (Nat × TableRule)) : Nat :=
  ((firstMidRow rules.toList).map fun k => min k rows.size).getD 0

public theorem firstMidRow_eq_none_of_no_mid (rules : List (Nat × TableRule))
    (h : ∀ p ∈ rules, p.2 ≠ .mid) : firstMidRow rules = none := by
  induction rules with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, r⟩ := p
    have hp := h (k, r) (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, q.2 ≠ .mid := fun q hq => h q (List.mem_cons_of_mem _ hq)
    cases r with
    | mid => exact absurd rfl hp
    | top => exact ih hrest
    | bottom => exact ih hrest
    | cmid a b l rt => exact ih hrest
    | gap s => exact ih hrest
    | measured => exact ih hrest

public theorem tableHeaderRows_between {β : Type} (rows : Array (Array (Array β)))
    (rules : Array (Nat × TableRule)) :
    0 ≤ tableHeaderRows rows rules ∧ tableHeaderRows rows rules ≤ rows.size := by
  refine ⟨Nat.zero_le _, ?_⟩
  unfold tableHeaderRows
  cases firstMidRow rules.toList with
  | none => exact Nat.zero_le _
  | some k => exact Nat.min_le_right _ _

public theorem tableHeaderRows_zero_of_no_mid {β : Type} (rows : Array (Array (Array β)))
    (rules : Array (Nat × TableRule)) (h : ∀ p ∈ rules, p.2 ≠ .mid) :
    tableHeaderRows rows rules = 0 := by
  unfold tableHeaderRows
  rw [firstMidRow_eq_none_of_no_mid rules.toList
    (fun p hp => h p (Array.mem_toList_iff.mp hp))]
  rfl

/-- What a float wraps: `{figure}`, `{table}`, or a `{subfigure}`/`{subtable}` box inside one. -/
public inductive FloatKind where
  | figure
  | table
  | sub
  /-- An `{algorithm}` float, numbered by its own counter. -/
  | algorithm
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A captioned float's number: its count among its kind, within the chapter `within` names where
the class numbers floats by chapter. -/
public structure FloatNum where
  within : String := ""
  n : Nat
  /-- The chapter begun last, whose start restarts the count where it keeps its number. -/
  scope : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A literal number is a float's count outside any chapter. -/
public instance (n : Nat) : OfNat FloatNum n := ⟨{ n }⟩

/-- The number as the caption and a reference print it: `1`, or `2.1` in chapter 2. -/
public def FloatNum.render (f : FloatNum) : String :=
  if f.within.isEmpty then toString f.n else f.within ++ "." ++ toString f.n

public instance : ToString FloatNum := ⟨FloatNum.render⟩

/-- What an algorithm's input/output line declares (algorithm2e's
`\KwIn`/`\KwOut`/`\KwData`/`\KwResult`, algorithmicx's
`\Require`/`\Ensure`). -/
public inductive AlgIo where
  | input
  | output
  | data
  | result
  /-- The document's declared word, with the use site its ink is reported at. -/
  | named (label : String) (site : Option Span)
  /-- algorithm2e's `\SetKwInOut` word: set in a column as wide as the widest of `column`'s words
  with their colon, its own colon at the column's end and its content hanging past it. -/
  | aligned (label : String) (site : Option Span) (column : Array String)
  deriving Repr, BEq, Inhabited

/-- The block forms an algorithm line can open, onto which algorithm2e and
algorithmicx both parse. -/
public inductive AlgOpen where
  | forLoop
  | forEach
  | whileLoop
  | ifThen
  | elseIf
  | elseBranch
  | repeatLoop
  | function
  | procedure
  deriving Repr, BEq, Inhabited

/-- One pseudocode line's kind; its keywords are generated from the locale's keyword table. -/
public inductive AlgKind where
  | statement
  | io (kind : AlgIo)
  | opener (o : AlgOpen)
  | closer (o : AlgOpen)
  | ret
  deriving Repr, BEq, Inhabited

/-- The aligned io word a line opens with (`\SetKwInOut`), its site and its column's words. -/
public def AlgKind.aligned? : AlgKind → Option (String × Option Span × Array String)
  | .io (.aligned word site column) => some (word, site, column)
  | .io .input | .io .output | .io .data | .io .result | .io (.named _ _) => none
  | .statement | .opener _ | .closer _ | .ret => none

/-- One pseudocode line: its nesting depth, its kind, the author's content and
an optional end-of-line comment. -/
public structure AlgLine where
  depth : Nat
  kind : AlgKind
  content : Array Inline
  comment : Option (Array Inline)
  deriving Repr, BEq, Inhabited

/-- The algorithm keyword table for one language, from algorithm2e's own keyword defaults. -/
public structure AlgWords where
  forKw : String
  foreachKw : String
  whileKw : String
  doKw : String
  ifKw : String
  thenKw : String
  elseIfKw : String
  elseKw : String
  repeatKw : String
  untilKw : String
  endKw : String
  returnKw : String
  inputKw : String
  outputKw : String
  dataKw : String
  resultKw : String
  functionKw : String
  procedureKw : String
  deriving Repr, BEq, Inhabited

/-- The keyword table a locale tag selects: en, fr, de, any other tag English. -/
public def algWords (tag : String) : AlgWords :=
  match (tag.splitOn "-").headD tag with
  | "fr" =>
    { forKw := "pour", foreachKw := "pour chaque", whileKw := "tant que"
      doKw := "faire", ifKw := "si", thenKw := "alors"
      elseIfKw := "sinon si", elseKw := "sinon", repeatKw := "répéter"
      untilKw := "jusqu'à", endKw := "fin", returnKw := "retourner"
      inputKw := "Entrées", outputKw := "Sorties", dataKw := "Données"
      resultKw := "Résultat", functionKw := "Fonction"
      procedureKw := "Procédure" }
  | "de" =>
    { forKw := "für", foreachKw := "für jedes", whileKw := "solange"
      doKw := "tue", ifKw := "wenn", thenKw := "dann"
      elseIfKw := "sonst wenn", elseKw := "sonst", repeatKw := "wiederhole"
      untilKw := "bis", endKw := "Ende", returnKw := "zurück"
      inputKw := "Eingabe", outputKw := "Ausgabe", dataKw := "Daten"
      resultKw := "Ergebnis", functionKw := "Funktion"
      procedureKw := "Prozedur" }
  | _ =>
    { forKw := "for", foreachKw := "foreach", whileKw := "while"
      doKw := "do", ifKw := "if", thenKw := "then"
      elseIfKw := "else if", elseKw := "else", repeatKw := "repeat"
      untilKw := "until", endKw := "end", returnKw := "return"
      inputKw := "Input", outputKw := "Output", dataKw := "Data"
      resultKw := "Result", functionKw := "Function"
      procedureKw := "Procedure" }

/-- The opener's keyword pair: the word before the condition and the word after it. -/
public def AlgOpen.words (w : AlgWords) : AlgOpen → String × Option String
  | .forLoop => (w.forKw, some w.doKw)
  | .forEach => (w.foreachKw, some w.doKw)
  | .whileLoop => (w.whileKw, some w.doKw)
  | .ifThen => (w.ifKw, some w.thenKw)
  | .elseIf => (w.elseIfKw, some w.thenKw)
  | .elseBranch => (w.elseKw, none)
  | .repeatLoop => (w.repeatKw, none)
  | .function => (w.functionKw, none)
  | .procedure => (w.procedureKw, none)

/-- The io line's label word; a `named` label is the author's word as declared. -/
public def AlgIo.word (w : AlgWords) : AlgIo → String
  | .input => w.inputKw
  | .output => w.outputKw
  | .data => w.dataKw
  | .result => w.resultKw
  | .named label _ => label
  | .aligned label _ _ => label

/-- The opener's dump spelling, for goldens. -/
public def AlgOpen.name : AlgOpen → String
  | .forLoop => "for"
  | .forEach => "foreach"
  | .whileLoop => "while"
  | .ifThen => "if"
  | .elseIf => "elseif"
  | .elseBranch => "else"
  | .repeatLoop => "repeat"
  | .function => "function"
  | .procedure => "procedure"

/-- The io kind's dump spelling, for goldens. -/
public def AlgIo.name : AlgIo → String
  | .input => "input"
  | .output => "output"
  | .data => "data"
  | .result => "result"
  | .named label _ => s!"named {label.quote}"
  | .aligned label _ column => s!"aligned {label.quote} {column.toList.map String.quote}"

/-- The line kind's dump spelling, for goldens. -/
public def AlgKind.name : AlgKind → String
  | .statement => "statement"
  | .io k => s!"io {k.name}"
  | .opener o => s!"open {o.name}"
  | .closer o => s!"close {o.name}"
  | .ret => "return"

/-- A line's ink `out` closed as every backend closes it: `;` where `semi` and `semis` ask, then its
comment, muted. -/
public def AlgLine.close (semis : Bool) (muted : Color) (l : AlgLine) (semi : Bool)
    (out : Array Inline) : Array Inline :=
  let out := if semi && semis then out.push (.text ";") else out
  match l.comment with
  | some c =>
    (if out.isEmpty then out else out.push (.text " ")).push (.colored muted (some (.role .muted))
      (#[Inline.text "/* "] ++ c ++ #[Inline.text " */"]))
  | none => out

/-- One algorithm line as display inlines: keywords bold, the comment muted,
`semis` closing statements with `;`. -/
public def AlgLine.rendered (w : AlgWords) (semis : Bool) (muted : Color)
    (l : AlgLine) : Array Inline := Id.run do
  let bold (s : String) : Inline := .styled .bold #[.text s]
  let mut out : Array Inline := #[]
  let mut semi := false
  match l.kind with
  | .statement =>
    out := l.content
    semi := !l.content.all (· matches Inline.label _)
  | .io k =>
    let label := bold (k.word w ++ ":")
    out := #[(match k with
      | .named _ (some site) | .aligned _ (some site) _ => .located site #[label]
      | _ => label), .text " "] ++ l.content
  | .opener o =>
    let (lead, trail) := o.words w
    out := #[bold lead]
    unless l.content.isEmpty do
      out := out.push (.text " ") ++ l.content
    if let some t := trail then
      out := out ++ #[.text " ", bold t]
  | .closer o =>
    if o matches .repeatLoop then
      out := #[bold w.untilKw]
      unless l.content.isEmpty do
        out := out.push (.text " ") ++ l.content
      semi := true
    else
      out := #[bold w.endKw]
  | .ret =>
    out := #[bold w.returnKw]
    unless l.content.isEmpty do
      out := out.push (.text " ") ++ l.content
    semi := true
  return l.close semis muted semi out

/-- Pad each table row to `n` cells with empty cells. -/
public def padTableRows {β : Type} (rows : Array (Array (Array β))) (n : Nat) :
    Array (Array (Array β)) :=
  rows.map fun r => r ++ Array.replicate (n - r.size) #[]

public theorem padTableRows_rectangular {β : Type} (rows : Array (Array (Array β))) (n : Nat)
    (h : ∀ r ∈ rows, r.size ≤ n) :
    ∀ r ∈ padTableRows rows n, r.size = n := by
  intro r hr
  rw [padTableRows, Array.mem_map] at hr
  obtain ⟨r0, hmem, rfl⟩ := hr
  have hle := h r0 hmem
  simp [Array.size_append]
  omega

/-- A viewport-pinned placement for a web element: CSS `position: fixed` with
a declared corner and offset. -/
public structure Pin where
  /-- `true` pins to the top edge, `false` to the bottom. -/
  top : Bool
  /-- `true` pins to the left edge, `false` to the right. -/
  left : Bool
  offset : SymGlue := {}
  reveal : Bool := false
  revealBy : Option SymGlue := none
  deriving Repr, BEq, Inhabited

/-- What a `{nav}` landmark declares about itself beside its body; `label`
names the landmark instance (`aria-label`). -/
public structure NavSpec where
  label : Option String := none
  pin : Option Pin := none
  deriving Repr, BEq, Inhabited

/-- One reference-list entry, resolved: its key, the marker the style shows
beside it, and its content. -/
public structure BibItem where
  key : String
  marker : Option String
  content : Array Inline
  /-- Whether the label is one a BibTeX style writes (`\bibitem[label]`), set
  flush left in the label column. -/
  labelFlush : Bool := false
  deriving Repr, BEq, Inhabited

/-- The Pygments styles a listing may select, each painted from its own table. -/
public inductive ListingStyle where
  | default
  | friendly
  deriving Repr, BEq, Inhabited

/-- The style's Pygments name, the one spelling a document selects it by. -/
public def ListingStyle.name : ListingStyle → String
  | .default => "default"
  | .friendly => "friendly"

public def ListingStyle.all : List ListingStyle := [.default, .friendly]

public theorem ListingStyle.all_complete (s : ListingStyle) : s ∈ ListingStyle.all := by
  cases s <;> simp [ListingStyle.all]

public def ListingStyle.ofName? (name : String) : Option ListingStyle :=
  let name := name.trimAscii.toString
  ListingStyle.all.find? (·.name == name)

/-- How a listing's environment spaces it from its neighbours, as its package sets it. -/
public inductive ListingFrame where
  | none
  | trivlist
  | list
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The frame a listing stands in on a page: its environment's where the class
spaces it as TeX does, else `none`. -/
public def ListingFrame.onPage (surface : Surface) (lists : ListLineage) :
    ListingFrame → ListingFrame
  | .trivlist => if surface == .tex && lists != .web then .trivlist else .none
  | .list => if surface == .tex && lists != .web then .list else .none
  | .none => .none

/-- Where a listing the layout wraps itself (`ListingSpec.breakIndent`) may
end a line. -/
public inductive ListingWrap where
  /-- listings.sty's own rule (`breaklines`, default
  `breakatwhitespace=false`): a break after every output unit. -/
  | units
  /-- Whitespace first: the last space that fits, else the last fitting
  boundary between highlighter type runs. -/
  | whitespaceFirst
  deriving Repr, BEq, Inhabited

/-- What a code listing declares beside its content: the delta between
`{verbatim}` and `{lstlisting}` or `{minted}`. -/
public structure ListingSpec where
  /-- Source start for diagnostics on listing lines and tokens; it plays no
  part in highlighting, sizing or emission. -/
  source : Option Span := none
  caption : Option (Nat × Array Inline) := none
  numbers : Bool := false
  language : Option ListingLang := none
  /-- The highlighting style the document declared; `none` paints from the default style's table. -/
  style : Option ListingStyle := none
  /-- minted's `bgcolor`: the listing's own ground, with the name it was spelled by. -/
  ground : Option (Color × Option ColorRef) := none
  /-- One segment array per normalized source line; empty means plain text. -/
  highlight : Array (Array ListingHighlight.Token) := #[]
  /-- The listing's resolved size declaration; bare `verbatim` inherits the ambient size. -/
  fontSize : Style := .size "normalsize"
  /-- FancyVerb/listings default: eight columns between tab stops. -/
  tabSize : Nat := 8
  /-- FancyVerb/listings default: source lines do not wrap. -/
  breakLines : Bool := false
  /-- What the listing's package takes off the space after each source line:
  fvextra's `fvextraLineOverlap` for minted, else zero. -/
  lineOverlap : Length := 0
  /-- Whether every code line carries a `\strut`, as minted's lines under `breaklines` do. -/
  lineStrut : Bool := false
  /-- How far a wrapping listing's continuation stands in past its line's
  indentation (listings' `breakindent`). -/
  breakIndent : Option Length := none
  /-- Where the layout's own wrap may end a line. -/
  wrapAt : ListingWrap := .units
  /-- How the environment spaces the code from its neighbours. -/
  frame : ListingFrame := .none
  deriving Repr, BEq, Inhabited

/-- fvextra's `backgroundcolorboxoverlap`, 0.25 pt: the `\vspace` it takes
back after every source line. -/
public def fvextraLineOverlap : Length := Dim.pt 1 / 4

/-- listings.sty's continuation indent: `breakindent` defaults to 20 pt. -/
public def listingBreakIndent : Length := pt 20

/-- What a listing sets with before its own keys: LaTeX's defaults on tex;
`\footnotesize`, wrapped whitespace first, on markdown and code files. -/
public def Surface.listing : Surface → ListingSpec
  | .tex => {}
  | .markdown | .code _ =>
    { fontSize := .size "footnotesize", breakLines := true, breakIndent := some listingBreakIndent
      wrapAt := .whitespaceFirst }

/-- The declared language as the bare token, `none` when none is declared. -/
public def ListingSpec.langToken (spec : ListingSpec) : Option String :=
  spec.language.map (·.val)

/-- The declared language as the `code` element's class, `language-<token>`;
`none` when undeclared. -/
public def ListingSpec.htmlClass (spec : ListingSpec) : Option String :=
  spec.langToken.map ("language-" ++ ·)

/-- The declared language as a fenced code block's info string, empty when undeclared. -/
public def ListingSpec.fenceInfo (spec : ListingSpec) : String :=
  spec.langToken.getD ""

public theorem listing_language_agree (spec : ListingSpec) :
    (spec.language = none → spec.htmlClass = none ∧ spec.fenceInfo = "") ∧
    (∀ l, spec.language = some l →
      spec.htmlClass = some ("language-" ++ l.val) ∧ spec.fenceInfo = l.val) := by
  constructor
  · intro h
    simp [ListingSpec.htmlClass, ListingSpec.fenceInfo, ListingSpec.langToken, h]
  · intro l h
    simp [ListingSpec.htmlClass, ListingSpec.fenceInfo, ListingSpec.langToken, h]

/-- The step a laid-out paragraph's scopes stand in by: the standard classes' one-column
`\parindent`, 1.5em. -/
@[expose] public def linesStep : SymLength := { em := 1500 }

/-- One line of a laid-out paragraph: how many scopes hold it, each a `linesStep` in, and its
content. -/
public structure LaidLine where
  depth : Nat
  content : Array Inline
  deriving Repr, BEq, Inhabited

/-- The scopes a laid-out paragraph's line opens past a line at depth `prev` and closes before one
at depth `next`. -/
@[expose] public def LaidLine.bounds (l : LaidLine) (prev next : Nat) : Nat × Nat :=
  (l.depth - prev, l.depth - next)

/-- Which of LaTeX's three quotation environments a quote is, each a list of one item. -/
public inductive QuoteKind where
  /-- `quote`: both margins at the level's indent, its paragraphs `\parsep` apart. -/
  | quote
  /-- `quotation`: each paragraph's first line indented, no space between paragraphs. -/
  | quotation
  /-- `verse`: each line hung from a margin 1.5 em deeper, the lines no space apart. -/
  | verse
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

/-- The environment a quote kind is, as LaTeX spells it. -/
public def QuoteKind.name : QuoteKind → String
  | .quote => "quote"
  | .quotation => "quotation"
  | .verse => "verse"

/-- The kind an environment name opens, if it is one of the three. -/
public def QuoteKind.ofName? : String → Option QuoteKind
  | "quote" => some .quote
  | "quotation" => some .quotation
  | "verse" => some .verse
  | _ => none

public theorem QuoteKind.ofName?_name (k : QuoteKind) : ofName? k.name = some k := by
  cases k <;> rfl

/-- The vertical keys an environment's own list setting declares over its level's: quotation's
`\parsep 0pt plus 1pt`, verse's `\itemsep 0pt`, and under beamer verse's
`\parsep .75em plus .25em minus .25em` (classes.dtx, beamerbaselocalstructure.sty). -/
public def QuoteKind.own (l : ListLineage) : QuoteKind → ListSet
  | .quote => {}
  | .quotation => { parsep := some { stretch := Dim.SymLength.ofLength (Dim.pt 1) } }
  | .verse =>
    if l == .beamer then
      { itemsep := some {}
        parsep := some { width := { em := 750 }, stretch := { em := 250 }, shrink := { em := 250 } } }
    else { itemsep := some {} }

/-- How far verse's lines hang from its margin, its `\itemindent -1.5em` (classes.dtx). -/
public def verseHang : Dim.SymLength := { em := 1500 }

/-- A quote's environment and what it keeps of the lists around it over its level's, its
environment's own keys standing over both (`quoteSpacing`). -/
public structure QuoteSpec where
  kind : QuoteKind
  spacing : ListSet
  deriving Repr, BEq, Inhabited, Hashable

/-- The keys a quotation's environment declares at `\@listdepth` `level` where its lineage sets list
skips (`QuoteKind.own`); none on the web, whose lists declare over zero. -/
public def QuoteKind.ownAt (k : QuoteKind) (l : ListLineage) (size : Length) (level : Nat) : ListSet :=
  if (listSkips l size level).isSome then k.own l else {}

/-- A quotation's spacing and `\partopsep` at `\@listdepth` `level`: its level's under what it keeps
and its environment's own keys over both (`QuoteKind.ownAt`). -/
public def quoteSpacing (l : ListLineage) (size : Length) (level : Nat) (tokens : Tokens) (q : QuoteSpec) :
    Option (ListSkips × SymGlue) :=
  listSpacing l size level tokens (q.spacing.over (q.kind.ownAt l size level))

public theorem quoteSpacing_own_exact (l : ListLineage) (size : Length) (level : Nat) (tokens : Tokens)
    (q : QuoteSpec) (sk : ListSkips) (p : SymGlue) (hl : l ≠ .web)
    (h : quoteSpacing l size level tokens q = some (sk, p)) :
    (∀ g, (q.kind.own l).parsep = some g → sk.parsep = g) ∧
      (∀ g, (q.kind.own l).itemsep = some g → sk.itemsep = g) := by
  have hsome : (listSkips l size level).isSome := by
    cases l with
    | web => exact absurd rfl hl
    | beamer => rfl
    | sizeFile => unfold listSkips; dsimp only; split <;> rfl
  have hown : q.kind.ownAt l size level = q.kind.own l := by simp [QuoteKind.ownAt, hsome]
  unfold quoteSpacing at h
  rw [hown] at h
  obtain ⟨-, hi, hp, -⟩ := listSpacing_declared_exact l size level tokens _ sk p h
  exact ⟨fun g hg => hp g (by simp [ListSet.over, hg]), fun g hg => hi g (by simp [ListSet.over, hg])⟩

/-- How beamer's `\tableofcontents` options set an entry: as it stands, shaded, or hidden. -/
public inductive ContentsShow where
  | shown
  | shaded
  | hidden
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a `\tableofcontents` declares: the heading numbers in force where it stands, how beamer's
options set each heading about them, in beamerbasetoc.sty's order of its style keys' parts, and the
depth the contents list to. -/
public structure ContentsSpec where
  current : Nat × Nat × Nat := (0, 0, 0)
  sections : ContentsShow × ContentsShow := (.shown, .shown)
  subsections : ContentsShow × ContentsShow × ContentsShow := (.shown, .shown, .shown)
  subsubsections : ContentsShow × ContentsShow × ContentsShow × ContentsShow :=
    (.shown, .shown, .shown, .shown)
  depth : Int := 3
  /-- beamer's `sections=`: the section numbers listed, every one where none is given. -/
  listed : Option (List (Nat × Option Nat)) := none
  /-- beamer's `pausesections` and `pausesubsections`: a `\pause` before each section, or each
  subsection and subsubsection, entry, the first slide's counted from `\pause[0]`. -/
  pauses : Bool × Bool := (false, false)
  deriving Repr, BEq, Inhabited

/-- One entry of a table of contents: its depth, the number its heading prints, its title as
`\nameref` sets it, the anchor it opens where its heading has one, whether it is set shaded, and
the folio of the page its heading lands on, once a setting has placed it. -/
public structure ContentsEntry where
  depth : Nat
  number : Option String
  title : Array Inline
  target : Option String
  shaded : Bool
  page : Option String := none
  deriving Repr, BEq, Inhabited

/-- An entry's words as both backends set them: its title, linked to its heading's anchor where it
has one and the title has words to link. -/
@[expose] public def ContentsEntry.inline (e : ContentsEntry) : Array Inline :=
  match e.target with
  | some t => if e.title.isEmpty then e.title else #[.link ("#" ++ t) e.title]
  | none => e.title

/-- The share of its colour a shaded entry keeps over its ground: beamer's `sections/subsections in
toc shaded` default (beamerinnerthemedefault.sty). -/
@[expose] public def contentsShadeShare : Nat := 20

/-- Whether a deck's contents set a section entry after `\vskip1.5em` rather than `\vfill`: where
the subsections of the other sections hide (beamerbasetoc.sty). -/
@[expose] public def ContentsSpec.tightSections (spec : ContentsSpec) : Bool :=
  spec.subsections.2.2 == .hidden

/-- A deck's contents indent per depth, in thousandths of an em: the default inner theme's
`subsection in toc` `\leftskip=1.5em` (beamerinnerthemedefault.sty). -/
@[expose] public def deckContentsIndent : Nat := 1500

/-- One item of a deck's contents on its frame's vertical list: a skip, or an entry. -/
public inductive ContentsStep where
  | skip (g : SymGlue)
  | entry (e : ContentsEntry)
  deriving Repr, BEq, Inhabited

/-- A deck's contents as beamer sets them: `\vspace*{-.5em}`, each section's entry after `\vfill`
or, where the sections stand tight, `\vskip1.5em`, and a closing `\vfill` (beamerbasetoc.sty). -/
@[expose] public def deckContentsSteps (spec : ContentsSpec) (entries : Array ContentsEntry) :
    Array ContentsStep :=
  let before : SymGlue := if spec.tightSections then { width := { em := 1500 } } else { fil := true }
  #[.skip { width := { em := -500 } }] ++
    entries.flatMap (fun e => if e.depth == 0 then #[.skip before, .entry e] else #[.entry e]) ++
    #[.skip { fil := true }]

/-- Whether a contents step is a `\vfill`. -/
@[expose] public def ContentsStep.fills : ContentsStep → Bool
  | .skip g => g.fil
  | .entry _ => false

/-- The `\vfill`s a deck's contents set on its frame's list (`deckContentsSteps`). -/
@[expose] public def contentsFills (spec : ContentsSpec) (entries : Array ContentsEntry) : Nat :=
  ((deckContentsSteps spec entries).filter (·.fills)).size

/-- Where a flow's contents set an entry of one depth, in thousandths of an em: its indent and the
width its number takes (article.cls `\l@section`, `\l@subsection` and below). -/
public structure ContentsLevel where
  indent : Nat
  numWidth : Nat
  deriving Repr, BEq, Inhabited

/-- The box a flow's contents set a page's folio in, right-aligned, in thousandths of an em:
article.cls's `\@pnumwidth`. -/
@[expose] public def contentsPageWidth : Nat := 1550

/-- How far short of the measure a dotted contents entry's lines wrap, in thousandths of an em:
article.cls's `\@tocrmarg`. -/
@[expose] public def contentsRightMargin : Nat := 2550

/-- article.cls's levels, which report.cls's from its chapter at 0 follow down to the paragraph: a
section at 0 with 1.5em, a subsection at 1.5em with 2.3em, a subsubsection at 3.8em with 3.2em, a
paragraph at 7em with 4.1em, a subparagraph at 10em with 5em. -/
@[expose] public def contentsFlowLevel : Nat → ContentsLevel
  | 0 => ⟨0, 1500⟩
  | 1 => ⟨1500, 2300⟩
  | 2 => ⟨3800, 3200⟩
  | 3 => ⟨7000, 4100⟩
  | _ => ⟨10000, 5000⟩

public inductive Block where
  | para (content : Array Inline)
  /-- A paragraph laid out in lines, each under the last at the leading, continuing at its indent
  when it wraps; a scope is a run of lines deeper than the lines around it. -/
  | lines (lines : Array LaidLine)
  /-- A heading; `number` is the section's resolved number, assigned at
  elaboration in flow order. -/
  | section (level : HeadingLevel) (starred : Bool) (number : Option String) (title : Array Inline)
  /-- A list; `spacing` is what its scope and its own options declare over its level's. -/
  | list (ordered : Bool) (spacing : ListSet) (items : Array (Array Block))
  | center (body : Array Block)
  /-- Unjustified setting for a scope, hanging from the side it declares. -/
  | ragged (flush : FlushSide) (body : Array Block)
  /-- `\block[before = <len>]{...}`: content with declared space above. -/
  | spaced (before : Sourced SymGlue) (body : Array Block)
  /-- The block half of `Inline.role`: a document-defined command whose
  expansion is block content keeps its authored name. -/
  | role (name : String) (body : Array Block)
  /-- One hyperlink over block-shaped content, which holds no interactive descendant. -/
  | link (target : String) (body : Array Block)
  /-- `{quote}`, `{quotation}` or `{verse}`: one list level indented on both margins. -/
  | quote (spec : QuoteSpec) (body : Array Block)
  /-- `{abstract}`: article's unnumbered titled block, `\small` under a
  centred bold heading, on quotation margins. -/
  | abstract (body : Array Block)
  /-- beamer's titled block (`{block}`, `{alertblock}`, `{exampleblock}`); an
  empty title is an untitled block. -/
  | titled (kind : TitledKind) (title : Array Inline) (body : Array Block)
  /-- A disclosure (markdown's `<details>` and `<summary>`): a summary in view
  and a body the reader opens and closes; `expanded` is HTML's `open`. -/
  | disclosure (summary : Array Inline) (expanded : Bool) (body : Array Block)
  /-- A numbered display equation; `number` is the rendered tag, `content` the
  formula after its `\label` anchors. -/
  | equation (number : Array Inline) (content : Array Inline)
  /-- `{verbatim}` content, kept literally; `covered` is the overlay shade's
  dim colour, `spec` what a listing environment declares. -/
  | verbatim (covered : Option Color) (content : String) (spec : ListingSpec)
  /-- Pseudocode: the lines of an `{algorithm}`/`{algorithmic}` environment;
  `numbered` and `semis` follow algorithm2e's defaults. -/
  | algorithm (numbered : Bool) (semis : Bool) (lines : Array AlgLine)
  /-- Side-by-side boxes (`{columns}`/`{column}`, and the one-box `{minipage}`
  and `\parbox`), each with its declared width. -/
  | columns (cols : Array (BoxWidth × Array Block))
  /-- Overlay blocks crisp on the selector's steps (`\item<2->`, `\pause`):
  the block form of `Inline.onSteps`. -/
  | onSteps (spec : OverlaySpec) (body : Array Block)
  /-- Block-level overlay alternation: the block form of `Inline.altSteps`. -/
  | altSteps (spec : OverlaySpec) (firstPage : Array Block)
      (otherPage : Array Block)
  /-- A speaker note (`\note{...}`): a side channel, never slide content. -/
  | note (body : Array Block)
  /-- `{ifbackend}{html,md}`: content addressed to a subset of the backends,
  which each keeps or drops (`keepFor`). -/
  | only (targets : Array String) (body : Array Block)
  /-- `{nav}`: a navigation landmark, a group of links for page or site navigation. -/
  | nav (spec : NavSpec) (body : Array Block)
  /-- beamer's `\logo` in the body: the pages from here on carry this content
  at their lower-right corner; empty content clears it. -/
  | logo (content : Array Inline)
  /-- `\pagebreak`/`\newpage`: a declared page boundary. -/
  | pagebreak
  /-- One slide; `breakable` (`[allowframebreaks]`) lets it continue on
  further pages, and a frame without it that continues is a loss
  (`Layout.spill_accounts`). -/
  | frame (title : Array Inline) (standout : Bool) (valign : VAlign) (breakable : Bool)
      (body : Array Block)
  /-- `\framefoot{...}`: the footer note the frames from here on carry in the
  chrome footer's left slot; empty content clears it. -/
  | framefoot (content : Array Inline)
  /-- A palette epoch: the full palette state in force from here on, in flow order. -/
  | setPalette (pal : Palette)
  /-- Body `\tokens` (`\setlength` mid-document): the token state in force from here on. -/
  | setTokens (tokens : Tokens)
  /-- A full-measure horizontal rule, the title page's separator; `name` is
  the colour's palette entry, as on `.colored`. -/
  | rule (color : Color) (name : Option ColorRef) (thickness : Sourced SymGlue)
  /-- An elaborated `tikzpicture` subset: concrete shapes in picture
  coordinates, everything evaluated at elaboration. -/
  | picture (pic : Pic.Picture)
  /-- `{tabular}`: a formal table with booktabs' rules and no vertical rules;
  `rows` is rectangular, each cell its blocks (`cellOf`), and `padLeft`/`padRight` are the outer
  pads `@{}` deletes. -/
  | table (cols : Array ColSpec) (padLeft : Bool) (padRight : Bool)
      (rows : Array (Array (Array Block))) (rules : Array (Nat × TableRule))
      (spans : Array ColSpan)
  /-- `{figure}`/`{table}`: a captioned object standing where written;
  `capAbove` is source order, `num` its number among captioned floats of its
  kind. -/
  | float (kind : FloatKind) (num : Option FloatNum) (capAbove : Bool) (body : Array Block)
      (caption : Array Inline)
  /-- `\bibliography{src}`: the reference list, standing where the command was
  written; its items fill once the `.bib` is read. -/
  | bibliography (src : String) (style : Option String) (items : Array BibItem)
  /-- `\tableofcontents`: the headings it lists, standing where the command was written; its
  entries fill once the document's headings are known. -/
  | contents (spec : ContentsSpec) (entries : Array ContentsEntry)
  deriving Repr, Inhabited

deriving_structural_beq Block

/-- A table cell holding inline content alone: one paragraph, or nothing when empty. -/
@[expose] public def cellOf (xs : Array Inline) : Array Block :=
  if xs.isEmpty then #[] else #[.para xs]

/-- A cell's content when it is one paragraph or empty, as every inline cell is. -/
@[expose] public def cellLine? (cell : Array Block) : Option (Array Inline) :=
  match cell.toList with
  | [] => some #[]
  | [.para xs] => some xs
  | _ => none

/-- A cell's inline content, empty for a cell holding blocks. -/
@[expose] public def cellLine (cell : Array Block) : Array Inline :=
  (cellLine? cell).getD #[]

/-- Whether `b` is one of a float's marks after its caption below, `captionAtRole`'s or
`captionCloseRole`'s, alone or as the paragraph it stands in. -/
public def Block.captionMark (b : Block) : Bool :=
  let named (n : String) := n == captionCloseRole || n == captionAtRole
  match b with
  | .role n inner => named n ||
    (n == inParagraphRole && match inner.toList with
      | [.role c _] => named c
      | _ => false)
  | _ => false

/-- Whether `b` is the mark of a center closing after its float's caption (`captionCloseRole`). -/
public def Block.closesCaption (b : Block) : Bool :=
  match b with
  | .role n inner => n == captionCloseRole ||
    (n == inParagraphRole && match inner.toList with
      | [.role c _] => c == captionCloseRole
      | _ => false)
  | _ => false

/-- Whether `b` may stand after a float's caption below its object: a caption mark, a skip, or a
skip's marker. -/
public def Block.captionTailish (b : Block) : Bool :=
  b.captionMark || match b with
    | .spaced _ inner => inner.isEmpty
    | .role n inner => inner.isEmpty && (n == primitiveSkipRole || n == pageAnchorRole)
    | _ => false

/-- A float's body split where its caption below stood: the object, and from the first caption mark
among the marks and skips ending the body, what is set below the caption; `none` where no caption
mark ends the body. -/
public def captionTail? (capBelow : Bool) (body : Array Block) : Option (Array Block × Array Block) :=
  let run := (body.toList.reverse.takeWhile Block.captionTailish).reverse
  let k := body.size - run.length + (run.takeWhile (!·.captionMark)).length
  if capBelow && k < body.size then some (body.extract 0 k, body.extract k body.size) else none

/-- Whether a float's center closed after its caption below (`captionTail?`). -/
public def closesAfterCaption (capBelow : Bool) (body : Array Block) : Bool :=
  ((captionTail? capBelow body).map fun (_, after) => after.any Block.closesCaption).getD false

/-- Single-interval construction; union nodes use `onSteps` directly. -/
@[match_pattern, expose] public def Block.step (n : Nat) (last : Option Nat) (body : Array Block) : Block :=
  .onSteps ⟨n, last, [], false⟩ body

/-- Single-interval alternation, with the same page-order storage. -/
@[match_pattern, expose] public def Block.alt (n : Nat) (last : Option Nat)
    (firstPage otherPage : Array Block) : Block :=
  .altSteps ⟨n, last, [], false⟩ firstPage otherPage

/-- An alternation in source order, stored in page order. -/
public def Block.alternate (spec : OverlaySpec) (active otherwise : Array Block) : Block :=
  let (firstPage, otherPage) := spec.pageOrder active otherwise
  .altSteps spec firstPage otherPage

/-- Whether a block only sets the palette or the tokens from here on. -/
public def Block.epoch (b : Block) : Bool := b matches .setPalette _ || b matches .setTokens _

/-- How many epochs close a block list: a scope's restores, which stand after a box it sets. -/
public def closingEpochs (body : Array Block) : Nat :=
  (body.toList.reverse.takeWhile Block.epoch).length

/-- The position of the one box a block list sets beside its epochs, else the centre. -/
public def lonePos (body : Array Block) : BoxPos :=
  if let [.columns cols] := body.toList.filter (!·.epoch) then
    if let [(w, _)] := cols.toList then w.pos else .center
  else .center

/-- What a box command (`Ir.boxCommands`) sets around block content: a lone box it is set in, the
scope's closing epochs after it, else a box of its own holding the content. -/
public def boxedBlocks (b : InlineBox) (body : Array Block) : Array Block :=
  let core := body.extract 0 (body.size - closingEpochs body)
  let own : Array Block := #[.columns #[({ size := .share, pos := lonePos body, box := some b }, body)]]
  if let [.columns cols] := core.toList then
    if let [(w, inner)] := cols.toList then
      if w.box.isNone then
        #[.columns #[({ w with box := some b }, inner)]] ++ body.extract core.size body.size
      else own
    else own
  else own

/-- The role a picture standing alone in a display rides in. -/
public def displayPictureRole : String := "display-picture"

/-- Classify a display region: `none` when another semantic inline is present,
else whether a formula or display picture was found; hand-rolled, as it reads
through location and colour wrappers only. -/
-- conserves: none — a classifier.
public def displayParts : List Inline → Bool → Option Bool
  | [], seen => some seen
  | .formula true _ _ :: rest, _ | .math true _ :: rest, _ => displayParts rest true
  | .role n _ :: rest, _ => if n == displayPictureRole then displayParts rest true else none
  | .label _ :: rest, seen => displayParts rest seen
  | .located _ body :: rest, seen | .colored _ _ body :: rest, seen =>
    (displayParts body.toList seen).bind (displayParts rest)
  | _ :: _, _ => none
termination_by xs _ => sizeOf xs
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    have hb : sizeOf body = 1 + sizeOf body.toList := rfl
    omega

public theorem displayParts_location_exact (span : Span) (body : Array Inline) (seen : Bool) :
    displayParts [.located span body] seen = displayParts body.toList seen := by
  simp only [displayParts]
  cases displayParts body.toList seen <;> simp [displayParts]

/-- The environments `\@trivlist` spaces with `\partopsep` in vertical mode: a
list, a quote, the kernel's theorem, a trivlist and a listing framed as one. -/
public def Block.partopsepEnv : Block → Bool
  | .list .. | .quote _ _ => true
  | .verbatim _ _ spec => spec.frame == .trivlist
  | .role n _ => n == thmSpaceRole .kernel || n == trivlistRole
  | _ => false

/-- A block that, opening an item, a quotation or a trivlist, stands in its label, where
`\@noparlist` sets no skip above or below it: a list, a quote, a trivlist or a listing framed as
one. -/
public def Block.opensInLabel : Block → Bool
  | .list .. | .quote _ _ => true
  | .verbatim _ _ spec => spec.frame == .trivlist
  | .role n _ => n == trivlistRole
  | _ => false

mutual

/-- A block whose end leaves TeX's `\@endpe` set: a list, a quote, the
kernel's theorem, a trivlist or a framed listing, also in an in-paragraph
wrapper or last in a carrier. -/
public def Block.leavesEndPe : Block → Bool
  | .list .. | .quote _ _ => true
  | .verbatim _ _ spec => spec.frame == .trivlist || spec.frame == .list
  | .role n body =>
    thmSpaceOf? n == some .kernel || n == trivlistRole ||
      (n == inParagraphRole && match body with
        | #[b] => b.partopsepEnv
        | _ => false)
  | .onSteps _ body | .only _ body => leavesEndPeLast body.toList
  | _ => false

/-- Whether the last of a carrier's blocks leaves `\@endpe` set. -/
public def leavesEndPeLast : List Block → Bool
  | [] => false
  | [b] => b.leavesEndPe
  | _ :: b :: rest => leavesEndPeLast (b :: rest)

end

/-- A block `partopsepEnv` accepts, marked as opened inside a paragraph; anything else as it is. -/
public def inParagraph (b : Block) : Block :=
  if b.partopsepEnv then .role inParagraphRole #[b] else b

/-- A block that is a page-model mark: an empty block in a
`pageMarkerRole`. -/
@[expose] public def pageMarkerBlock : Block → Bool
  | .role n body => body.isEmpty && pageMarkerRole n
  | _ => false

/-- Whether an inline sets no ink: a label anchor, alone or under a style, colour, span or role. -/
@[expose] public def anchorInline : Inline → Bool
  | .label _ => true
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body =>
    body.attach.all fun ⟨x, _⟩ => anchorInline x
  | .text _ | .math _ _ | .formula _ _ _ | .link _ _ | .ref _ _ _ _ | .decorated _ _ | .boxed _ _ | .fill
  | .hspace _ _ | .rule _ _ _ | .pageNumber | .pageCount | .linebreak _ | .strut _ | .italicCorr _
  | .onSteps _ _ | .altSteps _ _ _ | .image _ _ _ | .icon _ _ | .cite _ _ | .cited .. | .footnote _ _ =>
    false

/-- A paragraph of label anchors alone, which sets no line. -/
@[expose] public def anchorsOnly (content : Array Inline) : Bool :=
  !content.isEmpty && content.all anchorInline

/-- Mark the block an environment arm pushed past `k` as opened inside a
paragraph when `inPar` says so. -/
public def markInParagraph (inPar : Bool) (k : Nat) (blocks : Array Block) : Array Block :=
  match inPar && blocks.size == k + 1, blocks.back? with
  | true, some b => blocks.pop.push (inParagraph b)
  | false, _ => blocks
  | true, none => blocks

/-- The last block at index `k` or above that ships content, reading through epochs. -/
public def lastContentFrom? (blocks : Array Block) (k : Nat) : Option Block :=
  go blocks.size
where
  /-- Scan down from index `i - 1`, no lower than `k`. -/
  go : Nat → Option Block
    | 0 => none
    | i + 1 =>
      if i < k then none
      else if blocks[i]?.any (· matches .setPalette _ | .setTokens _) then go i
      else blocks[i]?

public def lastContent? (blocks : Array Block) : Option Block := lastContentFrom? blocks 0

/-- Whether flushing the open paragraph left one with text, label anchors
aside, past the first `k` blocks. -/
public def flushedText (k : Nat) (after : Array Block) : Bool :=
  match lastContentFrom? after k with
  | some (.para content) => !content.all (· matches .label _)
  | _ => false

/-- Whether the last content of `blocks` leaves `\@endpe` set. -/
public def lastLeavesEndPe (blocks : Array Block) : Bool :=
  ((lastContent? blocks).map Block.leavesEndPe).getD false

/-- A description item's first paragraph split at its label: the label and the
text after it; `none` for any other paragraph. -/
public def descLabel? (content : Array Inline) : Option (Array Inline × Array Inline) :=
  match content[0]? with
  | some (Inline.role n label) =>
    if n == descLabelRole then some (label, content.extract 1 content.size) else none
  | _ => none

/-- An item's first paragraph split at the label its `\item[label]` declares: the label and the text
after it; `none` for any other paragraph. -/
public def itemLabel? (content : Array Inline) : Option (Array Inline × Array Inline) :=
  match content[0]? with
  | some (Inline.role n label) =>
    if n == itemLabelRole then some (label, content.extract 1 content.size) else none
  | _ => none

/-- The label an item's `\item[label]` declares, read through the overlay step covering the item. -/
public def itemLabelOf? (item : Array Block) : Option (Array Inline × Array Inline) :=
  match item[0]? with
  | some (Block.para c) => itemLabel? c
  | some (Block.onSteps _ body) => match body[0]? with
    | some (Block.para c) => itemLabel? c
    | _ => none
  | _ => none

/-- `\labelsep`: half an em (classes.dtx `\setlength\labelsep{.5em}`). -/
public def labelSepAt (size : Length) : Length := size / 2

/-- A centred block's body that is one display formula and nothing else, labels aside. -/
public def displayContent? (body : Array Block) : Option (Array Inline) :=
  match body.toList with
  | [.para content] =>
    if displayParts content.toList false == some true then
      some content
    else none
  | _ => none

public theorem displayContent_projects (body : Array Block) (content : Array Inline)
    (h : displayContent? body = some content) : body.toList = [.para content] := by
  unfold displayContent? at h
  split at h
  · rename_i heq
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact heq
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A display a picture stands for: a diagram the engine draws, alone in
`\[…\]` or an unnumbered alignment. -/
public def displayPicture? : Block → Option (Array Inline × Pic.Picture)
  | .role n body =>
    if n != displayPictureRole then none else
    match body.toList with
    | [.picture p] => some (#[], p)
    | [.para anchors, .picture p] =>
      if !anchors.isEmpty && anchors.all (· matches .label _) then some (anchors, p) else none
    | _ => none
  | _ => none

/-- The block a display picture is: the paragraph of its label anchors, if
any, then the picture in the display picture's role. -/
public def displayPictureBlock (keys : Array String) (p : Pic.Picture) : Block :=
  .role displayPictureRole
    ((if keys.isEmpty then #[] else #[.para (keys.map Inline.label)]).push (.picture p))

public theorem displayPicture?_block_id (keys : Array String) (p : Pic.Picture) :
    displayPicture? (displayPictureBlock keys p) = some (keys.map Inline.label, p) := by
  by_cases h : keys.isEmpty
  · have he : keys = #[] := by simpa using h
    subst he
    simp [displayPicture?, displayPictureBlock]
  · have hne : keys ≠ #[] := fun he => h (by simp [he])
    simp [displayPicture?, displayPictureBlock, h, hne]

public theorem displayPicture?_role_exact (n : String) (body : Array Block)
    (h : n ≠ displayPictureRole) : displayPicture? (.role n body) = none := by
  simp [displayPicture?, h]

/-- A display: the unnumbered shape, a picture standing for one, or a numbered equation. -/
public def Block.isDisplay : Block → Bool
  | .center body => (displayContent? body).isSome
  | .equation .. => true
  | b@(.role _ _) => (displayPicture? b).isSome
  | _ => false

/-- The context a display block carries, with the display itself; an unwrapped
display carries the default. -/
public def displayCtxOf (b : Block) : DisplayCtx × Block :=
  match b with
  | .role n body => match DisplayCtx.ofRole? n, body.toList with
    | some c, [d] => (c, d)
    | _, _ => ({}, b)
  | _ => ({}, b)

/-- Whether an environment opening past the first `k` blocks opens inside a paragraph: text
flushed before it, or a display whose paragraph runs on to it. -/
public def opensInParagraph (k : Nat) (after : Array Block) : Bool :=
  flushedText k after || (after.size == k && match lastContent? after with
    | some b => (displayCtxOf b).2.isDisplay && !(displayCtxOf b).1.parEnd
    | none => false)

/-- Whether the paragraph after `b` takes no first-line indent: after an environment's
`parContinuesRole` marker or a display its paragraph does not end at, as `\@endpe` sets it, or after
a heading, as `\@afterindentfalse` does. -/
public def Block.continuesPar (b : Block) : Bool :=
  match b with
  | .role n body =>
    if body.isEmpty then n == parContinuesRole
    else (displayCtxOf b).2.isDisplay && !(displayCtxOf b).1.parEnd
  | .section .. => true
  | _ => b.isDisplay

/-- Whether `b` is `parRunsOnRole`'s marker. -/
public def Block.runsOn : Block → Bool
  | .role n body => body.isEmpty && n == parRunsOnRole
  | _ => false

public theorem pageOpening_runsOn (n : String) (opening : PageOpening)
    (h : pageOpeningOfRole? n = some opening) : (Block.role n #[]).runsOn = false := by
  have hn : n ≠ parRunsOnRole := by
    intro e
    subst e
    simp [pageOpeningOfRole?, parRunsOnRole, titlePageBeginRole, titlePageEndRole] at h
  simp [Block.runsOn, hn]

/-- Whether a paragraph opens on a run-in heading (`runInHeadRole`). -/
public def opensRunIn (content : Array Inline) : Bool :=
  match (content[0]? : Option Inline) with
  | some (.role n _) => n == runInHeadRole
  | _ => false

/-- Whether `b` is a bare vertical skip, which leaves the paragraph state as TeX's vertical list
does. -/
public def Block.isSkip : Block → Bool
  | .spaced _ body => body.isEmpty
  | _ => false

public theorem pageOpening_continuesPar (n : String) (opening : PageOpening)
    (h : pageOpeningOfRole? n = some opening) : (Block.role n #[]).continuesPar = false := by
  have hn : n ≠ parContinuesRole := by
    intro e
    subst e
    simp [pageOpeningOfRole?, parContinuesRole, titlePageBeginRole, titlePageEndRole] at h
  simp [Block.continuesPar, hn]

/-- Record where the display an arm pushed past `k` stands in its paragraph (`DisplayCtx`). -/
public def markDisplay (inPar parEnd afterEnv : Bool) (k : Nat) (blocks : Array Block) : Array Block :=
  match blocks.size == k + 1, blocks.back? with
  | true, some b =>
    let (c, d) := displayCtxOf b
    if !d.isDisplay then blocks else
    let c := { c with inPar, parEnd, afterEnv }
    blocks.pop.push (if c == {} then d else .role c.role #[d])
  | _, _ => blocks

/-- A display in context `c`, wrapped in the role that names it; unwrapped in
the default context. -/
public def withDisplayCtx (c : DisplayCtx) (d : Block) : Block :=
  if c == {} then d else .role c.role #[d]

/-- A display opening a carrier in vertical mode, in the state the carrier
opened in — after a break inside it (`broken`), in no paragraph, and one no
outer carrier reaches; any other block as it is. -/
private def openDisplayAt (inPar endPe broken : Bool) (b : Block) : Block :=
  let (c, d) := displayCtxOf b
  if d.isDisplay && !c.inPar && !c.afterEnv && !c.afterBreak then
    withDisplayCtx
      { c with inPar := inPar, afterEnv := !inPar && endPe && !broken, afterBreak := broken } d
  else b

/-- A display closing a carrier with no break after it inside the carrier,
before the break after the carrier; any other block as it is. -/
private def closeDisplayAt (parEnd : Bool) (b : Block) : Block :=
  let (c, d) := displayCtxOf b
  if d.isDisplay && !c.parEnd then withDisplayCtx { c with parEnd := parEnd } d else b

mutual

/-- The opening half of `carrierDisplays` on a carrier's first block, whose display and nested
carriers open in the state the carrier opened in (`openDisplayAt`). -/
private def carrierOpenBlock (inPar endPe broken : Bool) : Block → Block
  | .altSteps s fa oa =>
    .altSteps s (carrierOpenList inPar endPe broken fa.toList).toArray
      (carrierOpenList inPar endPe broken oa.toList).toArray
  | .onSteps s body => .onSteps s (carrierOpenList inPar endPe broken body.toList).toArray
  | b@(.para ..) | b@(.section ..) | b@(.list ..) | b@(.center ..) | b@(.ragged ..) |
    b@(.spaced ..) | b@(.role ..) | b@(.link ..) | b@(.quote ..) | b@(.lines ..) | b@(.abstract ..) |
    b@(.titled ..) | b@(.disclosure ..) | b@(.equation ..) | b@(.verbatim ..) |
    b@(.algorithm ..) | b@(.columns ..) | b@(.note ..) | b@(.only ..) | b@(.nav ..) |
    b@(.logo ..) | b@(.pagebreak) | b@(.frame ..) | b@(.framefoot ..) | b@(.setPalette ..) |
    b@(.setTokens ..) | b@(.rule ..) | b@(.picture ..) | b@(.table ..) | b@(.float ..) |
    b@(.bibliography ..) | b@(.contents ..) =>
    openDisplayAt inPar endPe broken b

private def carrierOpenList (inPar endPe broken : Bool) : List Block → List Block
  | b :: rest => carrierOpenBlock inPar endPe broken b :: rest
  | [] => []

end

mutual

/-- The closing half of `carrierDisplays` on a carrier's last block: a
display takes the break after the carrier (`closeDisplayAt`), and a carrier
closing it closes before that break too. -/
private def carrierCloseBlock (parEnd : Bool) : Block → Block
  | .altSteps s fa oa =>
    .altSteps s (carrierCloseList parEnd fa.toList).toArray
      (carrierCloseList parEnd oa.toList).toArray
  | .onSteps s body => .onSteps s (carrierCloseList parEnd body.toList).toArray
  | b@(.para ..) | b@(.section ..) | b@(.list ..) | b@(.center ..) | b@(.ragged ..) |
    b@(.spaced ..) | b@(.role ..) | b@(.link ..) | b@(.quote ..) | b@(.lines ..) | b@(.abstract ..) |
    b@(.titled ..) | b@(.disclosure ..) | b@(.equation ..) | b@(.verbatim ..) |
    b@(.algorithm ..) | b@(.columns ..) | b@(.note ..) | b@(.only ..) | b@(.nav ..) |
    b@(.logo ..) | b@(.pagebreak) | b@(.frame ..) | b@(.framefoot ..) | b@(.setPalette ..) |
    b@(.setTokens ..) | b@(.rule ..) | b@(.picture ..) | b@(.table ..) | b@(.float ..) |
    b@(.bibliography ..) | b@(.contents ..) =>
    closeDisplayAt parEnd b

private def carrierCloseList (parEnd : Bool) : List Block → List Block
  | [] => []
  | [b] => [carrierCloseBlock parEnd b]
  | b :: rest => b :: carrierCloseList parEnd rest

end

/-- A carrier's displays stand in their paragraph as they would with no carrier there. -/
public def carrierDisplays (inPar endPe parEnd broken : Bool) (blocks : Array Block) :
    Array Block :=
  (carrierCloseList parEnd (carrierOpenList inPar endPe broken blocks.toList)).toArray

/-- The frames the deck numbers: every `.frame` except a standout frame and one its first mark
leaves unnumbered. -/
public def Block.countable : Block → Bool
  | .frame _ standout _ _ body => !standout &&
      !(body.toList.takeWhile (· matches .role _ #[])).contains (.role unnumberedRole #[])
  | _ => false

/-- Whether a block is a frame whose first marks set it `[plain]`. -/
public def Block.plainFrame : Block → Bool
  | .frame _ _ _ _ body => (body.toList.takeWhile (· matches .role _ #[])).contains (.role plainRole #[])
  | _ => false

/-- Whether a frame shows no number: a `[plain]` frame, which sets no footline, a standout frame,
whose furniture shows none, and a title page where the theme leaves it bare (`titled` false); every
other block. -/
public def Block.numberless (titled : Bool) : Block → Bool
  | b@(.frame _ standout valign _ _) =>
    b.plainFrame || standout || (!titled && (valign matches .golden))
  | _ => true

/-- The footline number fold: a frame showing a number shows the counter beamer's
`\insertframenumber` reads, the count of numbered frames up to it; every other block none. -/
public def shownFrom (titled : Bool) (k : Nat) : List Block → List (Option Nat)
  | [] => []
  | b :: rest =>
    let k' := if b.countable then k + 1 else k
    (if b.numberless titled then none else some k') :: shownFrom titled k' rest

public def countTrue : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + countTrue rest

/-- The numbering fold: masked positions take k+1, k+2, …; the rest take none. -/
public def numbersFrom (k : Nat) : List Bool → List (Option Nat)
  | [] => []
  | b :: rest =>
    if b then some (k + 1) :: numbersFrom (k + 1) rest
    else none :: numbersFrom k rest

public theorem numbers_gapless (k : Nat) (bs : List Bool) :
    (numbersFrom k bs).filterMap id = List.range' (k + 1) (countTrue bs) := by
  induction bs generalizing k with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | false => simp [numbersFrom, countTrue, ih]
    | true =>
      have h1 : countTrue (true :: rest) = countTrue rest + 1 := by
        simp [countTrue, Nat.add_comm]
      rw [h1]
      simp [numbersFrom, ih, List.range'_succ]

public theorem numbers_le_total (bs : List Bool) (n : Nat)
    (h : n ∈ (numbersFrom 0 bs).filterMap id) : n ≤ countTrue bs := by
  rw [numbers_gapless] at h
  have := List.mem_range'.mp h
  omega

public theorem last_number_is_total (bs : List Bool) (h : 0 < countTrue bs) :
    ((numbersFrom 0 bs).filterMap id).getLast? = some (countTrue bs) := by
  obtain ⟨m, hm⟩ : ∃ m, countTrue bs = m + 1 :=
    ⟨countTrue bs - 1, (Nat.succ_pred_eq_of_pos h).symm⟩
  rw [numbers_gapless, hm, List.range'_concat, List.getLast?_concat]
  exact congrArg some (by omega)

public theorem numbersFrom_isSome (k : Nat) (bs : List Bool) (i : Nat) :
    ((numbersFrom k bs)[i]?.getD none).isSome = (bs[i]?.getD false) := by
  induction bs generalizing k i with
  | nil => rfl
  | cons b rest ih =>
    cases i with
    | zero => cases b <;> simp [numbersFrom]
    | succ n => cases b <;> simp [numbersFrom, ih]

public theorem numbersFrom_length (k : Nat) (bs : List Bool) :
    (numbersFrom k bs).length = bs.length := by
  induction bs generalizing k with
  | nil => rfl
  | cons b rest ih => cases b <;> simp [numbersFrom, ih]

/-- One footnote mark's number against the counter: an override is itself and
steps nothing, as `\footnote[n]` does. -/
public def footnoteMark (k : Nat) (override : Option Nat) : Nat × Nat :=
  match override with
  | some n => (n, k)
  | none => (k + 1, k + 1)

/-- The footnote numbering fold: `footnoteMark` over the marks' overrides in flow order. -/
public def footnoteMarksFrom (k : Nat) : List (Option Nat) → List Nat
  | [] => []
  | o :: rest => (footnoteMark k o).1 :: footnoteMarksFrom (footnoteMark k o).2 rest

public theorem footnote_numbers_gapless (k : Nat) (os : List (Option Nat)) :
    ((os.zip (footnoteMarksFrom k os)).filterMap fun p =>
        if p.1.isSome then none else some p.2) =
      List.range' (k + 1) (countTrue (os.map (·.isNone))) := by
  have h : ∀ k, ((os.zip (footnoteMarksFrom k os)).filterMap fun p =>
      if p.1.isSome then none else some p.2) =
    (numbersFrom k (os.map (·.isNone))).filterMap id := by
    induction os with
    | nil => intro k; rfl
    | cons o rest ih =>
      intro k
      cases o <;> simp [footnoteMarksFrom, footnoteMark, numbersFrom, ih]
  rw [h, numbers_gapless]

private def frameMask (body : Array Block) : List Bool :=
  body.toList.map Block.countable

/-- The frame number each top-level block bears: `some k` for the k-th
countable frame, `none` for everything else. -/
public def frameNumbers (body : Array Block) : Array (Option Nat) :=
  (numbersFrom 0 (frameMask body)).toArray

/-- The number of countable frames in the body. -/
public def frameCount (body : Array Block) : Nat :=
  countTrue (frameMask body)

public theorem frameNumbers_numbered_iff_countable (body : Array Block) (i : Nat) :
    ((frameNumbers body)[i]?.getD none).isSome =
      ((body[i]?.map Block.countable).getD false) := by
  have h := numbersFrom_isSome 0 (frameMask body) i
  simpa [frameNumbers, frameMask, List.getElem?_map] using h

public theorem frameNumbers_gapless (body : Array Block) :
    (frameNumbers body).toList.filterMap id =
      List.range' 1 (frameCount body) := by
  simpa [frameNumbers, frameCount] using numbers_gapless 0 (frameMask body)

public theorem frameNumbers_le_count (body : Array Block) (n : Nat)
    (h : n ∈ (frameNumbers body).toList.filterMap id) : n ≤ frameCount body := by
  exact numbers_le_total (frameMask body) n (by simpa [frameNumbers] using h)

public theorem frameNumbers_last_is_count (body : Array Block)
    (h : 0 < frameCount body) :
    ((frameNumbers body).toList.filterMap id).getLast? =
      some (frameCount body) := by
  simpa [frameNumbers, frameCount] using
    last_number_is_total (frameMask body) (by simpa [frameCount] using h)

public theorem frameNumbers_size (body : Array Block) :
    (frameNumbers body).size = body.size := by
  simp [frameNumbers, frameMask, numbersFrom_length]

/-- The number each top-level block's footline shows (`shownFrom`). -/
public def frameShown (titled : Bool) (body : Array Block) : Array (Option Nat) :=
  (shownFrom titled 0 body.toList).toArray

/-- Each block shows none where it is numberless, else the count of numbered frames up to and
including it. -/
public theorem shownFrom_exact (t : Bool) (k : Nat) (bs : List Block) (i : Nat) :
    (shownFrom t k bs)[i]? = bs[i]?.map fun b =>
      if b.numberless t then none else some (k + countTrue ((bs.take (i + 1)).map Block.countable)) := by
  induction bs generalizing k i with
  | nil => simp [shownFrom]
  | cons b rest ih =>
    cases i with
    | zero => cases hc : b.countable <;> simp [shownFrom, countTrue, hc]
    | succ j =>
      have h := ih (if b.countable then k + 1 else k) j
      simp only [shownFrom, List.getElem?_cons_succ, List.take_succ_cons, List.map_cons, countTrue]
      rw [h]
      cases rest[j]? with
      | none => rfl
      | some c =>
        cases b.countable
        · simp
        · simp [Nat.add_assoc]

public theorem shownFrom_numbered (t : Bool) (k : Nat) (bs : List Block) (i n : Nat)
    (hn : (numbersFrom k (bs.map Block.countable))[i]? = some (some n))
    (hp : bs[i]?.map (Block.numberless t) = some false) :
    (shownFrom t k bs)[i]? = some (some n) := by
  induction bs generalizing k i with
  | nil => simp [numbersFrom] at hn
  | cons b rest ih =>
    cases i with
    | zero =>
      have hpb : b.numberless t = false := by simpa using hp
      cases hc : b.countable
      · simp [numbersFrom, hc] at hn
      · simp only [List.map_cons, numbersFrom, hc, ite_true, List.getElem?_cons_zero,
          Option.some.injEq] at hn
        simp [shownFrom, hc, hpb, hn]
    | succ j =>
      cases hc : b.countable
      · simp only [List.map_cons, numbersFrom, hc] at hn
        have := ih k j (by simpa using hn) (by simpa using hp)
        simpa [shownFrom, hc] using this
      · simp only [List.map_cons, numbersFrom, hc, ite_true] at hn
        have := ih (k + 1) j (by simpa using hn) (by simpa using hp)
        simpa [shownFrom, hc] using this

/-- A numbered frame that shows a number shows its own. -/
public theorem frameShown_numbered (t : Bool) (body : Array Block) (i n : Nat)
    (hn : (frameNumbers body)[i]? = some (some n))
    (hp : body[i]?.map (Block.numberless t) = some false) :
    (frameShown t body)[i]? = some (some n) := by
  have := shownFrom_numbered t 0 body.toList i n
    (by simpa [frameNumbers, frameMask] using hn) (by simpa using hp)
  simpa [frameShown] using this

/-- The counters `numberFloats` threads: captioned figures, tables and
algorithms, and captioned subfloats reset for every float body. -/
private structure FloatCtr where
  fig : Nat := 0
  tab : Nat := 0
  sub : Nat := 0
  alg : Nat := 0
  /-- The chapter the counters stand in, numbering by chapter, and the chapter begun last. -/
  within : String := ""
  scope : Nat := 0
  deriving Repr, BEq

private def FloatCtr.get : FloatCtr → FloatKind → Nat
  | c, .figure => c.fig
  | c, .table => c.tab
  | c, .sub => c.sub
  | c, .algorithm => c.alg

private def FloatCtr.bump : FloatCtr → FloatKind → FloatCtr
  | c, .figure => { c with fig := c.fig + 1 }
  | c, .table => { c with tab := c.tab + 1 }
  | c, .sub => { c with sub := c.sub + 1 }
  | c, .algorithm => { c with alg := c.alg + 1 }

mutual

/-- The numbering walk: every captioned float outside a speaker note takes the
next number of its kind in document order, a float's subfloats lettered from
one. -/
private def numberFloatList (within : Bool) (c : FloatCtr) (out : Array Block) :
    List Block → FloatCtr × Array Block
  | [] => (c, out)
  | b :: rest =>
    let (c2, b2) := numberFloatOne within c b
    numberFloatList within c2 (out.push b2) rest

private def numberFloatOne (within : Bool) (c : FloatCtr) : Block → FloatCtr × Block
  | .para content => (c, .para content)
  | .equation n content => (c, .equation n content)
  | .section l st num title => (c, .section l st num title)
  | .list o s items =>
    let (c2, items2) := numberFloatItems within c #[] items.toList
    (c2, .list o s items2)
  | .center body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .center body2)
  | .ragged s body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .ragged s body2)
  | .quote q body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .quote q body2)
  | .lines ls => (c, .lines ls)
  | .abstract body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .abstract body2)
  | .titled kind title body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .titled kind title body2)
  | .disclosure summary expanded body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .disclosure summary expanded body2)
  | .role n body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .role n body2)
  | .link target body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .link target body2)
  | .spaced g body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .spaced g body2)
  | .columns cols =>
    let (c2, cols2) := numberFloatCols within c #[] cols.toList
    (c2, .columns cols2)
  | .onSteps spec body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .onSteps spec body2)
  | .altSteps spec firstPage otherPage =>
    let (c2, active2) := numberFloatList within c #[] firstPage.toList
    let (c3, otherwise2) := numberFloatList within c2 #[] otherPage.toList
    (c3, .altSteps spec active2 otherwise2)
  | .only targets body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .only targets body2)
  | .nav spec body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .nav spec body2)
  | .frame t s v br body =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    (c2, .frame t s v br body2)
  | .note body => (c, .note body)
  | .verbatim k s sp => (c, .verbatim k s sp)
  | .logo content => (c, .logo content)
  | .framefoot content => (c, .framefoot content)
  | .setPalette p => (c, .setPalette p)
  | .setTokens tk => (c, .setTokens tk)
  | .pagebreak => (c, .pagebreak)
  | .rule col nm th => (c, .rule col nm th)
  | .picture p => (c, .picture p)
  | .table cols pl pr rows rules spans => (c, .table cols pl pr rows rules spans)
  | .algorithm n sm lines => (c, .algorithm n sm lines)
  | .bibliography src style items => (c, .bibliography src style items)
  | .contents spec entries => (c, .contents spec entries)
  | .float kind num capAbove body caption =>
    -- By chapter, a float of a chapter the counters have not stood in starts its kinds from one.
    let lab := (num.map (·.within)).getD ""
    let scope := (num.map (·.scope)).getD 0
    let byChapter := within && (kind == .figure || kind == .table)
    let c := if byChapter && (lab != c.within || scope != c.scope) then
      { c with fig := 0, tab := 0, within := lab, scope } else c
    let cAfter := if caption.isEmpty then c else c.bump kind
    let num := if caption.isEmpty then none
      else some ⟨if byChapter then lab else "", c.get kind + 1, if byChapter then scope else 0⟩
    let (cBody, body2) := numberFloatList within { cAfter with sub := 0 } #[] body.toList
    (⟨cBody.fig, cBody.tab, cAfter.sub, cBody.alg, cBody.within, cBody.scope⟩,
      .float kind num capAbove body2 caption)

private def numberFloatItems (within : Bool) (c : FloatCtr) (out : Array (Array Block)) :
    List (Array Block) → FloatCtr × Array (Array Block)
  | [] => (c, out)
  | item :: rest =>
    let (c2, item2) := numberFloatList within c #[] item.toList
    numberFloatItems within c2 (out.push item2) rest

private def numberFloatCols (within : Bool) (c : FloatCtr) (out : Array (BoxWidth × Array Block)) :
    List (BoxWidth × Array Block) → FloatCtr × Array (BoxWidth × Array Block)
  | [] => (c, out)
  | (w, body) :: rest =>
    let (c2, body2) := numberFloatList within c #[] body.toList
    numberFloatCols within c2 (out.push (w, body2)) rest

end

/-- By chapter, a captioned figure or table takes one past its kind's count in the chapter the
counters stand in, and one where its chapter began after them, a chapter keeping its number
included. -/
private theorem numberFloatOne_chapter_exact (c : FloatCtr) (kind : FloatKind) (f : FloatNum)
    (capAbove : Bool) (body : Array Block) (caption : Array Inline)
    (hk : kind = .figure ∨ kind = .table) (hcap : caption.isEmpty = false) :
    ∃ body2, (numberFloatOne true c (.float kind (some f) capAbove body caption)).2 =
      .float kind (some ⟨f.within,
        if f.within != c.within || f.scope != c.scope then 1 else c.get kind + 1, f.scope⟩)
        capAbove body2 caption := by
  rcases hk with rfl | rfl <;>
  · simp only [numberFloatOne, hcap]
    by_cases hw : f.within = c.within <;> by_cases hs : f.scope = c.scope <;>
      simp +decide [hw, hs, FloatCtr.get]

/-- The body's captioned floats numbered, by chapter where `within`, as a class with chapters
numbers them (`\@addtoreset`). -/
public def numberFloats (xs : Array Block) (within : Bool := false) : Array Block :=
  (numberFloatList within {} #[] xs.toList).2

public theorem numberFloats_para_exact (xs : Array Inline) (within : Bool) :
    numberFloats #[.para xs] within = #[.para xs] := by
  rfl

mutual

/-- The numbers the walk assigned to captioned floats of kind `k`, in document
order; for `.sub`, a body's own letters, not those of a nested float. -/
public def floatNumsList (k : FloatKind) (out : List Nat) : List Block → List Nat
  | [] => out
  | b :: rest => floatNumsList k (floatNumsOne k out b) rest

private def floatNumsOne (k : FloatKind) (out : List Nat) : Block → List Nat
  | .para _ => out
  | .equation _ _ => out
  | .section _ _ _ _ => out
  | .list _ _ items => floatNumsItems k out items.toList
  | .center body => floatNumsList k out body.toList
  | .ragged _ body => floatNumsList k out body.toList
  | .quote _ body => floatNumsList k out body.toList
  | .lines _ => out
  | .abstract body => floatNumsList k out body.toList
  | .titled _ _ body => floatNumsList k out body.toList
  | .disclosure _ _ body => floatNumsList k out body.toList
  | .role _ body => floatNumsList k out body.toList
  | .link _ body => floatNumsList k out body.toList
  | .spaced _ body => floatNumsList k out body.toList
  | .columns cols => floatNumsCols k out cols.toList
  | .onSteps _ body => floatNumsList k out body.toList
  | .altSteps _ firstPage otherPage =>
    floatNumsList k (floatNumsList k out firstPage.toList) otherPage.toList
  | .only _ body => floatNumsList k out body.toList
  | .nav _ body => floatNumsList k out body.toList
  | .frame _ _ _ _ body => floatNumsList k out body.toList
  | .note _ => out
  | .verbatim _ _ _ => out
  | .logo _ => out
  | .framefoot _ => out
  | .setPalette _ => out
  | .setTokens _ => out
  | .pagebreak => out
  | .rule _ _ _ => out
  | .picture _ => out
  | .table _ _ _ _ _ _ => out
  | .algorithm _ _ _ => out
  | .bibliography _ _ _ | .contents _ _ => out
  | .float kind num _ body _ =>
    let out := match num with
      | some n => if kind = k then out ++ [n.n] else out
      | none => out
    if k = .sub then out else floatNumsList k out body.toList

private def floatNumsItems (k : FloatKind) (out : List Nat) :
    List (Array Block) → List Nat
  | [] => out
  | item :: rest => floatNumsItems k (floatNumsList k out item.toList) rest

private def floatNumsCols (k : FloatKind) (out : List Nat) :
    List (BoxWidth × Array Block) → List Nat
  | [] => out
  | (_, body) :: rest => floatNumsCols k (floatNumsList k out body.toList) rest

end

private theorem floatNumsList_append (k : FloatKind) (out : List Nat)
    (l1 l2 : List Block) :
    floatNumsList k out (l1 ++ l2) = floatNumsList k (floatNumsList k out l1) l2 := by
  induction l1 generalizing out with
  | nil => simp [floatNumsList]
  | cons b rest ih => simp [floatNumsList, ih]

private theorem range'_glue (s m n : Nat) :
    List.range' s m ++ List.range' (s + m) n = List.range' s (m + n) :=
  List.range'_append_1 ..

mutual

private theorem numberFloatList_exact (k : FloatKind) (c : FloatCtr) (acc : Array Block)
    (out : List Nat) (bs : List Block) :
    ∃ n, ((numberFloatList false c acc bs).1).get k = c.get k + n ∧
      floatNumsList k out ((numberFloatList false c acc bs).2).toList
        = floatNumsList k out acc.toList ++ List.range' (c.get k + 1) n := by
  match bs with
  | [] => exact ⟨0, by simp [numberFloatList], by simp [numberFloatList]⟩
  | b :: rest =>
    obtain ⟨m, hcm, hnm⟩ :=
      numberFloatOne_exact k c (floatNumsList k out acc.toList) b
    obtain ⟨n, hcn, hnn⟩ := numberFloatList_exact k (numberFloatOne false c b).1
      (acc.push (numberFloatOne false c b).2) out rest
    refine ⟨m + n, ?_, ?_⟩
    · show ((numberFloatList false (numberFloatOne false c b).1
        (acc.push (numberFloatOne false c b).2) rest).1).get k = _
      rw [hcn, hcm, Nat.add_assoc]
    · show floatNumsList k out ((numberFloatList false (numberFloatOne false c b).1
        (acc.push (numberFloatOne false c b).2) rest).2).toList = _
      rw [hnn, Array.toList_push, floatNumsList_append]
      simp only [floatNumsList]
      rw [hnm, hcm, List.append_assoc,
        show c.get k + m + 1 = (c.get k + 1) + m by omega, range'_glue]

private theorem numberFloatOne_exact (k : FloatKind) (c : FloatCtr) (out : List Nat)
    (b : Block) :
    ∃ n, ((numberFloatOne false c b).1).get k = c.get k + n ∧
      floatNumsOne k out (numberFloatOne false c b).2
        = out ++ List.range' (c.get k + 1) n := by
  match b with
  | .para _ | .lines _ | .equation _ _ | .section _ _ _ _ | .note _ | .verbatim _ _ _ | .logo _
  | .algorithm _ _ _
  | .bibliography _ _ _ | .contents _ _
  | .framefoot _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ =>
    exact ⟨0, by simp [numberFloatOne], by simp [numberFloatOne, floatNumsOne]⟩
  | .list o _ items =>
    obtain ⟨n, hc, hn⟩ := numberFloatItems_exact k c #[] out items.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsItems] using hn⟩
  | .center body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .ragged _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .quote _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .abstract body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .titled _ _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .disclosure _ _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .role _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .link _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .spaced _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .columns cols =>
    obtain ⟨n, hc, hn⟩ := numberFloatCols_exact k c #[] out cols.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsCols] using hn⟩
  | .onSteps _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .altSteps _ firstPage otherPage =>
    obtain ⟨m, hcm, hnm⟩ := numberFloatList_exact k c #[] out firstPage.toList
    obtain ⟨p, hcp, hnp⟩ := numberFloatList_exact k
      (numberFloatList false c #[] firstPage.toList).1 #[]
      (floatNumsList k out (numberFloatList false c #[] firstPage.toList).2.toList)
      otherPage.toList
    refine ⟨m + p, ?_, ?_⟩
    · show ((numberFloatList false (numberFloatList false c #[] firstPage.toList).1 #[]
        otherPage.toList).1).get k = _
      rw [hcp, hcm, Nat.add_assoc]
    · show floatNumsList k (floatNumsList k out
        ((numberFloatList false c #[] firstPage.toList).2).toList)
        ((numberFloatList false (numberFloatList false c #[] firstPage.toList).1 #[]
          otherPage.toList).2).toList = _
      rw [hnp]
      simp only [floatNumsList]
      rw [hnm]
      simp only [floatNumsList]
      rw [hcm, List.append_assoc,
        show c.get k + m + 1 = (c.get k + 1) + m by omega, range'_glue]
  | .only _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .nav _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .frame _ _ _ _ body =>
    obtain ⟨n, hc, hn⟩ := numberFloatList_exact k c #[] out body.toList
    exact ⟨n, by simpa [numberFloatOne] using hc,
      by simpa [numberFloatOne, floatNumsOne, floatNumsList] using hn⟩
  | .float kind _ capAbove body caption =>
    by_cases hcap : caption.isEmpty
    ·
      obtain ⟨n, hc, hn⟩ :=
        numberFloatList_exact k { c with sub := 0 } #[] out body.toList
      cases k with
      | sub =>
        refine ⟨0, ?_, ?_⟩
        · simp [numberFloatOne, hcap, FloatCtr.get]
        · simp [numberFloatOne, floatNumsOne, hcap]
      | figure =>
        refine ⟨n, ?_, ?_⟩
        · simpa [numberFloatOne, hcap, FloatCtr.get] using hc
        · simpa [numberFloatOne, floatNumsOne, floatNumsList, hcap,
            FloatCtr.get] using hn
      | table =>
        refine ⟨n, ?_, ?_⟩
        · simpa [numberFloatOne, hcap, FloatCtr.get] using hc
        · simpa [numberFloatOne, floatNumsOne, floatNumsList, hcap,
            FloatCtr.get] using hn
      | algorithm =>
        refine ⟨n, ?_, ?_⟩
        · simpa [numberFloatOne, hcap, FloatCtr.get] using hc
        · simpa [numberFloatOne, floatNumsOne, floatNumsList, hcap,
            FloatCtr.get] using hn
    · cases k with
      | sub =>
        cases kind with
        | sub =>
          refine ⟨1, ?_, ?_⟩
          · simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump]
          · simp [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              List.range'_succ]
        | figure =>
          refine ⟨0, ?_, ?_⟩
          · simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump]
          · simp [numberFloatOne, floatNumsOne, hcap]
        | table =>
          refine ⟨0, ?_, ?_⟩
          · simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump]
          · simp [numberFloatOne, floatNumsOne, hcap]
        | algorithm =>
          refine ⟨0, ?_, ?_⟩
          · simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump]
          · simp [numberFloatOne, floatNumsOne, hcap]
      | figure =>
        cases kind with
        | figure =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .figure
            { c.bump .figure with sub := 0 } #[] (out ++ [c.get .figure + 1])
            body.toList
          refine ⟨n + 1, ?_, ?_⟩
          · have := hc
            simp only [FloatCtr.get, FloatCtr.bump] at this ⊢
            simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump, this]
            omega
          · have := hn
            simp only [FloatCtr.get, FloatCtr.bump] at this
            simp [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList, this, List.append_assoc]
            rw [List.range'_succ]
        | table =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .figure
            { c.bump .table with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | sub =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .figure
            { c.bump .sub with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | algorithm =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .figure
            { c.bump .algorithm with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
      | table =>
        cases kind with
        | table =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .table
            { c.bump .table with sub := 0 } #[] (out ++ [c.get .table + 1])
            body.toList
          refine ⟨n + 1, ?_, ?_⟩
          · have := hc
            simp only [FloatCtr.get, FloatCtr.bump] at this ⊢
            simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump, this]
            omega
          · have := hn
            simp only [FloatCtr.get, FloatCtr.bump] at this
            simp [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList, this, List.append_assoc]
            rw [List.range'_succ]
        | figure =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .table
            { c.bump .figure with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | sub =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .table
            { c.bump .sub with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | algorithm =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .table
            { c.bump .algorithm with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
      | algorithm =>
        cases kind with
        | algorithm =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .algorithm
            { c.bump .algorithm with sub := 0 } #[] (out ++ [c.get .algorithm + 1])
            body.toList
          refine ⟨n + 1, ?_, ?_⟩
          · have := hc
            simp only [FloatCtr.get, FloatCtr.bump] at this ⊢
            simp [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump, this]
            omega
          · have := hn
            simp only [FloatCtr.get, FloatCtr.bump] at this
            simp [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList, this, List.append_assoc]
            rw [List.range'_succ]
        | figure =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .algorithm
            { c.bump .figure with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | table =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .algorithm
            { c.bump .table with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn
        | sub =>
          obtain ⟨n, hc, hn⟩ := numberFloatList_exact .algorithm
            { c.bump .sub with sub := 0 } #[] out body.toList
          refine ⟨n, ?_, ?_⟩
          · simpa [numberFloatOne, hcap, FloatCtr.get, FloatCtr.bump] using hc
          · simpa [numberFloatOne, floatNumsOne, hcap, FloatCtr.get,
              FloatCtr.bump, floatNumsList] using hn

private theorem numberFloatItems_exact (k : FloatKind) (c : FloatCtr)
    (acc : Array (Array Block)) (out : List Nat) (items : List (Array Block)) :
    ∃ n, ((numberFloatItems false c acc items).1).get k = c.get k + n ∧
      floatNumsItems k out ((numberFloatItems false c acc items).2).toList
        = floatNumsItems k out acc.toList ++ List.range' (c.get k + 1) n := by
  match items with
  | [] => exact ⟨0, by simp [numberFloatItems], by simp [numberFloatItems]⟩
  | item :: rest =>
    obtain ⟨m, hcm, hnm⟩ := numberFloatList_exact k c #[]
      (floatNumsItems k out acc.toList) item.toList
    obtain ⟨n, hcn, hnn⟩ := numberFloatItems_exact k
      (numberFloatList false c #[] item.toList).1
      (acc.push (numberFloatList false c #[] item.toList).2) out rest
    refine ⟨m + n, ?_, ?_⟩
    · show ((numberFloatItems false (numberFloatList false c #[] item.toList).1
        (acc.push (numberFloatList false c #[] item.toList).2) rest).1).get k = _
      rw [hcn, hcm, Nat.add_assoc]
    · show floatNumsItems k out ((numberFloatItems false (numberFloatList false c #[] item.toList).1
        (acc.push (numberFloatList false c #[] item.toList).2) rest).2).toList = _
      rw [hnn, Array.toList_push]
      have happ : ∀ (l1 : List (Array Block)) (o : List Nat) (x : Array Block),
          floatNumsItems k o (l1 ++ [x])
            = floatNumsList k (floatNumsItems k o l1) x.toList := by
        intro l1 o x
        induction l1 generalizing o with
        | nil => simp [floatNumsItems]
        | cons y rest ih => simp [floatNumsItems, ih]
      rw [happ]
      simp only [floatNumsList] at hnm
      rw [hnm, hcm, List.append_assoc,
        show c.get k + m + 1 = (c.get k + 1) + m by omega, range'_glue]

private theorem numberFloatCols_exact (k : FloatKind) (c : FloatCtr)
    (acc : Array (BoxWidth × Array Block)) (out : List Nat)
    (cols : List (BoxWidth × Array Block)) :
    ∃ n, ((numberFloatCols false c acc cols).1).get k = c.get k + n ∧
      floatNumsCols k out ((numberFloatCols false c acc cols).2).toList
        = floatNumsCols k out acc.toList ++ List.range' (c.get k + 1) n := by
  match cols with
  | [] => exact ⟨0, by simp [numberFloatCols], by simp [numberFloatCols]⟩
  | (w, body) :: rest =>
    obtain ⟨m, hcm, hnm⟩ := numberFloatList_exact k c #[]
      (floatNumsCols k out acc.toList) body.toList
    obtain ⟨n, hcn, hnn⟩ := numberFloatCols_exact k
      (numberFloatList false c #[] body.toList).1
      (acc.push (w, (numberFloatList false c #[] body.toList).2)) out rest
    refine ⟨m + n, ?_, ?_⟩
    · show ((numberFloatCols false (numberFloatList false c #[] body.toList).1
        (acc.push (w, (numberFloatList false c #[] body.toList).2)) rest).1).get k = _
      rw [hcn, hcm, Nat.add_assoc]
    · show floatNumsCols k out ((numberFloatCols false (numberFloatList false c #[] body.toList).1
        (acc.push (w, (numberFloatList false c #[] body.toList).2)) rest).2).toList = _
      rw [hnn, Array.toList_push]
      have happ : ∀ (l1 : List (BoxWidth × Array Block)) (o : List Nat)
          (x : BoxWidth × Array Block),
          floatNumsCols k o (l1 ++ [x])
            = floatNumsList k (floatNumsCols k o l1) x.2.toList := by
        intro l1 o x
        induction l1 generalizing o with
        | nil => simp [floatNumsCols]
        | cons y rest ih => simp [floatNumsCols, ih]
      rw [happ]
      simp only [floatNumsList] at hnm
      rw [hnm, hcm, List.append_assoc,
        show c.get k + m + 1 = (c.get k + 1) + m by omega, range'_glue]

end

public theorem numberFloats_exact (k : FloatKind) (xs : Array Block) :
    floatNumsList k [] (numberFloats xs).toList
      = List.range' 1 (floatNumsList k [] (numberFloats xs).toList).length := by
  obtain ⟨n, _, hn⟩ := numberFloatList_exact k {} #[] [] xs.toList
  have h0 : (({} : FloatCtr)).get k = 0 := by cases k <;> rfl
  have hnums : floatNumsList k [] (numberFloats xs).toList = List.range' 1 n := by
    simpa [numberFloats, floatNumsList, h0] using hn
  rw [hnums, List.length_range']

private theorem numberFloats_sub_letters (c : FloatCtr) (body : Array Block) :
    floatNumsList .sub []
        ((numberFloatList false { c with sub := 0 } #[] body.toList).2).toList
      = List.range' 1
        (((numberFloatList false { c with sub := 0 } #[] body.toList).1).get .sub) := by
  obtain ⟨n, hc, hn⟩ :=
    numberFloatList_exact .sub { c with sub := 0 } #[] [] body.toList
  have h0 : (({ c with sub := 0 } : FloatCtr)).get .sub = 0 := by rfl
  rw [h0] at hc hn
  simpa [floatNumsList, hc] using hn

/-- A subfloat's letter, `\alph` (1 → a, …, 26 → z); past 26 the number itself. -/
public def subLetter (n : Nat) : String :=
  if 1 ≤ n && n ≤ 26 then String.ofList [Char.ofNat (96 + n)] else s!"{n}"

/-- The caption's number prefix, derived from the node, as article's `\@makecaption` sets it. -/
public def captionPrefix (loc : Locale) (kind : FloatKind) (num : Option FloatNum) : Option String :=
  num.map fun n =>
    match kind with
    | .figure => s!"{loc.figure} {n.render}: "
    | .table => s!"{loc.table} {n.render}: "
    | .algorithm => s!"{loc.algorithm} {n.render}: "
    | .sub => s!"({subLetter n.n}) "

/-- A caption with its number prefix set in front. -/
public def numberedCaption (loc : Locale) (kind : FloatKind) (num : Option FloatNum)
    (caption : Array Inline) : Array Inline :=
  match captionPrefix loc kind num with
  | some p => (Inline.text p :: caption.toList).toArray
  | none => caption

/-- The float type a caption setting may be scoped to, as the caption package
names it (`\captionsetup[table]{...}`). -/
public def FloatKind.captionScope : FloatKind → String
  | .figure => "figure"
  | .table => "table"
  | .sub => "sub"
  | .algorithm => "algorithm"

/-- The kind a caption package float type names, if the engine has it. -/
public def FloatKind.ofCaptionType? : String → Option FloatKind
  | "figure" => some .figure
  | "table" => some .table
  | "sub" | "subfigure" | "subtable" => some .sub
  | "algorithm" => some .algorithm
  | _ => none

/-- A caption token as one float kind reads it: the kind's own
(`tablecaptionsep`), else the document's (`captionsep`). -/
public def captionTokenOf (tokens : Tokens) (kind : FloatKind) (key : String) : Option SymGlue :=
  tokens.find? (kind.captionScope ++ key) <|> tokens.find? key

/-- Where a document tells the caption package a float type's captions stand
(`position`); `auto` is the package's default. -/
public inductive CaptionPos where
  | top
  | bottom
  | auto
  deriving Repr, BEq, Inhabited

/-- A position as caption3.sty spells it: `top`, `t`, `above`; `bottom`,
`b`, `below`; `auto`, `a`. -/
public def CaptionPos.ofKey? : String → Option CaptionPos
  | "top" | "t" | "above" => some .top
  | "bottom" | "b" | "below" => some .bottom
  | "auto" | "a" => some .auto
  | _ => none

/-- `\caption@iftop`: whether a caption on `capAbove`'s side is placed as a top one. -/
public def CaptionPos.placedTop : CaptionPos → Bool → Bool
  | .top, _ => true
  | .bottom, _ => false
  | .auto, capAbove => capAbove

/-- The position a float kind's captions are placed for in a class's lineage,
where the document declares none. -/
public def captionPosFor (l : ListLineage) (decl : Array (String × CaptionPos))
    (kind : FloatKind) : CaptionPos :=
  match (decl.find? (·.1 == kind.captionScope)) <|> (decl.find? (·.1 == "")), l with
  | some (_, p), _ => p
  | none, .beamer => .bottom
  | none, .sizeFile | none, .web => .auto

/-- LaTeX's two caption skips: `above` is `\abovecaptionskip` (the engine's
`captionsep`), `below` is `\belowcaptionskip`. -/
public inductive CaptionSkip where
  | above
  | below
  deriving Repr, BEq, Inhabited

/-- The tokens a skip reads for a float kind, the kind's own before the document's. -/
public def CaptionSkip.keys (s : CaptionSkip) (kind : FloatKind) : List String :=
  let base := match s with
    | .above => "captionsep"
    | .below => "belowcaptionskip"
  [kind.captionScope ++ base, base]

/-- A skip's declared value for a float kind, if the document declares one. -/
public def CaptionSkip.find? (s : CaptionSkip) (tokens : Tokens) (kind : FloatKind) : Option SymGlue :=
  (s.keys kind).findSome? tokens.find?

/-- A skip's value where the document declares none. -/
public def CaptionSkip.default (s : CaptionSkip) (size : Length) : SymGlue :=
  match s with
  | .above => captionSepDefault size
  | .below => {}

/-- A skip's value where the document declares none, in a class's lineage:
beamer sets both to 7 pt. -/
public def CaptionSkip.defaultFor (l : ListLineage) (s : CaptionSkip) (size : Length) : SymGlue :=
  match l with
  | .beamer => { width := { fixed := Dim.pt 7 } }
  | .sizeFile | .web => s.default size

/-- Every token name an engine site reads, the names a document's length reaches the engine by. -/
public def engineTokenNames : List String :=
  let kinds : List FloatKind := [.figure, .table, .sub, .algorithm]
  [trivlistSkipName, "partopsep", "itemsep", "trivlist-topsep", "trivlist-partopsep", "trivlist-itemsep",
   "floatsep", "footins", bibHangName, bibSepName,
   displaySkipAbove, displaySkipBelow, displaySkipAboveShort, displaySkipBelowShort,
   "smallskipamount", "medskipamount", "bigskipamount", "fboxsep", "fboxrule", "headsep", "footskip",
   "topskip",
   "progressheight", "frametitlepadding", "algindent", "algnumindent", "subtitlegap",
   "separatorheight", "separatorgap", "authorgap", "institutegap", "captionmargin"] ++
    ([1, 2, 3, 4, 5, 6].map leftMarginName) ++ tableLengths.map (·.1) ++
    kinds.map (·.captionScope ++ "captionmargin") ++
    [CaptionSkip.above, CaptionSkip.below].flatMap fun s => kinds.flatMap s.keys

/-- A caption's two skips, by the side it stands on and the side it is placed
for: the object side's, then the text side's. -/
public def captionSides (pos : CaptionPos) (capAbove : Bool) : CaptionSkip × CaptionSkip :=
  if pos.placedTop capAbove == capAbove then (.above, .below) else (.below, .above)

/-- A listing caption with its number prefix in front, as "Listing 1: text". -/
-- conserves: none — the prefix is furniture added at emission.
public def listingCaption (loc : Locale) (n : Nat) (caption : Array Inline) : Array Inline :=
  (Inline.text s!"{loc.listing} {n}: " :: caption.toList).toArray

/-- Verbatim content split into lines, without the newline after
`\begin{verbatim}` and the blank tail before `\end{verbatim}`. -/
public def verbatimLines (s : String) : Array String := Id.run do
  let s := if s.startsWith "\n" then (s.drop 1).toString
    else if s.startsWith "\r\n" then (s.drop 2).toString else s
  let lines := ((s.splitOn "\n").map fun l =>
    if l.endsWith "\r" then (l.dropEnd 1).toString else l).toArray
  return lines.popWhile (·.trimAscii.isEmpty)

/-- The listing's classified source lines; a cache that does not match the
source falls back to plain text. -/
public def ListingSpec.tokenLines (spec : ListingSpec) (source : String) :
    Array (Array ListingHighlight.Token) :=
  if spec.highlight.map ListingHighlight.lineText = verbatimLines source then
    spec.highlight
  else
    (verbatimLines source).map fun line => #[{ text := line }]

public theorem listing_source_exact (spec : ListingSpec) (source : String) :
    (spec.tokenLines source).map ListingHighlight.lineText = verbatimLines source := by
  unfold ListingSpec.tokenLines
  split
  · assumption
  · simp [Array.map_map, Function.comp_def, ListingHighlight.lineText]

/-- A listing segment's layout spelling and next display column, with TABs
advanced to the next stop. -/
public def ListingSpec.layoutText (spec : ListingSpec) (column : Nat) (s : String) :
    String × Nat :=
  s.foldl (fun (out, col) c =>
    let space := if spec.breakLines && col > 0 then ' ' else '\u00a0'
    if c == '\t' then
      let width := max 1 spec.tabSize
      let count := width - col % width
      (out ++ String.ofList (List.replicate count space), col + count)
    else (out.push (if c == ' ' then space else c), col + 1)) ("", column)

/-- Verbatim content as inline text: tabs to the declared stops, source lines
joined by forced breaks, a blank line kept as one no-break space. -/
public def verbatimInlines (s : String) (spec : ListingSpec := {}) : Array Inline := Id.run do
  let mut out : Array Inline := #[]
  for line in verbatimLines s do
    unless out.isEmpty do
      out := out.push (.linebreak {})
    let kept := (spec.layoutText 0 line).1
    out := out.push (.text (if kept.isEmpty then "\u00a0" else kept))
  return out

/-- Where a heading rule stands against the heading's baseline; `xHeight`
raises it half the heading face's x-height. -/
public inductive RulePosition where
  | xHeight
  | baseline
  deriving Repr, BEq, Inhabited, DecidableEq

/-- How far above the baseline a heading rule's bottom edge stands, from its
position and the heading face's x-height. -/
public def RulePosition.raise : RulePosition → Length → Length
  | .xHeight, xh => xh / 2
  | .baseline, _ => 0

public theorem heading_rule_position_exact (xh : Length) :
    RulePosition.raise .baseline xh = 0 ∧ RulePosition.raise .xHeight xh = xh / 2 :=
  ⟨rfl, rfl⟩

/-- The declared datum a title-page slot sets: the five parts `\maketitle` reads back. -/
public inductive TitleDatum where
  | title
  | subtitle
  | author
  | institute
  | date
  deriving Repr, BEq, DecidableEq, Inhabited

public def TitleDatum.name : TitleDatum → String
  | .title => "title"
  | .subtitle => "subtitle"
  | .author => "author"
  | .institute => "institute"
  | .date => "date"

public theorem TitleDatum.name_exact (datum : TitleDatum) :
    datum.name = (match datum with
      | .title => "title"
      | .subtitle => "subtitle"
      | .author => "author"
      | .institute => "institute"
      | .date => "date") := by
  cases datum <;> rfl

public def TitleDatum.ofName? : String → Option TitleDatum
  | "title" => some .title
  | "subtitle" => some .subtitle
  | "author" => some .author
  | "institute" => some .institute
  | "date" => some .date
  | _ => none

public theorem TitleDatum.ofName_name (d : TitleDatum) : TitleDatum.ofName? d.name = some d := by
  cases d <;> rfl

/-- A point of a box, by pgf's compass names. -/
public inductive BoxPoint where
  | center
  | north
  | south
  | east
  | west
  | northEast
  | northWest
  | southEast
  | southWest
  deriving Repr, BEq, DecidableEq, Inhabited

public def BoxPoint.ofName? : String → Option BoxPoint
  | "center" => some .center
  | "north" => some .north
  | "south" => some .south
  | "east" => some .east
  | "west" => some .west
  | "north east" => some .northEast
  | "north west" => some .northWest
  | "south east" => some .southEast
  | "south west" => some .southWest
  | _ => none

public def BoxPoint.name : BoxPoint → String
  | .center => "center"
  | .north => "north"
  | .south => "south"
  | .east => "east"
  | .west => "west"
  | .northEast => "north east"
  | .northWest => "north west"
  | .southEast => "south east"
  | .southWest => "south west"

public theorem BoxPoint.ofName_name (p : BoxPoint) : BoxPoint.ofName? p.name = some p := by
  cases p <;> rfl

/-- Where the point stands across its box: `(left, right)` shares of its width. -/
public def BoxPoint.hshares : BoxPoint → Nat × Nat
  | .west | .northWest | .southWest => (0, 1)
  | .center | .north | .south => (1, 1)
  | .east | .northEast | .southEast => (1, 0)

/-- Where the point stands down its box: `(above, below)` shares of its height. -/
public def BoxPoint.vshares : BoxPoint → Nat × Nat
  | .north | .northWest | .northEast => (0, 1)
  | .center | .west | .east => (1, 1)
  | .south | .southWest | .southEast => (1, 0)

public def shareOf (s : Nat × Nat) (e : Int) : Int :=
  if s.1 + s.2 = 0 then 0 else e * s.1 / (s.1 + s.2)

/-- A length's share `s.1 / (s.1 + s.2)`, rounded down. -/
public def shareLen (s : Nat × Nat) (e : Length) : Length := ⟨shareOf s e.units⟩

public theorem pagePoint_agree (p : BoxPoint) (e : Int) :
    shareOf p.hshares e = shareOf p.hshares 100000 * e / 100000 ∧
    shareOf p.vshares e = shareOf p.vshares 100000 * e / 100000 := by
  cases p <;> simp [shareOf, BoxPoint.hshares, BoxPoint.vshares] <;> omega

/-- A title slot pinned to its page: which point of its box stands at which
point of the page, moved by the shifts. -/
public structure TitlePlace where
  anchor : BoxPoint
  pagePoint : BoxPoint
  xshift : Option SymGlue := none
  yshift : Option SymGlue := none
  innerSep : Option SymGlue := none
  deriving Repr, BEq, Inhabited

/-- pgf's own `inner sep`, `0.3333em`, at the em it is read in. -/
public def pgfInnerSep (em : Length) : Length := em * 3333 / 10000

/-- pgf's initial `outer sep`: half the initial 0.4 pt line width, an anchor
clearance, not padding. -/
public def pgfOuterSep : Length := Dim.pt 1 / 5

/-- One independently styled part of a title slot: `datum` selects document
metadata, else `content` is literal. -/
public structure TitlePart where
  datum : Option TitleDatum
  content : Array Inline := #[]
  font : Option (Array Inline) := none
  align : Option String := none
  size : Option SymGlue := none
  leading : Option SymGlue := none
  newLine : Bool := false
  before : Option SymGlue := none
  deriving Repr, BEq, Inhabited

/-- One box of a declared title page: its ordered, independently styled parts,
its measure, and where it stands. -/
public structure TitleSlot where
  parts : Array TitlePart := #[]
  width : Option SymGlue := none
  place : Option TitlePlace := none
  deriving Repr, BEq, Inhabited

/-- The one slot a source node owns. -/
public def TitleSlot.ofNodeParts (parts : Array TitlePart) (width : Option SymGlue)
    (place : Option TitlePlace) : TitleSlot :=
  { parts := parts, width := width, place := place }

public theorem TitleSlot.ofNodeParts_exact (parts : Array TitlePart) (width : Option SymGlue)
    (place : Option TitlePlace) :
    (TitleSlot.ofNodeParts parts width place).parts = parts := by
  rfl

/-- The box-owned projection both backends consume: width and placement. -/
public def TitleSlot.box (slot : TitleSlot) : Option SymGlue × Option TitlePlace :=
  (slot.width, slot.place)

public theorem TitleSlot.ofNodeParts_projects (parts : Array TitlePart) (width : Option SymGlue)
    (place : Option TitlePlace) :
    (TitleSlot.ofNodeParts parts width place).box = (width, place) := by
  rfl

/-- The role a title slot's block rides in, by the slot's index. -/
public def titleSlotRole (i : Nat) : String := s!"titlepage-slot-{i}"

/-- The role one styled part rides inside its slot. -/
public def titlePartRole (slot part : Nat) : String := s!"titlepage-slot-{slot}-part-{part}"

/-- The slot a role name shows, among a title page's declared slots. -/
public def titleSlotOf (slots : Array TitleSlot) (n : String) : Option TitleSlot :=
  (slots.zipIdx.find? fun (_, i) => titleSlotRole i == n).map (·.1)

/-- The part an inline role shows; a role that names no part stays an authored role. -/
public def titlePartOf (slots : Array TitleSlot) (n : String) : Option TitlePart :=
  slots.zipIdx.findSome? fun (slot, i) =>
    slot.parts.zipIdx.findSome? fun (part, k) =>
      if titlePartRole i k == n then some part else none

/-- A skip a block template stands in vertical mode: a skip register read
where the block stands, or a written glue. -/
public inductive BlockSkip where
  | register (name : String)
  | glue (g : SymGlue)
  deriving Repr, BEq, Inhabited

/-- One skip, in force where the block stands. -/
public def BlockSkip.resolve (tokens : Tokens) : BlockSkip → SymGlue
  | .register n => skipAmount tokens n
  | .glue g => g

/-- A run of skips, added as TeX's list adds them. -/
public def blockSkipSum (tokens : Tokens) (skips : Array BlockSkip) : SymGlue :=
  skips.foldl (fun acc s => acc.add (s.resolve tokens)) {}

/-- The box a template's rule stands beside: the title's own box, or the box
holding title and body. -/
public inductive BlockSpan where
  | title
  | whole
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A length a template's rule reads in its title's font: thousandths of its
`\baselineskip` and cap height, plus a fixed length. -/
public structure BlockMetric where
  lead : Int := 0
  cap : Int := 0
  fixed : Length := 0
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A metric at the title's `\baselineskip` and cap height. -/
public def BlockMetric.resolve (m : BlockMetric) (lead cap : Length) : Length :=
  m.lead * lead / (1000 : Int) + m.cap * cap / (1000 : Int) + m.fixed

public def BlockMetric.neg (m : BlockMetric) : BlockMetric :=
  { lead := -m.lead, cap := -m.cap, fixed := -m.fixed }

/-- Half the leading the capitals leave, `(\baselineskip-\fontcharht\font`H)/2`. -/
public def BlockMetric.halfLeading : BlockMetric := { lead := 500, cap := -500 }

public theorem BlockMetric.halfLeading_centred_exact (lead cap : Length) :
    BlockMetric.halfLeading.resolve lead cap - BlockMetric.halfLeading.neg.resolve lead cap =
      lead - cap := by
  simp only [BlockMetric.resolve, BlockMetric.halfLeading, BlockMetric.neg]
  length_omega

/-- How far a template's rule reaches beside its box: `box`, the box's own
height and depth; `lines`, by the title's lines. -/
public inductive BlockReach where
  | box
  | lines (height depth : BlockMetric)
  deriving Repr, BEq, Inhabited

/-- Where a web page stands a rule reaching by a block title's lines beside
the header that sets the title. -/
public structure BlockTitlePlace where
  top : Length
  bottom : Length
  rise : Length
  riseMany : Length
  room : Length
  depth : Length
  bodyBelow : Length
  deriving Repr, BEq, Inhabited

/-- A rule beside one of a block's boxes, as themes spell it: `width` wide,
`sep` from the box's `side`, reaching as `reach` says. -/
public structure BlockEdge where
  span : BlockSpan
  side : FlushSide
  width : SymGlue
  sep : SymGlue
  hang : Bool
  color : Color
  name : Option ColorRef := none
  reach : BlockReach := .box
  deriving Repr, BEq, Inhabited

/-- A template rule's colour against the palette in force: the entry the rule
names, else its declared colour. -/
public def BlockEdge.ink (e : BlockEdge) (pal : Palette) : Color :=
  (e.name.bind pal.lookup).getD e.color

/-- Whether the rule stands beside the title's box, alone or as the title's
part of a rule beside the whole block. -/
public def BlockEdge.besideTitle (e : BlockEdge) : Bool :=
  e.span == .title || (e.span == .whole && e.reach matches .lines ..)

/-- The title as a block template sets it: `boxed` in a box of its own,
`\hsize` wide, else a paragraph of the list it stands in. -/
public structure BlockTitleBox where
  boxed : Bool := false
  strut : Bool := false
  parskip : Bool := false
  deriving Repr, BEq, Inhabited

/-- The arm an untitled block takes where its template tests the title and
sets none: the skips it stands above the body. -/
public structure BlockBare where
  before : Array BlockSkip := #[]
  between : Array BlockSkip := #[]
  deriving Repr, BEq, Inhabited

/-- A block template, read: `bare` is how an untitled block stands, `whole`
the box holding title and body when the template sets one. -/
public structure BlockShape where
  before : Array BlockSkip := #[]
  title : BlockTitleBox := {}
  bare : Option BlockBare := none
  between : Array BlockSkip := #[]
  after : Array BlockSkip := #[]
  whole : Option Bool := none
  edges : Array BlockEdge := #[]
  deriving Repr, BEq, Inhabited

/-- Whether a block in this template sets its title's box: a titled block
always, an untitled one where the template keeps the box. -/
public def BlockShape.showsTitle (s : BlockShape) (titled : Bool) : Bool :=
  titled || s.bare.isNone

/-- The skips a block stands above its title, and between title and body, in the arm it takes. -/
public def BlockShape.skipsAbove (s : BlockShape) (titled : Bool) : Array BlockSkip :=
  match s.bare, titled with
  | some b, false => b.before
  | _, _ => s.before

public def BlockShape.skipsBetween (s : BlockShape) (titled : Bool) : Array BlockSkip :=
  match s.bare, titled with
  | some b, false => b.between
  | _, _ => s.between

/-- How far a span's box stands in from the measure on one side: `width + sep`
of each rule inside its line there. -/
public def BlockShape.inset (s : BlockShape) (span : BlockSpan) (side : FlushSide) : SymGlue :=
  s.edges.foldl (fun acc e =>
    if e.span == span && e.side == side && !e.hang then (acc.add e.width).add e.sep else acc) {}

/-- How a URL sets its `~`: as its face's glyph, or as url.sty's `lowtilde` draws it, a script-size
math `\sim` raised 0.2ex. -/
public inductive UrlTilde where
  | glyph
  | low
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One piece of an item label's template: text, or the item's number in a numeral style
(enumitem's `\arabic*`, `\alph*`, `\Alph*`, `\roman*` and `\Roman*`). -/
public inductive LabelPart where
  | lit (body : Array Inline)
  | count (style : NumStyle)
  deriving Repr, BEq, Inhabited

/-- How an element kind looks, from `\style{element}{...}`. -/
public structure ElementStyle where
  font : Option (Array Inline) := none
  before : Option SymGlue := none
  after : Option SymGlue := none
  /-- A rule filling the rest of the heading's line, in this palette colour. -/
  rule : Option (Color × Option ColorRef) := none
  /-- Where `rule` stands against the baseline; undeclared, `xHeight`. -/
  rulePosition : Option RulePosition := none
  /-- `rule`'s thickness; undeclared, the engine's em-relative weight in print
  and one device pixel on screen. -/
  ruleThickness : Option SymGlue := none
  /-- List marker content, replacing the level's class-default marker. -/
  marker : Option (Array Inline) := none
  indent : Option SymGlue := none
  /-- Space between list items. -/
  gap : Option SymGlue := none
  /-- Horizontal alignment of the element's lines; undeclared, a title page centres. -/
  align : Option HAlign := none
  /-- A full-measure rule after the element's leading part, in this palette colour. -/
  separator : Option (Color × Option ColorRef) := none
  /-- A full-measure rule above the element, this thick, in the ink colour. -/
  ruleAbove : Option SymGlue := none
  /-- Declared space above `ruleAbove`; undeclared, `titleBarSkip`. -/
  ruleAboveSkip : Option SymGlue := none
  /-- Declared space between `ruleAbove` and the element's first line;
  undeclared, `titleBarGap`. -/
  ruleAboveGap : Option SymGlue := none
  /-- A full-measure rule below the element, this thick. -/
  ruleBelow : Option SymGlue := none
  /-- Declared space between the element's last line and `ruleBelow`;
  undeclared, `titleBarGap`. -/
  ruleBelowGap : Option SymGlue := none
  /-- Declared space below `ruleBelow`, before what follows; undeclared, `titleBarSkip`. -/
  ruleBelowSkip : Option SymGlue := none
  /-- The author line's font template, read at the title block
  (`\style{titlepage}{ author-font = ... }`). -/
  authorFont : Option (Array Inline) := none
  /-- The author line's minimum height above its baseline. -/
  authorStrut : Option SymGlue := none
  /-- The size step the element's body sets at, read by the abstract only. -/
  bodySize : Option String := none
  /-- Interaction states, read by the HTML backend only: `hover` and `focus`
  colour the element's links, `motion` is the transition's duration in
  milliseconds. -/
  hover : Option (Color × Option ColorRef) := none
  focus : Option (Color × Option ColorRef) := none
  motion : Option Nat := none
  /-- The ink a link kind's text is set in (`link`, `url`, `cite`): hyperref's
  `linkcolor`, `urlcolor` and `citecolor` under `colorlinks`. -/
  color : Option (Color × Option ColorRef) := none
  /-- The title page's declared slots; empty is the built-in title page. -/
  slots : Array TitleSlot := #[]
  /-- A beamer block kind's template, read by the three block elements only;
  `none` is the default inner theme's colour boxes. -/
  shape : Option BlockShape := none
  /-- The spacing the lists of the element's scope declare, read where each opens (`listSetScopes`). -/
  list : ListSet := {}
  /-- How the `url` element sets a URL's `~`. -/
  tilde : Option UrlTilde := none
  /-- A list's label template, each item's label its number set in it, read where the list's
  items elaborate. -/
  label : Option (Array LabelPart) := none
  deriving Repr, BEq, Inhabited

/-- The part of the `titlepage` style the title heading itself takes: every
key but those that place a heading's line. -/
public def titleHeadingStyle (st : ElementStyle) : ElementStyle :=
  { st with rule := none, rulePosition := none, ruleThickness := none, indent := none,
            marker := none, gap := none, bodySize := none }

/-- beamer's three blocks, which a `\style` styles by their kind. -/
public def blockStyleElements : List String := ["block", "alertblock", "exampleblock"]

/-- The headings and lists a document may style, each beside its plural as the document sets it. -/
private def styleableFlow : List (String × String) :=
  [("section", "section headings"), ("subsection", "subsection headings"),
   ("subsubsection", "subsubsection headings"), ("heading1", "first-level headings"),
   ("heading5", "fifth-level headings"), ("heading6", "sixth-level headings"),
   ("abstract", "abstracts"), ("itemize", "itemize lists"), ("enumerate", "enumerate lists"),
   ("itemize2", "second-level itemize lists"), ("itemize3", "third-level itemize lists"),
   ("itemize4", "fourth-level itemize lists"), ("enumerate2", "second-level enumerate lists"),
   ("enumerate3", "third-level enumerate lists"), ("enumerate4", "fourth-level enumerate lists")]

/-- The deck furniture, links and blocks a document may style, each beside its plural. -/
private def styleableFurniture : List (String × String) :=
  [("frametitle", "frame titles"), ("sectionpage", "section pages"),
   ("standout", "standout frames"), ("titlepage", "title blocks"),
   ("nav", "navigation landmarks"), ("logo", "logos"), ("link", "links within the document"),
   ("url", "links to addresses"), ("cite", "citations"), ("block", "blocks"),
   ("alertblock", "alert blocks"), ("exampleblock", "example blocks")]

/-- Elements a document may style, each beside its plural; a `\define`d name is styleable too. -/
public def styleableNouns : List (String × String) := styleableFlow ++ styleableFurniture

/-- The list kinds a spacing scope names, as enumitem names them. -/
public def listSetKinds : List String := ["itemize", "enumerate", "description"]

/-- The element a list spacing scope declares through: every list or a kind, at every level or
one, enumitem's `list`, `list⟨n⟩`, a kind and a kind at its own depth. -/
public def listSetElement : Option String × Option Nat → String
  | (none, none) => "list"
  | (none, some l) => s!"list{l}"
  | (some k, none) => k
  | (some k, some l) => s!"{k}{l}"

/-- Every element a list spacing scope declares through, at the four levels lists nest. -/
public def listSetElements : List String :=
  ([none] ++ listSetKinds.map some).flatMap fun k =>
    ([none] ++ [1, 2, 3, 4].map some).map fun l => listSetElement (k, l)

/-- Every element whose style a list's spacing reads, from the widest scope to the narrowest. -/
public def listSetScopes (kind : String) (depth kindDepth : Nat) : List String :=
  [(none, none), (none, some depth), (some kind, none), (some kind, some kindDepth)].map
    listSetElement

/-- The elements the document styles directly. -/
private def drawnElements : List String := styleableNouns.map (·.1)

/-- The elements that declare only a list's spacing. -/
public def listSetOnly : List String := listSetElements.filter (!drawnElements.contains ·)

/-- Elements a document may style; a `\define`d name is styleable too. -/
public def styleableElements : List String := drawnElements ++ listSetOnly

/-- The keys a `\style` declaration takes. -/
public def styleKeys : List String :=
  ["font", "before", "after", "rule", "rule-position", "rule-thickness", "marker", "indent", "gap",
   "align", "separator", "rule-above", "rule-above-skip", "rule-above-gap",
   "rule-below", "rule-below-gap", "rule-below-skip", "author-font",
   "author-strut", "body-size", "hover", "focus", "motion", "slot", "color", "tilde", "label",
   "leftmargin"] ++ listSetKeys

/-- The keys a heading, a list and the navigation landmark read: their spacing, rule, marker,
indent and gap, and the web page's interaction states. -/
private def flowStyleKeys : List String :=
  ["before", "after", "rule", "rule-position", "rule-thickness", "marker", "indent", "gap", "hover",
   "focus", "motion"]

/-- The `\style` keys an element's sites read, a `\define`d name a heading's. -/
public def styleKeysRead : String → List String
  | "section" | "subsection" | "subsubsection" => "font" :: flowStyleKeys
  | "heading1" | "heading5" | "heading6" | "nav" => flowStyleKeys
  | "abstract" => ["font", "align", "body-size"]
  | "titlepage" => ["font", "before", "after", "separator", "rule-above", "rule-above-skip",
      "rule-above-gap", "rule-below", "rule-below-gap", "rule-below-skip", "author-font",
      "author-strut", "hover", "focus", "motion", "slot", "align"]
  | "link" | "cite" => ["color"]
  | "url" => ["color", "tilde"]
  | "logo" => ["align"]
  | "frametitle" | "sectionpage" | "standout" | "block" | "alertblock" | "exampleblock" => ["font"]
  | e =>
    if drawnElements.contains e && listSetElements.contains e then
      flowStyleKeys ++ listSetKeys ++ ["label", "leftmargin"]
    else if listSetOnly.contains e then listSetKeys ++ ["leftmargin"]
    else flowStyleKeys

public structure Styles where
  entries : Array (String × ElementStyle) := #[]
  deriving Repr, BEq, Inhabited

public def Styles.find? (s : Styles) (element : String) : Option ElementStyle :=
  (s.entries.find? (·.1 == element)).map (·.2)

/-- The `\style` element a titled block reads: its environment's own name;
tcolorbox's box reads none. -/
public def TitledKind.styleElement : TitledKind → Option String
  | .block => some "block"
  | .alert => some "alertblock"
  | .example => some "exampleblock"
  | .box => none

/-- The template a titled block stands in: its kind's declared shape; `none`
is the default inner theme's pair. -/
public def blockShapeOf (styles : Styles) (kind : TitledKind) : Option BlockShape :=
  kind.styleElement.bind fun el => (styles.find? el).bind (·.shape)

/-- The `\topsep` beamer's squeeze leaves in force (beamerbaseframesize.sty:22), rigid. -/
public def squeezedTopsep : SymGlue := { width := { fixed := Dim.pt 1 / 2 } }

/-- Where a frame's squeezed list spacing comes from. -/
public inductive FrameSqueeze where
  | none
  | declared
  | fitted
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Whether a block is one of a frame's marks: an empty engine role opening the frame's body. -/
@[expose] public def Block.isFrameMark : Block → Bool
  | .role n inner => inner.isEmpty &&
      (n == squeezeRole || n == squeezeFitRole || fitMarkRole n || n == unnumberedRole ||
        n == plainRole)
  | _ => false

/-- The marks a frame's body opens with, in order. -/
public def frameMarks (body : Array Block) : List String :=
  (body.toList.takeWhile Block.isFrameMark).filterMap fun b => match b with
    | .role n _ => some n
    | _ => none

public def frameSqueeze (body : Array Block) : FrameSqueeze :=
  if (frameMarks body).contains squeezeRole then .declared
  else if (frameMarks body).contains squeezeFitRole then .fitted
  else .none

/-- Mark a frame with the frame mark `role` opening its body; a frame already
marked so keeps its one mark. -/
-- conserves: none — splices one empty mark.
public def Block.markFrame (role : String) (b : Block) : Block :=
  match b with
  | .frame title standout valign breakable fbody =>
    if (frameMarks fbody).contains role then b
    else .frame title standout valign breakable
      (fbody.insertIdx 0 (Block.role role #[]) (Nat.zero_le _))
  | .para _ | .section .. | .list .. | .center _ | .ragged .. | .spaced .. | .role ..
  | .link .. | .quote _ _ | .lines _ | .abstract _ | .titled .. | .disclosure .. | .equation .. | .verbatim ..
  | .algorithm .. | .columns _ | .onSteps .. | .altSteps .. | .note _ | .only ..
  | .nav .. | .logo _ | .pagebreak | .framefoot _ | .setPalette _ | .setTokens _
  | .rule .. | .picture _ | .table .. | .float .. | .bibliography .. | .contents .. => b

/-- Mark the top-level frames at `indices` with the frame mark `role`. -/
-- conserves: none — splices empty marks.
public def markFrames (body : Array Block) (indices : Array Nat) (role : String) :
    Array Block :=
  body.mapIdx fun i b => if indices.contains i then b.markFrame role else b

public theorem markFrames_id (body : Array Block) (role : String) :
    markFrames body #[] role = body := by
  unfold markFrames
  apply Array.ext
  · simp
  · intro i h1 h2
    simp

/-- Mark each top-level frame `i` of `marks` with its role. -/
public def markFramesAt (body : Array Block) (marks : Array (Nat × String)) : Array Block :=
  marks.foldl (fun body (i, role) => markFrames body #[i] role) body

public theorem markFramesAt_id (body : Array Block) : markFramesAt body #[] = body := by
  simp [markFramesAt]

/-- The web deck's squeeze of the frames the page could not set at their glue's natural size. -/
public def squeezeFrames (body : Array Block) (indices : Array Nat) : Array Block :=
  markFrames body indices squeezeFitRole

public theorem squeezeFrames_id (body : Array Block) : squeezeFrames body #[] = body :=
  markFrames_id body squeezeFitRole

/-- How a frame not declared breakable stands on its page, the overflow ladder at least cost. -/
public inductive FrameFit where
  | natural
  | shrunk
  | overfull (over : Length)
  | continued (over : Length)
  deriving Repr, DecidableEq, Inhabited

/-- Whether the ladder moved a frame step: stood it overfull or continued it. -/
@[expose] public def FrameFit.moved : FrameFit → Bool
  | .overfull _ | .continued _ => true
  | .natural | .shrunk => false

/-- Whether the ladder continued a frame step on the next page. -/
@[expose] public def FrameFit.continues : FrameFit → Bool
  | .continued _ => true
  | .natural | .shrunk | .overfull _ => false

/-- The overflow ladder's decision for one step, from how far its content
stood past its text area at its glue's natural size. -/
public def frameFit (needed beyond clearance : Length) : FrameFit :=
  if 0 < beyond then
    if beyond ≤ clearance then .overfull beyond else .continued beyond
  else if 0 < needed then .shrunk
  else .natural

public theorem frameFit_id (needed beyond clearance : Length) (h : needed ≤ 0)
    (hb : beyond ≤ 0) : frameFit needed beyond clearance = .natural := by
  have h1 : ¬ (0 : Length) < beyond := Length.not_lt.mpr hb
  have h2 : ¬ (0 : Length) < needed := Length.not_lt.mpr h
  simp only [frameFit, h1, h2, ite_false]

public theorem frameFit_between (needed beyond clearance o : Length)
    (h : frameFit needed beyond clearance = .overfull o) : 0 < o ∧ o ≤ clearance := by
  unfold frameFit at h
  by_cases h0 : 0 < beyond
  · by_cases h1 : beyond ≤ clearance
    · simp only [h0, h1, ite_true, FrameFit.overfull.injEq] at h
      subst h
      exact ⟨h0, h1⟩
    · simp [h0, h1] at h
  · by_cases h2 : 0 < needed
    · simp [h0, h2] at h
    · simp [h0, h2] at h

/-- Where a block's own blocks stand against the vertical list the block stands on. -/
public inductive ListScope where
  | onList
  | box
  | aside
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A block's `ListScope` under a class's list lineage and the document's
declared styles. -/
@[expose] public def Block.listScope (l : ListLineage) (styles : Styles) : Block → ListScope
  | .quote _ _ | .abstract _ => if l == .beamer then .box else .onList
  | .float .. => if l == .beamer then .onList else .box
  | .titled kind .. => if (blockShapeOf styles kind).isSome then .onList else .box
  | .disclosure .. => .onList
  | .columns _ => .box
  | .note _ => .aside
  | .para _ | .lines _ | .section .. | .list .. | .center _ | .ragged .. | .spaced .. | .role ..
  | .link .. | .equation .. | .verbatim .. | .algorithm .. | .onSteps .. | .altSteps ..
  | .only .. | .nav .. | .logo _ | .pagebreak | .frame .. | .framefoot _ | .setPalette _
  | .setTokens _ | .rule .. | .picture _ | .table .. | .bibliography .. | .contents .. => .onList

/-- A list whose every item runs in by its label: a description list. -/
public def listIsDesc (ordered : Bool) (items : Array (Array Block)) : Bool :=
  !ordered && !items.isEmpty && items.all fun it => match it[0]? with
    | some (Block.para c) => (descLabel? c).isSome
    | _ => false

mutual

/-- The run of `\vfill`s a list item ends on, read through overlay steps and
backend shares; `n` is the run so far. -/
-- conserves: none — the length of one leaf run.
public def trailingFillsOne (n : Nat) : Block → Nat
  | .spaced g body => if g.value.fil && body.isEmpty then n + 1 else 0
  | .onSteps _ body => trailingFillsList 0 body.toList
  | .only _ body => trailingFillsList 0 body.toList
  | .para _ | .section .. | .list .. | .center _ | .ragged .. | .role .. | .link ..
  | .quote _ _ | .lines _ | .abstract _ | .titled .. | .disclosure .. | .equation .. | .verbatim .. | .algorithm ..
  | .columns _ | .altSteps .. | .note _ | .nav .. | .logo _ | .pagebreak | .frame ..
  | .framefoot _ | .setPalette _ | .setTokens _ | .rule .. | .picture _ | .table ..
  | .float .. | .bibliography .. | .contents .. => 0

public def trailingFillsList (n : Nat) : List Block → Nat
  | [] => n
  | b :: rest => trailingFillsList (trailingFillsOne n b) rest

end

/-- The fills a list item ends on (`trailingFillsOne`). -/
public def itemTrailingFills (item : Array Block) : Nat := trailingFillsList 0 item.toList

/-- Which reading of a frame a fill census takes: one step's page, every step
at once, or the web deck's one stage. -/
public inductive FillView where
  | page (step : Nat)
  | every
  | deck
  deriving Repr, BEq, Inhabited

mutual

/-- The `\vfill`s on a frame's own vertical list under one reading;
hand-rolled, not a `foldBlocks` leaf, because it stops at boxes and asides. -/
-- conserves: none — a count of one leaf kind.
public def frameFillsOne (l : ListLineage) (styles : Styles) (v : FillView) (acc : Nat) :
    Block → Nat
  | .spaced g inner => frameFillsList l styles v (if g.value.fil then acc + 1 else acc) inner.toList
  | .list ordered _ items =>
    match v with
    | .deck =>
      if listIsDesc ordered items then frameFillsItems l styles v acc items.toList
      else items.foldl (fun n item => n + itemTrailingFills item) acc
    | .page _ | .every => frameFillsItems l styles v acc items.toList
  | .center body => frameFillsList l styles v acc body.toList
  | .ragged _ body => frameFillsList l styles v acc body.toList
  | .role _ body => frameFillsList l styles v acc body.toList
  | .link _ body => frameFillsList l styles v acc body.toList
  | .onSteps _ body => frameFillsList l styles v acc body.toList
  | .altSteps spec first other =>
    match v with
    | .page k =>
      if spec.showsFirst k then frameFillsList l styles v acc first.toList
      else frameFillsList l styles v acc other.toList
    | .every => frameFillsList l styles v (frameFillsList l styles v acc first.toList) other.toList
    | .deck => acc
  | .only _ body => frameFillsList l styles v acc body.toList
  | .nav spec body => if spec.pin.isSome then acc else frameFillsList l styles v acc body.toList
  | .quote q body =>
    if (Block.quote q body).listScope l styles == .onList then frameFillsList l styles v acc body.toList
    else acc
  | .abstract body =>
    if (Block.abstract body).listScope l styles == .onList then
      frameFillsList l styles v acc body.toList
    else acc
  | .float kind num capAbove body caption =>
    if (Block.float kind num capAbove body caption).listScope l styles == .onList then
      frameFillsList l styles v acc body.toList
    else acc
  | .titled kind title body =>
    if (Block.titled kind title body).listScope l styles == .onList then
      frameFillsList l styles v acc body.toList
    else acc
  | .disclosure summary expanded body =>
    if (Block.disclosure summary expanded body).listScope l styles == .onList then
      frameFillsList l styles v acc body.toList
    else acc
  | .contents spec entries => acc + contentsFills spec entries
  | .para _ | .lines _ | .section .. | .equation .. | .verbatim .. | .algorithm .. | .columns _
  | .note _ | .logo _ | .pagebreak | .frame .. | .framefoot _ | .setPalette _ | .setTokens _
  | .rule .. | .picture _ | .table .. | .bibliography .. =>
    acc

public def frameFillsList (l : ListLineage) (styles : Styles) (v : FillView) (acc : Nat) :
    List Block → Nat
  | [] => acc
  | b :: rest => frameFillsList l styles v (frameFillsOne l styles v acc b) rest

public def frameFillsItems (l : ListLineage) (styles : Styles) (v : FillView) (acc : Nat) :
    List (Array Block) → Nat
  | [] => acc
  | item :: rest => frameFillsItems l styles v (frameFillsList l styles v acc item.toList) rest

end

/-- The `\vfill`s on a frame body's own vertical list under one reading
(`frameFillsOne`). -/
public def frameFills (l : ListLineage) (styles : Styles) (v : FillView) (body : Array Block) :
    Nat :=
  frameFillsList l styles v 0 body.toList

/-- beamer's four font axes, in the order `\beamer@usebeamerfont` selects
them (beamerbasefont.sty): size, shape, series, family. -/
public inductive FontAxis where
  | size
  | shape
  | series
  | family
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The axes in the order beamer selects them. -/
@[expose] public def FontAxis.all : List FontAxis := [.size, .shape, .series, .family]

public theorem FontAxis.all_complete (a : FontAxis) : a ∈ FontAxis.all := by
  cases a <;> simp [FontAxis.all]

public theorem FontAxis.all_nodup : FontAxis.all.Nodup := by decide

/-- The axis's key in a beamer font declaration. -/
@[expose] public def FontAxis.key : FontAxis → String
  | .size => "size"
  | .shape => "shape"
  | .series => "series"
  | .family => "family"

/-- The axis a style selects on; `none` for a style that selects on no one axis. -/
public def Style.fontAxis : Style → Option FontAxis
  | .size _ | .fontSize _ _ => some .size
  | .italic | .smallcaps | .upright => some .shape
  | .bold | .medium | .series _ => some .series
  | .sans | .roman | .mono | .family _ => some .family
  | .emph | .normal | .lang _ => none

/-- A font template's selection on each axis, as a beamer font element carries one per axis. -/
public structure FontAxes where
  size : Option Style := none
  shape : Option Style := none
  series : Option Style := none
  family : Option Style := none
  deriving Repr, BEq, Inhabited

public def FontAxes.get (a : FontAxes) : FontAxis → Option Style
  | .size => a.size
  | .shape => a.shape
  | .series => a.series
  | .family => a.family

/-- Select `s` on its axis, replacing what the axis held. -/
public def FontAxes.select (a : FontAxes) (s : Style) : FontAxes :=
  match s.fontAxis with
  | some .size => { a with size := some s }
  | some .shape => { a with shape := some s }
  | some .series => { a with series := some s }
  | some .family => { a with family := some s }
  | none => a

/-- `own`'s selection on every axis it makes one, `parent`'s elsewhere. -/
public def FontAxes.over (own parent : FontAxes) : FontAxes :=
  { size := own.size.or parent.size, shape := own.shape.or parent.shape
    series := own.series.or parent.series, family := own.family.or parent.family }

/-- The selections as a font template, size outermost, then shape, series and
family around the empty hole. -/
public def FontAxes.template (a : FontAxes) : Array Inline :=
  let wrap (s : Option Style) (body : Array Inline) : Array Inline :=
    match s with
    | some st => #[.styled st body]
    | none => body
  wrap a.size (wrap a.shape (wrap a.series (wrap a.family #[])))

mutual

-- conserves: none — reads template wrappers.
private def axesOne (acc : FontAxes) : Inline → Option FontAxes
  | .styled st body => if st.fontAxis.isSome then axesList (acc.select st) body.toList else none
  | _ => none

-- conserves: none — list companion of `axesOne`.
private def axesList (acc : FontAxes) : List Inline → Option FontAxes
  | [] => some acc
  | [x] => axesOne acc x
  | _ => none

end

/-- A font template's selections, read; `none` for a template holding anything
but nested axis wrappers around the empty hole. -/
public def fontAxesOf (tpl : Array Inline) : Option FontAxes := axesList {} tpl.toList

/-- Every selection stands on its own axis. -/
public def FontAxes.Sorted (a : FontAxes) : Prop :=
  ∀ ax s, a.get ax = some s → s.fontAxis = some ax

private theorem FontAxes.select_sorted (a : FontAxes) (s : Style) (h : a.Sorted) :
    (a.select s).Sorted := by
  intro ax t ht
  unfold FontAxes.select at ht
  cases hs : s.fontAxis with
  | none => rw [hs] at ht; exact h ax t ht
  | some sax =>
    rw [hs] at ht
    cases sax <;> cases ax <;> simp only [FontAxes.get] at ht <;>
      first
      | (simp only [Option.some.injEq] at ht; subst ht; exact hs)
      | exact h _ t ht

private theorem axesOne_sorted (x : Inline) :
    ∀ (acc out : FontAxes), acc.Sorted → axesOne acc x = some out → out.Sorted := by
  induction x using Inline.rec
    (motive_2 := fun body => ∀ acc out, FontAxes.Sorted acc →
      axesList acc body.toList = some out → out.Sorted)
    (motive_3 := fun xs => ∀ acc out, FontAxes.Sorted acc → axesList acc xs = some out →
      out.Sorted) with
  | styled st body ih =>
    intro acc out hacc h
    simp only [axesOne] at h
    split at h
    · exact ih _ _ (FontAxes.select_sorted acc st hacc) h
    · simp at h
  | mk _ ih =>
    rename_i acc out hacc h
    exact ih acc out hacc h
  | nil =>
    rename_i acc out hacc h
    simp only [axesList, Option.some.injEq] at h
    subst h
    exact hacc
  | cons x xs ihx ihxs =>
    rename_i acc out hacc h
    cases xs with
    | nil => simp only [axesList] at h; exact ihx acc out hacc h
    | cons y ys => simp [axesList] at h
  | _ => intro acc out _ h; simp [axesOne] at h

private theorem FontAxes.over_get (o p : FontAxes) (ax : FontAxis) :
    (o.over p).get ax = (o.get ax).or (p.get ax) := by
  cases ax <;> rfl

private theorem FontAxes.over_sorted (o p : FontAxes) (ho : o.Sorted) (hp : p.Sorted) :
    (o.over p).Sorted := by
  intro ax s h
  rw [FontAxes.over_get] at h
  cases hg : o.get ax with
  | none => rw [hg] at h; exact hp ax s h
  | some t =>
    rw [hg] at h
    simp only [Option.or, Option.some.injEq] at h
    subst h
    exact ho ax t hg

private theorem axesList_sorted (xs : List Inline) (acc out : FontAxes) (hacc : acc.Sorted)
    (h : axesList acc xs = some out) : out.Sorted := by
  match xs, h with
  | [], h =>
    simp only [axesList, Option.some.injEq] at h
    subst h
    exact hacc
  | [x], h =>
    simp only [axesList] at h
    exact axesOne_sorted x acc out hacc h
  | _ :: _ :: _, h => simp [axesList] at h

private theorem fontAxesOf_sorted (tpl : Array Inline) (a : FontAxes) (h : fontAxesOf tpl = some a) :
    a.Sorted :=
  axesList_sorted tpl.toList {} a (fun ax s h => by cases ax <;> simp [FontAxes.get] at h) h

public theorem FontAxes.template_exact (a : FontAxes) (h : a.Sorted) :
    fontAxesOf a.template = some a := by
  obtain ⟨sz, sh, se, fa⟩ := a
  have h1 : ∀ s, sz = some s → s.fontAxis = some .size := fun s hs => h .size s hs
  have h2 : ∀ s, sh = some s → s.fontAxis = some .shape := fun s hs => h .shape s hs
  have h3 : ∀ s, se = some s → s.fontAxis = some .series := fun s hs => h .series s hs
  have h4 : ∀ s, fa = some s → s.fontAxis = some .family := fun s hs => h .family s hs
  cases sz <;> cases sh <;> cases se <;> cases fa <;>
    simp_all [FontAxes.template, fontAxesOf, axesList, axesOne, FontAxes.select]

/-- A block title's font template: the plain block's own, or an alerted or
example title's axes over the plain block's; `none` keeps the built-in
bold. -/
public def blockTitleFont (styles : Styles) (kind : TitledKind) : Option (Array Inline) :=
  kind.styleElement.bind fun el =>
    let own := (styles.find? el).bind (·.font)
    if el == "block" then own else
    let parent := (styles.find? "block").bind (·.font)
    match own, parent with
    | none, p => p
    | some o, none => some o
    | some o, some p =>
      match fontAxesOf o, fontAxesOf p with
      | some oa, some pa => some (oa.over pa).template
      | _, _ => some o

public theorem blockTitleFont_axes_exact (styles : Styles) (kind : TitledKind) (el : String)
    (hel : kind.styleElement = some el) (hne : el ≠ "block") (o p : Array Inline)
    (oa pa : FontAxes) (ho : (styles.find? el).bind (·.font) = some o)
    (hp : (styles.find? "block").bind (·.font) = some p)
    (hoa : fontAxesOf o = some oa) (hpa : fontAxesOf p = some pa) (ax : FontAxis) :
    ((blockTitleFont styles kind).bind fontAxesOf).map (·.get ax) =
      some ((oa.get ax).or (pa.get ax)) := by
  have hs := FontAxes.over_sorted oa pa (fontAxesOf_sorted o oa hoa) (fontAxesOf_sorted p pa hpa)
  have hne' : (el == "block") = false := by simpa using hne
  simp only [blockTitleFont, hel, Option.bind_some, ho, hp, hne', hoa, hpa]
  simp [FontAxes.template_exact _ hs, FontAxes.over_get]

/-- A link's body in its kind's declared ink (`ElementStyle.color`), as
hyperref's `colorlinks` colours a link's text. -/
public def Styles.linkInk (s : Styles) (kind : String) (body : Array Inline) : Array Inline :=
  match (s.find? kind).bind (·.color) with
  | some (c, n) => #[.colored c n body]
  | none => body

/-- A later declaration of an element overrides its whole record, keeping one entry per element. -/
public def Styles.declare (s : Styles) (element : String) (st : ElementStyle) : Styles :=
  { entries := redeclare s.entries element st }

/-- The abstract heading's style: the section heading's, centred. -/
public def abstractHeadingStyle (styles : Styles) : ElementStyle :=
  let sec := (styles.find? "section").getD {}
  let own := (styles.find? "abstract").getD {}
  { own with
    font := own.font <|> sec.font
    align := own.align <|> some .center }

public theorem abstract_heading_follows_section (styles : Styles)
    (h : styles.find? "abstract" = none) :
    (abstractHeadingStyle styles).font =
      ((styles.find? "section").getD {}).font ∧
    (abstractHeadingStyle styles).align = some .center := by
  simp [abstractHeadingStyle, h]

/-- The abstract body's size step; undeclared, article.cls's `\small`. -/
public def abstractBodySize (styles : Styles) : String :=
  ((styles.find? "abstract").bind (·.bodySize)).getD "small"

/-- What a chrome footer slot shows, resolved per page: the current top-level
section's title, or the page's frame number. -/
public inductive ChromeSlot where
  | sectionTitle
  | frameNumber
  /-- The `n / N` form, beamer's `[totalframenumber]` template. -/
  | frameFraction
  /-- A slot declared empty, as a footline template leaves a side. -/
  | blank
  deriving Repr, BEq, Inhabited

public def ChromeSlot.label : ChromeSlot → String
  | .sectionTitle => "sectiontitle"
  | .frameNumber => "framenumber"
  | .frameFraction => "framefraction"
  | .blank => "none"

/-- The declared priority of a slot datum: which slot yields when two boxes collide. -/
public def ChromeSlot.priority : ChromeSlot → Nat
  | .frameNumber => 0
  | .frameFraction => 1
  | .sectionTitle => 2
  | .blank => 4

public theorem ChromeSlot.priority_injective : ∀ a b : ChromeSlot,
    a.priority = b.priority → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [priority]

/-- A `\framefoot` note's priority, above every furniture datum. -/
public def notePriority : Nat := 3

/-- Which side of a furniture band a slot occupies; a band holds at most one slot per side. -/
public inductive BandSide where
  | left
  | right
  deriving Repr, BEq, DecidableEq, Inhabited

public def BandSide.idx : BandSide → Nat
  | .left => 0
  | .right => 1

/-- One slot of a furniture band: the declared side, the resolved content and
the declared priority. -/
public structure BandSlot where
  side : BandSide
  content : Array Inline
  priority : Nat
  label : String
  deriving Repr, BEq, Inhabited

/-- The band's paint order: declared priority first, side as the tiebreak. -/
public def BandSlot.rank (s : BandSlot) : Nat := 2 * s.priority + s.side.idx

public theorem BandSlot.rank_ne_of_side_ne (a b : BandSlot) (h : a.side ≠ b.side) :
    a.rank ≠ b.rank := by
  cases ha : a.side <;> cases hb : b.side <;>
    simp_all [rank, BandSide.idx] <;> omega

/-- A footer slot as text: the one place a frame number is formatted. -/
public def ChromeSlot.render (s : ChromeSlot) (sectionTitle : Array Inline)
    (n total : Nat) : Array Inline :=
  match s with
  | .sectionTitle => sectionTitle
  | .frameNumber => #[.text (toString n)]
  | .frameFraction => #[.text s!"{n} / {total}"]
  | .blank => #[]

/-- Page furniture a theme or the document (`\chrome`) declares: the slide footer's two slots. -/
public structure Chrome where
  footerLeft : Option ChromeSlot := none
  footerRight : Option ChromeSlot := none
  /-- Restore an explicit note on a standout frame; `some false` disables it. -/
  standoutNote : Option Bool := none
  deriving Repr, BEq, Inhabited

public def Chrome.hasFooter (c : Chrome) : Bool :=
  c.footerLeft.isSome || c.footerRight.isSome

/-- The footline's slot pair: the left slot a `\framefoot` note in force, else
the declared left datum, and the right slot. -/
public def Chrome.footSlots (c : Chrome) (frameFoot : Option (Array Inline))
    (sectionTitle : Array Inline) (n total : Nat) :
    Array Inline × Array Inline :=
  let slot (s : ChromeSlot) : Array Inline := s.render sectionTitle n total
  let left := match frameFoot with
    | some xs => xs
    | none => (c.footerLeft.map slot).getD #[]
  (left, (c.footerRight.map slot).getD #[])

/-- One band slot when its content ships ink, none when it is empty. -/
public def bandSlotIf (side : BandSide) (content : Array Inline)
    (priority : Nat) (label : String) : Array BandSlot :=
  if content.isEmpty then #[] else #[{ side, content, priority, label }]

public theorem mem_bandSlotIf {s : BandSlot} {side : BandSide}
    {content : Array Inline} {priority : Nat} {label : String}
    (h : s ∈ bandSlotIf side content priority label) :
    s.side = side ∧ s.content = content := by
  unfold bandSlotIf at h
  split at h
  · simp at h
  · simp only [Array.mem_singleton] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- The footline as a band of slots, each with its declared side, its content
from `footSlots` and its priority. -/
public def Chrome.footBand (c : Chrome) (frameFoot : Option (Array Inline))
    (sectionTitle : Array Inline) (n total : Nat) : Array BandSlot :=
  let (left, right) := c.footSlots frameFoot sectionTitle n total
  let (lp, ll) := match frameFoot, c.footerLeft with
    | some _, _ => (notePriority, "the \\framefoot note")
    | none, some s => (s.priority, s.label)
    | none, none => (0, "")
  bandSlotIf .left left lp ll ++
    bandSlotIf .right right ((c.footerRight.map (·.priority)).getD 0)
      ((c.footerRight.map (·.label)).getD "")

public theorem Chrome.footBand_projects (c : Chrome) (ff : Option (Array Inline))
    (sec : Array Inline) (n total : Nat) {s : BandSlot}
    (h : s ∈ c.footBand ff sec n total) :
    (s.side = .left ∧ s.content = (c.footSlots ff sec n total).1) ∨
    (s.side = .right ∧ s.content = (c.footSlots ff sec n total).2) := by
  unfold footBand at h
  rw [Array.mem_append] at h
  rcases h with h | h
  · exact .inl (mem_bandSlotIf h)
  · exact .inr (mem_bandSlotIf h)

/-- The frame's band; a standout frame's carries only a restored explicit note. -/
public def Chrome.frameFootBand (c : Chrome) (ff : Option (Array Inline))
    (sec : Array Inline) (n : Option Nat) (total : Nat) (standout : Bool) :
    Option (Array BandSlot) :=
  if standout then
    if c.standoutNote.getD false && !(ff.getD #[]).isEmpty then
      some (bandSlotIf .left (ff.getD #[]) notePriority "the \\framefoot note")
    else none
  else
    n.bind fun k =>
      if c.hasFooter || ff.isSome then some (c.footBand ff sec k total) else none

public theorem Chrome.standoutFootBand_exact (c : Chrome) (ff : Option (Array Inline))
    (sec : Array Inline) (n : Option Nat) (total : Nat) :
    c.frameFootBand ff sec n total true =
      if c.standoutNote.getD false && !(ff.getD #[]).isEmpty then
        some (bandSlotIf .left (ff.getD #[]) notePriority "the \\framefoot note")
      else none := by
  simp [frameFootBand]

/-- A band's inline content in reading order, left to right. -/
public def bandInlines (b : Array BandSlot) : Array Inline :=
  (b.filter (·.side == .left) ++ b.filter (·.side == .right)).flatMap
    (·.content)

public theorem Chrome.footSlots_right_ignores_left (c c' : Chrome)
    (ff ff' : Option (Array Inline)) (sec : Array Inline) (n total : Nat)
    (h : c.footerRight = c'.footerRight) :
    (c.footSlots ff sec n total).2 = (c'.footSlots ff' sec n total).2 := by
  simp [footSlots, h]

public theorem Chrome.footSlots_left_ignores_right (c c' : Chrome)
    (ff : Option (Array Inline)) (sec : Array Inline) (n total : Nat)
    (h : c.footerLeft = c'.footerLeft) :
    (c.footSlots ff sec n total).1 = (c'.footSlots ff sec n total).1 := by
  simp [footSlots, h]

/-- Where the footline template stands on the page, and how much of the page
it takes from the frame. -/
public structure Footline where
  step : String
  left : Length
  right : Length
  raise : Length
  sep : Length
  deriving Repr

public def footline : Footline :=
  { step := "tiny"      -- beamerfontthemedefault.sty:67 and :19, footline: parent={tiny structure}, size=\tiny
    left := Dim.pt 4    -- beamerouterthememoloch.sty:115, leftskip=4pt
    right := Dim.pt 5   -- beamerouterthememoloch.sty:116, rightskip=5pt
    raise := Dim.pt 4   -- beamerouterthememoloch.sty:123, \vskip4pt
    sep := Dim.pt 4 }   -- beamerbaseframecomponents.sty:167, \advance\footheight by 4pt

/-- The footline's size: its step of `base` on the document's ladder, which both backends and the
contrast judge read. -/
@[expose] public def footlineSize (scale : List (String × Nat)) (base : Length) : Length :=
  scaleStepIn scale base footline.step

/-- A note mark's size: the default ladder's script step, near LaTeX's math script size, which a
declared `\scriptsize` does not move. -/
@[expose] public def noteMarkSize (base : Length) : Length := scaleStepIn sizeScale base "scriptsize"

mutual

/-- The walk of `fillTemplate`: any body-carrying wrapper may hold the template's hole. -/
private def fillOne (content : Array Inline) : Inline → Inline
  | .styled st body =>
    .styled st (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .colored c n body =>
    .colored c n (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .located span body =>
    .located span (fillList content body.toList).toArray
  | .role n body =>
    .role n (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .decorated kind body =>
    .decorated kind (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .boxed b body =>
    .boxed b (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .link u body =>
    .link u (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .onSteps spec body =>
    .onSteps spec (if body.isEmpty then content else (fillList content body.toList).toArray)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec
      (if firstPage.isEmpty then content else (fillList content firstPage.toList).toArray)
      (if otherPage.isEmpty then content else (fillList content otherPage.toList).toArray)
  | .text s => .text s
  | .math d src => .math d src
  | .formula d src body => .formula d src body
  | .image src size alt => .image src size alt
  | .icon s l => .icon s l
  | .label k => .label k
  | .ref k p t tg => .ref k p t tg
  | .fill => .fill
  | .hspace g keep => .hspace g keep
  | .rule w h r => .rule w h r
  | .strut h => .strut h
  | .italicCorr m => .italicCorr m
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak e => .linebreak e
  | .cite t ks => .cite t ks
  | .cited t ks ink => .cited t ks ink
  | .footnote n body => .footnote n body

private def fillList (content : Array Inline) : List Inline → List Inline
  | [] => []
  | x :: rest => fillOne content x :: fillList content rest

end

/-- Fill a font template's hole, its innermost empty body, with content; a
template with no hole is returned unchanged. -/
-- conserves: none — a splice of two trees.
public def fillTemplate (template content : Array Inline) : Array Inline :=
  if template.isEmpty then content else (fillList content template.toList).toArray

/-- The size a font template sets its content at: the outermost `.size`
wrapper's step of the base on the document's ladder, else the base. -/
public def templateSize (scale : List (String × Nat)) (base : Length) (tpl : Array Inline) : Length :=
  if let some (Inline.styled (Style.size s) _) := (tpl[0]? : Option Inline)
  then scaleStepIn scale base s else base

/-- The `\baselineskip` each named size sets under a class option, in
milli-points, from its size file's `\@setfontsize`. -/
private def sizeFileLeadings : Nat → List (String × Nat)
  | 8 => [("tiny", 6000), ("scriptsize", 6000), ("footnotesize", 7000), ("small", 8000),
      ("normalsize", 9500), ("large", 10950), ("Large", 12000), ("LARGE", 14000),
      ("huge", 18000), ("Huge", 22000)]
  | 9 => [("tiny", 6000), ("scriptsize", 7000), ("footnotesize", 8000), ("small", 9000),
      ("normalsize", 10950), ("large", 12000), ("Large", 13000), ("LARGE", 14000),
      ("huge", 18000), ("Huge", 22000)]
  | 10 => [("tiny", 6000), ("scriptsize", 8000), ("footnotesize", 9500), ("small", 11000),
      ("normalsize", 12000), ("large", 14000), ("Large", 18000), ("LARGE", 22000),
      ("huge", 25000), ("Huge", 30000)]
  | 11 => [("tiny", 7000), ("scriptsize", 9500), ("footnotesize", 11000), ("small", 12000),
      ("normalsize", 13600), ("large", 14000), ("Large", 18000), ("LARGE", 22000),
      ("huge", 25000), ("Huge", 30000)]
  | 12 => [("tiny", 7000), ("scriptsize", 9500), ("footnotesize", 12000), ("small", 13600),
      ("normalsize", 14500), ("large", 18000), ("Large", 22000), ("LARGE", 25000),
      ("huge", 30000), ("Huge", 30000)]
  | 14 => [("tiny", 7000), ("scriptsize", 9500), ("footnotesize", 12000), ("small", 14000),
      ("normalsize", 17000), ("large", 22000), ("Large", 25000), ("LARGE", 30000),
      ("huge", 35000), ("Huge", 40000)]
  | 17 => [("tiny", 9000), ("scriptsize", 11000), ("footnotesize", 14000), ("small", 17000),
      ("normalsize", 22000), ("large", 25000), ("Large", 30000), ("LARGE", 35000),
      ("huge", 41000), ("Huge", 52000)]
  | 20 => [("tiny", 11000), ("scriptsize", 14000), ("footnotesize", 17000), ("small", 22000),
      ("normalsize", 25000), ("large", 30000), ("Large", 35000), ("LARGE", 41000),
      ("huge", 52000), ("Huge", 63000)]
  | _ => []

/-- The `\baselineskip` a named size of the engine's ladder sets: the size file's where the
body is an option's size, else the engine's leading of the size. -/
public def sizeFileLeading (body : Length) (leading : Nat) (name : String) : Length :=
  match displayOptions.find? fun o => Dim.pt o.1 == body || o.2 == body with
  | some (opt, _) =>
    match (sizeFileLeadings opt).lookup name with
    | some milli => Dim.pt 1 * (milli : Int) / (1000 : Int) * (leading : Int) / (1000 : Int)
    | none => leadingFor (scaleStepIn sizeScale body name) leading
  | none => leadingFor (scaleStepIn sizeScale body name) leading

/-- A block title's `\baselineskip`, from the size its font template sets outermost. -/
public def blockTitleLeading (scale : List (String × Nat)) (body : Length) (leading : Nat)
    (env : MeasureValues) (font : Option (Array Inline)) : SymLength :=
  match (font.bind (·[0]?) : Option Inline) with
  | some (.styled (.size s) _) =>
    .ofLength (if scale == sizeScale then sizeFileLeading body leading s
      else leadingFor (scaleStepIn scale body s) leading)
  | some (.styled (.fontSize _ lead) _) => (lead.eval env.find).width.scale leading 1000
  | _ => .ofLength (leadingFor body leading)

public theorem frameTitlePadding_exact :
    frameTitlePadding.width.resolve (scaleStepIn sizeScale slidesFontSize "large") 0 =
      frameTitleStrut (scaleStepIn sizeScale slidesFontSize "large") := by
  decide

/-- The kernel's page models: how content maps onto the surfaces the paged backends draw. -/
public inductive PageModel where
  /-- Content flows into a sequence of pages (`article`'s model). -/
  | flow
  /-- A frame is a page boundary; overlays produce steps (`slides`). -/
  | frame
  /-- Fixed faces, no flow: trim sizes and a print safe zone (`card`). -/
  | face
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The page-count bound a class implies: a literal, or the document's own declared faces. -/
public inductive PagesBound where
  | lit (op : CmpOp) (n : Int)
  | faces
  deriving Repr, BEq

/-- How a class sets its abstract's body. -/
public inductive AbstractForm where
  /-- article.cls's: `quotation`'s margins on both sides, its lists a level deeper. -/
  | quotation
  /-- A title page's, report.cls's default: the full measure. -/
  | titlePage
  /-- beamer's template: `abstractInset` beside its paragraphs, ragged right, a list at its own
  margins as `\@trivlist` resets `\leftskip`. -/
  | inset
  deriving Repr, BEq, DecidableEq, Inhabited

/-- beamer's abstract `\leftskip2em` and `\rightskip2em`, in the preamble's font
(beamerinnerthemedefault.sty:325). -/
public def abstractInset : Dim.SymLength := { em := 2000 }

/-- ISO 216's A4, 210 × 297 mm, as LaTeX's classes set it. -/
public def a4Page : Length × Length := (Dim.mm 210, Dim.mm 297)

/-- Named page sizes as LaTeX's classes set them: ISO 216's A4 and A5, ISO B5, and US letter,
legal and executive. -/
public def pageSizes : List (String × (Length × Length)) :=
  [("letter", (Dim.bp 612, Dim.bp 792)),
   ("legal", (Dim.bp 612, Dim.bp 1008)),
   ("a4", a4Page),
   ("a5", (Dim.mm 148, Dim.mm 210)),
   ("b5", (Dim.mm 176, Dim.mm 250)),
   ("executive", (Dim.bp 522, Dim.bp 756))]

/-- A document class as a record over one of the kernel's page models:
defaults, furniture flags, implied assertions, build intent. -/
public structure ClassRecord where
  model : PageModel
  /-- The class's body-size default, when it declares one (`slides`: beamer's documented 11 pt). -/
  fontSize : Option Length := none
  /-- Whether the body's `\baselineskip` is its size file's `\normalsize` one, as LaTeX's standard
  classes and KOMA-Script's set it (size11.clo's 13.6pt), not the 6⁄5 rule. -/
  sizeFileSkip : Bool := false
  /-- The class's paragraph-separation default, when it declares one. -/
  parskip : Option Dim.SymGlue := none
  /-- Whether the class's `parskip` option sets the paragraph separation in lines of its
  `\baselineskip` (`classParskip?`). -/
  parskipOption : Bool := false
  /-- Where the class's list spacing comes from (`listSkips`). -/
  lists : ListLineage := .sizeFile
  /-- How the class's list levels read the `\parskip` in force (`ListExtra.over`). -/
  listExtra : ListExtra := .none
  /-- A quotation's `\listparindent`, its paragraphs' first-line indent (classes.dtx's 1.5 em). -/
  quotationIndent : Dim.SymLength := { em := 1500 }
  /-- Whether the preamble sets text in the sans family, as beamer's
  `\familydefault` is `\sfdefault`. -/
  preambleSans : Bool := false
  /-- Whether headings number by default; `\section*` opts out either way. -/
  numberHeadings : Bool := false
  /-- Whether the measure is judged against the readable band. -/
  measureBand : Bool := false
  /-- Whether running head, foot and logo are legal furniture. -/
  runningFurniture : Bool := true
  /-- Whether pages carry the physical page number, centred in the foot,
  unless the document declares otherwise. -/
  pageNumbers : Bool := false
  /-- Whether the chrome band and the slides furniture styles draw. -/
  chrome : Bool := false
  /-- Whether the class draws the `\title` family as a page-top headline band,
  without a `\maketitle`. -/
  headline : Bool := false
  /-- How far the class's tinted grounds stand from its page when a palette is
  generated from seeds, and its text's floor: a document's, a deck's stage or a poster's board. -/
  groundDepth : GroundDepth := .documents
  /-- What the class asks of the colours nothing declares. -/
  colorRow : ClassRow := .latex
  /-- The colour schemes the class's page offers where its document names none. -/
  schemes : ClassSchemes := .every
  /-- An implied page-count contract, checked against the shipped pages as a
  declared `\assert` is. -/
  pagesBound : Option PagesBound := none
  /-- Failure guidance for a `.lit` pages bound. -/
  pagesHelp : String := ""
  /-- `textInArea` implied, with its failure guidance. -/
  inkInArea : Option String := none
  /-- `minXHeight` implied: the floor and its failure guidance. -/
  xHeightFloor : Option (Length × String) := none
  /-- The page (width × height) the class sets where no option names one: a face's trade trim, a
  KOMA-Script page's A4. -/
  trimDefault : Option (Length × Length) := none
  /-- The face's print safe zone: the default margins, inside which a drifting trim cannot cut. -/
  safeMargin : Option Length := none
  /-- Build intent when the document's `\output` names no formats. -/
  formats : Array String := #[]
  /-- The markdown twin's default file name, when the class has one. -/
  mdName : Option String := none
  /-- How the class sets its abstract, before its title-page options. -/
  abstractForm : AbstractForm := .quotation
  /-- The web layout a flow's page takes where the document declares none: book-theme's, MyST's
  default site template. -/
  webLayout : WebLayout := .book
  /-- Where the class's text area comes from where the document declares none. -/
  area : AreaRule := .engine
  deriving Repr, BEq

/-- The document's class, closed: a class `ofString?` does not answer never enters the IR. -/
public inductive DocClass where
  | article
  | slides
  | card
  /-- An article with the résumé genre's contract implied: one page, ink
  inside the margins, nothing below the legibility floor. -/
  | resume
  /-- An article, HTML-primary, declaring its own build intent (html and md). -/
  | webpage
  /-- One fixed, printed, trimmed surface at a large base: the face model's second class. -/
  | poster
  /-- KOMA-Script's article, report and book classes, one record for the three. -/
  | koma
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The class's one spelling, the `\documentclass` argument. -/
public def DocClass.name : DocClass → String
  | .article => "article"
  | .slides => "slides"
  | .card => "card"
  | .resume => "resume"
  | .webpage => "webpage"
  | .poster => "poster"
  | .koma => "scrartcl"

/-- The class a `\documentclass` argument names, if any: the inverse of `name`, KOMA-Script's
report and book spelling its article. -/
public def DocClass.ofString? : String → Option DocClass
  | "article" => some .article
  | "slides" => some .slides
  | "card" => some .card
  | "resume" => some .resume
  | "webpage" => some .webpage
  | "poster" => some .poster
  | "scrartcl" | "scrreprt" | "scrbook" => some .koma
  | _ => none

public theorem DocClass.ofString?_name (c : DocClass) : ofString? c.name = some c := by
  cases c <;> rfl

/-- Every class, in the order a help lists them. -/
@[expose] public def DocClass.all : List DocClass :=
  [.article, .slides, .card, .resume, .webpage, .poster, .koma]

public theorem DocClass.all_complete (c : DocClass) : c ∈ DocClass.all := by
  cases c <;> simp [DocClass.all]

public theorem DocClass.all_nodup : DocClass.all.Nodup := by decide

/-- Each class as its record: slides' 11 pt is beamer's, the card's and
résumé's floor the fluent-reading x-height at hand-held distance. -/
@[expose] public def DocClass.record : DocClass → ClassRecord
  | .article =>
    { model := .flow
      sizeFileSkip := true
      area := .sizeFile
      numberHeadings := true
      measureBand := true
      pageNumbers := true }
  | .slides =>
    { model := .frame
      fontSize := some slidesFontSize
      parskip := some {}
      lists := .beamer
      preambleSans := true
      chrome := true
      groundDepth := .decks
      colorRow := .stage
      schemes := .own
      abstractForm := .inset }
  | .card =>
    { model := .face
      abstractForm := .inset
      colorRow := .stage
      schemes := .own
      runningFurniture := false
      pagesBound := some .faces
      inkInArea := some "the margins are the print safe zone: ink past them risks \
the trim; declare \\assert{ text.in_area } to take control"
      xHeightFloor := some (cardXHeightFloor,
        "1.4mm x-height is the fluent-reading floor at hand-held \
distance (Legge & Bigelow 2011); declare \\assert{ text.xheight >= ... } to take control")
      trimDefault := some (Dim.mm100 8560, Dim.mm100 5398)
      safeMargin := some (Dim.mm 5) }
  | .resume =>
    { model := .flow
      measureBand := true
      parskip := some {}
      pagesBound := some (.lit .eq 1)
      pagesHelp := "the resume class asserts content fits one page; \
declare \\assert{ pages <= N } to take control"
      inkInArea := some "the margins frame what every printer keeps: ink past \
them risks the clip; declare \\assert{ text.in_area } to take control"
      xHeightFloor := some (cardXHeightFloor,
        "1.4mm x-height is the fluent-reading floor at hand-held \
distance (Legge & Bigelow 2011); declare \\assert{ text.xheight >= ... } to take control") }
  | .webpage =>
    { model := .flow
      measureBand := true
      lists := .web
      colorRow := .web
      formats := #["html", "md"]
      mdName := some "llms.txt" }
  | .poster =>
    { model := .face
      abstractForm := .inset
      fontSize := some posterFontSize
      lists := .beamer
      colorRow := .stage
      schemes := .own
      preambleSans := true
      headline := true
      groundDepth := .posters
      pagesBound := some .faces
      inkInArea := some "the margins are the print safe zone: ink past them risks \
the trim; declare \\assert{ text.in_area } to take control"
      xHeightFloor := some (posterXHeightFloor,
        "3.5mm x-height is the fluent-reading floor (Legge & Bigelow 2011) \
at 1m, the distance where a poster body at beamerposter's own 24.88pt \
calibration reads fluently; declare \
\\assert{ text.xheight >= ... } to take control")
      -- ISO 216 A0, landscape: beamerposter's default board.
      trimDefault := some (Dim.mm 1189, Dim.mm 841)
      safeMargin := some (Dim.mm 10) }
  -- scrkernel-fontsize.dtx's 11pt, scrkernel-paragraphs.dtx's `parskip=false`.
  | .koma =>
    { model := .flow
      fontSize := some (Dim.pt 11)
      sizeFileSkip := true
      -- typearea's `paper=a4`, its default.
      trimDefault := some a4Page
      parskip := some texParskipDefault
      parskipOption := true
      listExtra := .koma
      -- scrkernel-listsandtabulars.dtx's quotation.
      quotationIndent := { em := 1000 }
      numberHeadings := true
      measureBand := true
      pageNumbers := true
      area := .typearea }

/-- A document's class defaults: its class's colour row and ground depth, the
web's row for a source that is not tex. -/
@[expose] public def DocClass.classColors (c : DocClass) (surface : Surface) : ClassColors :=
  { row := if surface == .tex then c.record.colorRow else .web
    depth := c.record.groundDepth }

public theorem poster_model_face : (DocClass.poster).record.model = .face := by rfl

/-- The paragraph separation a class's `parskip` option sets from its `\baselineskip`, as
scrkernel-paragraphs.dtx's `\setparsizes` reads each value; `none` for one it does not name. -/
public def classParskip? (value : Option String) (skip : Length) : Option SymGlue :=
  let lines (w st : Int) : SymGlue :=
    { width := Dim.SymLength.ofLength (skip * w / 10), stretch := Dim.SymLength.ofLength (skip * st / 10) }
  match value.getD "true" with
  | "never" => some {}
  | "false" | "off" | "no" => some texParskipDefault
  | "full" | "full-" | "full+" | "full*" | "true" | "on" | "yes" => some (lines 10 1)
  | "half" | "half-" | "half+" | "half*" => some (lines 5 5)
  | _ => none

/-- The space a class's `parskip` option keeps free after a paragraph's last line, as
`\setparsizes` sets `\parfillskip`; `none` where the line may run to the margin. -/
public def classParfill? (value : Option String) : Option String :=
  match value.getD "true" with
  | "full" | "half" | "true" | "on" | "yes" => some "1em"
  | "full+" | "half+" => some "a third of the line"
  | "full*" | "half*" => some "a quarter of the line"
  | _ => none

/-- The font a package measures its lengths in as it loads: Latin Modern at
the class's `\normalsize`, its sans under beamer. -/
public structure PreambleFace where
  size : Length
  xHeight : Length
  deriving Repr, BEq, Inhabited

/-- A class's preamble font at the `\normalsize` its size option sets. -/
public def PreambleFace.ofClass (rec : ClassRecord) (size : Length) : PreambleFace :=
  let size := optionNormalSize size
  { size, xHeight := size * (if rec.preambleSans then 444 else 431) / 1000 }

/-- The article class's preamble font at its default size. -/
public def PreambleFace.article : PreambleFace := PreambleFace.ofClass DocClass.article.record baseFontSize

/-- A length as the preamble font fixes it: its em at the class size, its ex
at Latin Modern's x-height there. -/
public def PreambleFace.resolve (face : PreambleFace) (l : Dim.SymLength) : Length :=
  l.resolve face.size face.xHeight

/-- The lengths a class or package fixes as it loads: the table lengths and `\leftmargin⟨n⟩`. -/
public def loadLength (name : String) : Bool :=
  (tableLengths.lookup name).isSome || leftMarginNamed name

/-- The lengths `fixes` names, fixed as `\setlength` evaluates them in the preamble's font. -/
public def PreambleFace.fixLengths (face : PreambleFace) (fixes : String → Bool) (tk : Tokens) :
    Tokens :=
  { entries := tk.entries.map fun (n, g) =>
      if fixes n then (n, { g with width := Dim.SymLength.ofLength (face.resolve g.width) })
      else (n, g) }

/-- The load-fixed lengths a preamble declares, fixed in the preamble's font. -/
public def PreambleFace.fixLoadLengths (face : PreambleFace) (tk : Tokens) : Tokens :=
  face.fixLengths loadLength tk

/-- A list or quotation level's `\leftmargin⟨n⟩` as its class fixes it, in the preamble font. -/
public def leftMarginAt (l : ListLineage) (tokens : Tokens) (face : PreambleFace) (level : Nat) :
    Length :=
  face.resolve (leftMarginFor l tokens level).width

/-- The poster's headline band: title, authors, institute, the `\title` family
read as class furniture. -/
public structure Headline where
  title : Array Inline
  author : Array Inline := #[]
  institute : Array Inline := #[]
  deriving Repr, BEq, Inhabited

/-- One piece of recovered ink: the loss that named it, the command it stood
for, and the source text the recovery kept. -/
public structure Recovered where
  code : DiagCode
  /-- The refused command's name, without its backslash. -/
  command : String
  /-- The source the groups carried, as the author wrote it. -/
  text : String
  deriving Repr, BEq

/-- The diagnostic subject a recovery is paid for under: `warnOnce`'s own key. -/
@[expose] public def Recovered.subject (s : Recovered) : String := "ctrl:" ++ s.command

/-- What a boundary request draws: a `tikzpicture` body, or a whole commutative diagram. -/
public inductive PicKind where
  | picture
  | cd
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The environment a standalone opens around a request's body. -/
@[expose] public def PicKind.env : PicKind → String
  | .picture => "tikzpicture"
  | .cd => "tikzcd"

/-- The standalone's document opening, through the size switch in force where
the picture stands, and the kind's environment opening. -/
@[expose] public def PicKind.docOpen : PicKind → Option String → String
  | .picture, none => "\\begin{document}\n\\begin{tikzpicture}"
  | .cd, none => "\\begin{document}\n\\begin{tikzcd}"
  | k, some sw => "\\begin{document}\n" ++ sw ++ "\n\\begin{" ++ k.env ++ "}"

/-- The kind's environment closing, then the document's. -/
@[expose] public def PicKind.docClose : PicKind → String
  | .picture => "\\end{tikzpicture}\n\\end{document}\n"
  | .cd => "\\end{tikzcd}\n\\end{document}\n"

/-- One boundary request as the document wrote it: its kind, its body, and the
size switch in force where it stands. -/
public structure PicSrc where
  kind : PicKind
  body : String
  size : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The source a request's identity is the hash of: the body or the whole
diagram environment, after the size switch in force. -/
@[expose] public def PicSrc.source (s : PicSrc) : String :=
  let core := match s.kind with
    | .picture => s.body
    | .cd => "\\begin{" ++ s.kind.env ++ "}" ++ s.body ++ "\\end{" ++ s.kind.env ++ "}"
  match s.size with
  | none => core
  | some z => "\\" ++ z ++ " " ++ core

/-- The macro a deck's `\AtBeginSection` or `\AtBeginSubsection` defines and each section it
opens calls: the starred one for a starred section or one with a blank title, as beamer's. -/
@[expose] public def sectionHookName (sub starred : Bool) : String :=
  " atbegin" ++ (if sub then "subsection" else "section") ++ (if starred then "s" else "")

/-- Whether a control is one of the hooks a deck's sections call. -/
@[expose] public def isSectionHookName (n : String) : Bool :=
  [sectionHookName false false, sectionHookName false true, sectionHookName true false,
    sectionHookName true true].contains n

/-- The control a theme's section hook calls: the section's own page. -/
public def sectionPageCtrl : String := " sectionpage"

/-- The block a theme's section hook leaves right after its section: the section's own page. -/
public def sectionPageRole : String := "section-page"

/-- The block a frame of the document's own setting only `\sectionpage` leaves after its section,
by the frame's alignment. -/
public def framedSectionPageRole : VAlign → String
  | .top => "section-page framed t"
  | .bottom => "section-page framed b"
  | .center | .golden => "section-page framed"

/-- The alignment of the document's own frame a section page after a deck's section stands in. -/
public def framedSectionPage? (next : Option Block) : Option VAlign :=
  match next with
  | some (.role n body) =>
    if body.isEmpty then [VAlign.top, .center, .bottom].find? (framedSectionPageRole · == n) else none
  | _ => none

/-- Whether the block after a deck's section is its section page, so the section stands on a page
of its own; any other names navigation alone, as beamer's `\section` does. -/
@[expose] public def standsOnPage (next : Option Block) : Bool :=
  (match next with
    | some (.role n body) => n == sectionPageRole && body.isEmpty
    | _ => false) || (framedSectionPage? next).isSome

/-- The glue a section page spends about its content: the document's own frame's under the deck's
keys, a theme's divider moloch's `[c]`. -/
public def sectionPageGlue (keys : FrameKeys) (next : Option Block) : FrameGlue :=
  match framedSectionPage? next with
  | some v => frameGlue keys false v
  | none => VAlign.glue .moloch .center

/-- A hand-written mark: `\markboth`'s left and right texts, or `\markright`'s right text alone. -/
public structure PageMark where
  left : Option (Array Inline)
  right : Array Inline
  deriving Repr, BEq, Inhabited

/-- A heading's short title, `\section[short]{long}`'s: the heading by its number, its words and how
many unstarred headings before it set both, and its short title. -/
public structure ShortTitle where
  number : Option String
  words : String
  nth : Nat
  short : Array Inline
  /-- Whether `\nameref` reads it, as a heading's own short title, not a contents line's. -/
  named : Bool
  /-- The number its contents line sets where it is not the heading's own: a chapter's bare number,
  `\numberline`'s argument. -/
  listed : Option String
  deriving Repr, BEq, Inhabited

public structure Doc where
  docClass : DocClass := .article
  surface : Surface := .tex
  classOptions : String := ""
  /-- The class heads chapters (report.cls, book.cls): a body h1 is a chapter. -/
  chapters : Bool := false
  /-- How the abstract's body sets: its class's form under the title-page options, or a
  redefinition's quotation. -/
  abstractForm : AbstractForm := .quotation
  page : PageSpec := {}
  fonts : FontSpec := {}
  palette : Palette := {}
  tokens : Tokens := {}
  /-- The caption positions the document declares, by float type scope (`""` for every type). -/
  captionPos : Array (String × CaptionPos) := #[]
  /-- The marker each itemize level's class label (`\labelitemi`…`\labelitemiv`) is redefined to,
  by level; a declared level style's marker stands over it. -/
  itemLabels : Array (Nat × Array Inline) := #[]
  /-- `\runninghead` / `\runningfoot`: one line of inline content each, laid
  out in the margin after the body. -/
  head : Option (Array Inline) := none
  foot : Option (Array Inline) := none
  /-- A verso's own running head and foot on two-sided pages (fancyhdr's `E` fields), else `head`
  and `foot` serve every page. -/
  headEven : Option (Array Inline) := none
  footEven : Option (Array Inline) := none
  /-- beamer's `\logo`: inline content placed at the lower-right corner of
  every page carrying running content. -/
  logo : Option (Array Inline) := none
  /-- The headline band a headline class draws; `none` on every other class
  and when no title is declared. -/
  headline : Option Headline := none
  /-- `\logoleft` / `\logoright`: the headline band's two corner slots. -/
  logoLeft : Option (Array Inline) := none
  logoRight : Option (Array Inline) := none
  /-- First page that carries the running head (`\runninghead[from = 2]`). -/
  headFrom : Nat := 1
  /-- First page that carries the running foot; `\thispagestyle{empty}` on the
  opening page sets both to `2`. -/
  footFrom : Nat := 1
  /-- Slide chrome, the themed default footer's slots, which `foot` wins over. -/
  chrome : Chrome := {}
  /-- Whether the document itself declared `\chrome`, not a theme installing its default. -/
  chromeDeclared : Bool := false
  /-- The frame-alignment keys the deck's theme sets (`Theme.frameKeys`). -/
  frameKeys : FrameKeys := .beamer
  styles : Styles := {}
  info : Meta := {}
  output : OutputSpec := {}
  asserts : Array Assertion := #[]
  /-- `\allow{W0307, ...}`: diagnostic codes whose losses this document
  accepts, downgraded to warnings and always printed. -/
  allow : Array String := #[]
  /-- The citation setup natbib or biblatex loads: `none` with neither, else its declarations in
  the order they apply. -/
  citeSetup : Option (Array CiteDecl) := none
  /-- The boundary tool in force: the external TeX the driver runs for
  pictures outside the rendered subset. -/
  pictureTool : Option String := some "lualatex"
  /-- Whether an external converter may draw a figure the engine cannot draw
  whole; `\figures{ convert = none }` refuses. -/
  figureConvert : Bool := true
  /-- The boundary requests this document states: `(id, src)`, the identity
  the content hash of the author's bytes. -/
  pictureSrcs : Array (String × PicSrc) := #[]
  /-- The preamble a boundary standalone needs beyond the document's design:
  non-native package loads and tikz set lines, as written. -/
  picturePreamble : String := ""
  /-- The directories graphicx searches for an included file after the
  document's own (`\graphicspath{{dir/}…}`), in order. -/
  graphicsPath : Array String := #[]
  /-- The document's own macro definitions, in document order: the name, and
  the declaration as the boundary standalone reads it. -/
  pictureMacros : Array (String × String) := #[]
  /-- The ink this document carries that its author did not write: one entry
  per refused and recovered construct, in flow order. -/
  salvage : Array Recovered := #[]
  /-- Where the frame numbering starts over: the body index of the first block
  after `\appendix` under appendixnumberbeamer. -/
  frameRestart : Option Nat := none
  /-- The short titles headings declared, which a flow's contents and bookmarks list. -/
  shortTitles : Array ShortTitle := #[]
  /-- The marks `\markboth` and `\markright` set, by the index their roles name. -/
  marks : Array PageMark := #[]
  /-- The roles the document's own colour declarations set, a theme's aside. -/
  ownRoles : Array Role := #[]
  /-- Where each `\bibliography` list's footnotes number from, in document
  order, and how many notes its fields set. -/
  listNotes : Array (Nat × Nat) := #[]
  body : Array Block := #[]
  deriving Repr, BEq, Inhabited

/-- A body's frame numbering: numbered whole, or each part from 1 where `restart` splits it. -/
public def frameNumbersFrom (restart : Option Nat) (body : Array Block) : Array (Option Nat) :=
  match restart with
  | none => frameNumbers body
  | some p => frameNumbers (body.extract 0 p) ++ frameNumbers (body.extract p body.size)

/-- The rule the document's list levels read the `\parskip` in force by: the parskip package's
where it loads, else the class's. -/
public def Doc.listExtra (doc : Doc) : ListExtra :=
  if doc.page.listsParskip then .koma else doc.docClass.record.listExtra

/-- The document's frame numbering: the body numbered whole, or each part from
1 where `frameRestart` splits it. -/
public def Doc.frameNumbers (doc : Doc) : Array (Option Nat) :=
  frameNumbersFrom doc.frameRestart doc.body

/-- The document's footline numbers, from 1 again where `frameRestart` splits the body; a counted
title page shows its number under a footer the document declares or moloch's, which it keeps. -/
public def Doc.frameShown (doc : Doc) : Array (Option Nat) :=
  let t := doc.frameKeys == .moloch || doc.chromeDeclared
  match doc.frameRestart with
  | none => Ir.frameShown t doc.body
  | some p => Ir.frameShown t (doc.body.extract 0 p) ++ Ir.frameShown t (doc.body.extract p doc.body.size)

/-- The numbering's denominator at body index `i`: the count of the part `i` stands in. -/
public def Doc.frameCountAt (doc : Doc) (i : Nat) : Nat :=
  match doc.frameRestart with
  | none => Ir.frameCount doc.body
  | some p =>
    if i < p then Ir.frameCount (doc.body.extract 0 p)
    else Ir.frameCount (doc.body.extract p doc.body.size)

/-- The numbering's denominator where the document starts. -/
public def Doc.frameCount (doc : Doc) : Nat :=
  doc.frameCountAt 0

/-- The name each frame is known by at its body index: its number
(`appendix-n` from `frameRestart` on), else `standout`, `standout-2`, … or
`titlepage`, `titlepage-2`, …; `none` at every other block. -/
public def Doc.frameLabels (doc : Doc) : Array (Option String) := Id.run do
  let nums := doc.frameNumbers
  let mut standouts := 0
  let mut titlePages := 0
  let mut unnumbered := 0
  let mut out : Array (Option String) := #[]
  for h : i in [0:doc.body.size] do
    match doc.body[i] with
    | .frame _ standout valign _ fbody =>
      match nums[i]?.getD none with
      | some n =>
        out := out.push (some (if doc.frameRestart.any (· ≤ i) then s!"appendix-{n}"
          else toString n))
      | none =>
        if (frameMarks fbody).contains unnumberedRole && !(valign matches .golden) then
          unnumbered := unnumbered + 1
          out := out.push (some s!"unnumbered-{unnumbered}")
        else if standout then
          out := out.push (some (if standouts == 0 then "standout"
            else s!"standout-{standouts + 1}"))
          standouts := standouts + 1
        else
          out := out.push (some (if titlePages == 0 then "titlepage"
            else s!"titlepage-{titlePages + 1}"))
          titlePages := titlePages + 1
    | _ => out := out.push none
  return out

/-- The document's preamble font, at its class size. -/
public def Doc.preambleFace (doc : Doc) : PreambleFace :=
  PreambleFace.ofClass doc.docClass.record doc.page.fontSize

/-- Where a deck's chrome may stand: a class whose record draws it, with no
`\runningfoot` owning the foot. -/
public def Doc.chromeAllowed (doc : Doc) : Bool :=
  doc.docClass.record.chrome && doc.foot.isNone

/-- Whether a frame stands its body in beamer's text area, the paper's top
edge to `\footheight` above its bottom edge. -/
public def frameInTextArea (chromeAllowed : Bool) (valign : VAlign) : Bool :=
  chromeAllowed && !(valign matches .golden)

public theorem Doc.frameNumbers_restart_exact (doc : Doc) (p : Nat)
    (h : doc.frameRestart = some p) :
    doc.frameNumbers.toList.filterMap id =
      List.range' 1 (Ir.frameCount (doc.body.extract 0 p)) ++
        List.range' 1 (Ir.frameCount (doc.body.extract p doc.body.size)) := by
  simp only [Doc.frameNumbers, frameNumbersFrom, h, Array.toList_append, List.filterMap_append,
    frameNumbers_gapless]

public theorem Doc.frameNumbers_size (doc : Doc) : doc.frameNumbers.size = doc.body.size := by
  unfold Doc.frameNumbers frameNumbersFrom
  split
  · exact Ir.frameNumbers_size doc.body
  · simp only [Array.size_append, Ir.frameNumbers_size, Array.size_extract]
    omega

/-- Whether the artifacts carry the document's faces: a declared `fonts =`
wins, else the stylesheet rule. -/
public def Doc.fontPolicy (doc : Doc) : FontPolicy :=
  match doc.output.contract.fonts with
  | some p => p
  | none => if doc.output.css.isNone then .embedded else .none

/-- Whether pages carry the plain page number: the document's own
`\page{ numbers = ... }`, else its class default. -/
@[expose] public def Doc.pageNumbersOn (doc : Doc) : Bool :=
  doc.page.numbers.getD doc.docClass.record.pageNumbers

/-- Whether counted body lines carry margin line numbers: the document's own
declaration and nothing else. -/
@[expose] public def Doc.lineNumbersOn (doc : Doc) : Bool :=
  doc.page.linenumbers.getD false

/-- The line-number modulus in force, at least 1; 1 unless declared. -/
public def Doc.lineModulo (doc : Doc) : Nat :=
  max 1 (doc.page.lineModulo.getD 1)

/-- A symbolic glue as it was declared, for goldens. -/
public def dumpGlue (g : SymGlue) : String :=
  let part (l : SymLength) : String :=
    let bits := (if l.fixed != 0 then [s!"{l.fixed.toPtString}pt"] else []) ++
      (if l.em != 0 then [s!"{l.em}/1000em"] else []) ++
      (if l.ex != 0 then [s!"{l.ex}/1000ex"] else [])
    if bits.isEmpty then "0" else String.intercalate "+" bits
  let base := part g.width
  let plus := if g.stretch == ({} : SymLength) then "" else s!" plus {part g.stretch}"
  let minus := if g.shrink == ({} : SymLength) then "" else s!" minus {part g.shrink}"
  base ++ plus ++ minus

/-- A sourced glue as the golden shows it: the declared value and its token name. -/
private def dumpSourcedGlue (g : Sourced SymGlue) : String :=
  match g.token with
  | some n => s!"{dumpGlue g.value} from {n}"
  | none => dumpGlue g.value

/-- LaTeX's own punctuation: the characters that are markup in a math source
and never its content. -/
public def markupChars : List Char := ['\\', '{', '}', '$', '&', '^', '_', '~']

/-- Control words whose leading `{...}` arguments name something rather than
carry content, with how many do. -/
public def floorNamedArgs : List (String × Nat) :=
  [("textcolor", 1), ("colorbox", 1), ("fcolorbox", 2), ("color", 1),
   ("pagecolor", 1), ("label", 1), ("ref", 1), ("eqref", 1), ("tag", 1),
   ("hspace", 1), ("vspace", 1), ("raisebox", 1), ("begin", 1), ("end", 1),
   ("cite", 1), ("phantom", 1), ("hphantom", 1), ("vphantom", 1),
   ("parbox", 1), ("rule", 2), ("setlength", 2), ("addtolength", 2),
   ("cancelto", 1)]

/-- Past a balanced `{...}` beginning at `i`, or past the end when it never closes. -/
private def skipBalanced (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  let mut depth := 0
  for _ in [0:cs.size + 1] do
    if j ≥ cs.size then break
    let c := (cs[j]?).getD ' '
    if c == '{' then
      depth := depth + 1
      j := j + 1
    else if c == '}' then
      j := j + 1
      if depth ≤ 1 then break else depth := depth - 1
    else
      j := j + 1
  return j

/-- Past a `[...]` option run beginning at `i`, else `i` itself. -/
private def skipOption (cs : Array Char) (i : Nat) : Nat := Id.run do
  if (cs[i]?).getD ' ' != '[' then return i
  let mut j := i + 1
  for _ in [0:cs.size + 1] do
    if j ≥ cs.size then break
    let c := (cs[j]?).getD ' '
    j := j + 1
    if c == ']' then break
  return j

/-- Past the spaces at `i`. -/
private def skipFloorWs (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:cs.size + 1] do
    if j ≥ cs.size then break
    if !((cs[j]?).getD 'x').isWhitespace then break
    j := j + 1
  return j

/-- Which characters of a math source are content, one flag per character:
control-sequence names and named arguments are markup. -/
public def floorMask (src : String) : Array Bool := Id.run do
  let cs := src.toList.toArray
  let at? (k : Nat) : Char := (cs[k]?).getD ' '
  let mut keep : Array Bool := Array.replicate cs.size true
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    if at? i != '\\' then
      i := i + 1
    else
      keep := keep.setIfInBounds i false
      let mut j := i + 1
      if j < cs.size && !(at? j).isAlpha then
        let sym := at? j
        keep := keep.setIfInBounds j false
        j := j + 1
        -- Only `\\` takes an option run: after `\{` or `\,` a bracket is content.
        if sym == '\\' then
          let optStart := skipFloorWs cs j
          let stop := skipOption cs optStart
          if stop != optStart then
            for m in [j:stop] do
              keep := keep.setIfInBounds m false
            j := stop
      else
        let mut name := ""
        for _ in [0:cs.size + 1] do
          if j ≥ cs.size then break
          if !(at? j).isAlpha then break
          name := name.push (at? j)
          keep := keep.setIfInBounds j false
          j := j + 1
        let star := skipFloorWs cs j
        if at? star == '*' then
          for m in [j:star + 1] do
            keep := keep.setIfInBounds m false
          j := star + 1
        -- An option run right after the name is the command's, whether or not the engine knows it.
        let optStart := skipFloorWs cs j
        let optStop := skipOption cs optStart
        if optStop != optStart then
          for m in [j:optStop] do
            keep := keep.setIfInBounds m false
          j := optStop
        if let some arity := floorNamedArgs.lookup name then
          for _ in [0:arity] do
            let opened := skipFloorWs cs (skipOption cs (skipFloorWs cs j))
            -- Mask the run up to the group before the `{` test, so a failed scan still drops it.
            for m in [j:opened] do
              keep := keep.setIfInBounds m false
            if at? opened != '{' then
              j := opened
              break
            let stop := skipBalanced cs opened
            for m in [opened:stop] do
              keep := keep.setIfInBounds m false
            j := stop
          -- `\raisebox{lift}[height][depth]{body}`: options trail the named argument.
          for _ in [0:2] do
            let stop := skipOption cs j
            if stop == j then break
            for m in [j:stop] do
              keep := keep.setIfInBounds m false
            j := stop
      i := j
  -- A second pass squeezes the whitespace a dropped command leaves behind.
  let survives (k : Nat) : Bool :=
    (keep[k]?.getD false) && !markupChars.contains (at? k)
  let mut lastSpace := true
  for k in [0:cs.size] do
    if survives k then
      if (at? k).isWhitespace then
        if lastSpace then keep := keep.setIfInBounds k false
        else lastSpace := true
      else lastSpace := false
  let mut last := cs.size
  for _ in [0:cs.size + 1] do
    if last == 0 then break
    let k := last - 1
    if survives k then
      if (at? k).isWhitespace then keep := keep.setIfInBounds k false else break
    last := k
  return keep

/-- What the salvage keeps: the math source's own content characters, LaTeX's
punctuation removed. -/
public def floorChars (src : String) : List Char :=
  let mask := floorMask src
  (src.toList.zipIdx.filterMap fun (c, i) =>
    if (mask[i]?.getD true) && !markupChars.contains c then some c else none)

/-- The placeholder a formula sets when its salvage comes to nothing. -/
public def mathFloorPlaceholder : List Char := ['[', '\u2026', ']']

/-- The characters a degraded formula inks: its salvage, or the placeholder
when the salvage is empty. -/
public def floorInk (src : String) : List Char :=
  let cs := floorChars src
  if cs.isEmpty then mathFloorPlaceholder else cs

/-- The floor for math the elaborator cannot model: the formula's text
content, or a visible placeholder when it has none. -/
public def mathFloor (src : String) : String := String.ofList (floorInk src)

/-- Math accents with their combining marks and stretch flags, from unicode-math's accent table. -/
public def mathAccentCommands : List (String × Char × Bool) :=
  [("hat", '\u0302', false), ("widehat", '\u0302', true),
   ("tilde", '\u0303', false), ("widetilde", '\u0303', true),
   ("bar", '\u0304', false), ("dot", '\u0307', false), ("ddot", '\u0308', false),
   ("vec", '\u20D7', false), ("overline", '\u0305', true)]

namespace FormulaText

-- A structural reading of the math AST: the glyph census omits rule-drawn operators.
private def grouped (s : String) : String := (String.singleton '(' ++ s).push ')'

private def optionalChar : Option Char → String
  | none => ""
  | some c => String.singleton c

private def script (marker body : String) : String :=
  if body.isEmpty then "" else
    let text := grouped body
    marker ++ text

private def scripts (base sup sub : String) : String :=
  if sup.isEmpty && sub.isEmpty then base
  else grouped base ++ script "_" sub ++ script "^" sup

private def fraction (spec : Math.FracSpec) (num den : String) : String :=
  optionalChar spec.left ++
    (if spec.rule = some 0 then
      if num.isEmpty && den.isEmpty then "" else "stack" ++ grouped (num ++ ";" ++ den)
     else grouped num ++ "/" ++ grouped den) ++
    optionalChar spec.right

private def radical (degree body : String) : String :=
  let text := grouped body
  if degree.isEmpty then
    "sqrt" ++ text
  else
    let index := grouped degree
    "root" ++ index ++ text

private def cancellation (mark : Math.CancelMark) (value body : String) : String :=
  let name := match mark with
    | .up => "cancel" | .down => "bcancel" | .cross => "xcancel" | .to => "cancelto"
  let text := grouped (body ++
    (if mark = .to then ";" ++ value
     else if value.isEmpty then "" else ";" ++ value))
  name ++ text

mutual

private def list (acc : String) : Math.MList → String
  | .nil => acc
  | .cons x rest => list (acc ++ item x) rest

private def item : Math.MItem → String
  | .atom _ n sup sub _ => scripts (nucleus n) (list "" sup) (list "" sub)
  | .space _ => ""
  | .ink _ _ => ""

private def nucleus : Math.MNucleus → String
  | .sym c => String.singleton c
  | .styled _ c => String.singleton c
  | .word s => s
  | .list body => list "" body
  | .alpha _ _ body => list "" body
  | .frac spec num den => fraction spec (list "" num) (list "" den)
  | .rad deg body => radical (list "" deg) (list "" body)
  | .delim left right body =>
    let text := optionalChar left ++ list "" body
    let close := optionalChar right
    text ++ close
  | .big d _ => optionalChar d
  | .grid _ rs =>
    let text := rows "" rs
    if text.isEmpty then "" else "[" ++ text ++ "]"
  | .accent mark wide body =>
    let name := ((mathAccentCommands.find? (fun p => p.2 == (mark, wide))).map (·.1)).getD "accent"
    name ++ grouped (list "" body)
  | .cancel mark _ value body => cancellation mark (list "" value) (list "" body)

private def row (acc : String) : Math.MRow → String
  | .nil => acc
  | .cons c rest => row (acc ++ list "" c ++ (match rest with
      | .nil => "" | .cons _ _ => ",")) rest

private def rows (acc : String) : Math.MRows → String
  | .nil => acc
  | .cons r rest => rows (acc ++ "[" ++ row "" r ++ "]" ++ (match rest with
      | .nil => "" | .cons _ _ => ",")) rest

end

private theorem script_length (marker body : String) : body.length ≤ (script marker body).length := by
  simp only [script]
  split
  · rename_i h
    simp_all
  · simp [grouped, String.length_append]
    omega

private theorem scripts_length (base sup sub : String) :
    base.length + sup.length + sub.length ≤ (scripts base sup sub).length := by
  simp only [scripts]
  split
  · rename_i h
    simp_all
  · have hs := script_length "^" sup
    have hb := script_length "_" sub
    simp only [grouped, String.length_append, String.length_push, String.length_singleton] at *
    omega

private theorem fraction_length (spec : Math.FracSpec) (num den : String) :
    (optionalChar spec.left).length + num.length + den.length + (optionalChar spec.right).length ≤
      (fraction spec num den).length := by
  simp only [fraction]
  split
  · split
    · rename_i h
      simp_all
    · simp only [grouped, String.length_append, String.length_push, String.length_singleton]
      omega
  · simp only [grouped, String.length_append, String.length_push, String.length_singleton]
    omega

private theorem radical_length (deg body : String) :
    deg.length + body.length ≤ (radical deg body).length := by
  simp only [radical]
  split
  · rename_i h
    simp_all [grouped]
    omega
  · simp only [grouped, String.length_append, String.length_push, String.length_singleton]
    omega

private theorem cancellation_length (mark : Math.CancelMark) (value body : String) :
    body.length + value.length ≤ (cancellation mark value body).length := by
  cases mark <;> by_cases h : value.isEmpty <;> simp_all [cancellation, grouped] <;> omega

mutual

private theorem list_length : ∀ (body : Math.MList) (chars : Array Char) (text : String),
    (Math.MList.scalarsList true chars body).size + text.length ≤
      (list text body).length + chars.size
  | .nil, _, _ => by simp [list, Math.MList.scalarsList, Nat.add_comm]
  | .cons x rest, chars, text => by
    have hx := item_length x chars
    have hr := list_length rest (x.scalars true chars) (text ++ item x)
    simp only [list, Math.MList.scalarsList, String.length_append] at *
    omega

private theorem item_length : ∀ (x : Math.MItem) (chars : Array Char),
    (x.scalars true chars).size ≤ chars.size + (item x).length
  | .space _, _ => by simp [item, Math.MItem.scalars]
  | .ink _ _, _ => by simp [item, Math.MItem.scalars]
  | .atom _ n sup sub _, chars => by
    have hn := nucleus_length n chars
    have hs := list_length sup (n.scalars true chars) ""
    have hb := list_length sub (Math.MList.scalarsList true (n.scalars true chars) sup) ""
    have h := scripts_length (nucleus n) (list "" sup) (list "" sub)
    simp only [item, Math.MItem.scalars, String.length_empty, Nat.add_zero] at *
    omega

private theorem nucleus_length : ∀ (n : Math.MNucleus) (chars : Array Char),
    (n.scalars true chars).size ≤ chars.size + (nucleus n).length
  | .sym c, _ => by simp [Math.MNucleus.scalars, nucleus]
  | .styled _ c, _ => by simp [Math.MNucleus.scalars, nucleus]
  | .word s, _ => by
    simp [Math.MNucleus.scalars, nucleus, String.foldl_eq_foldl_toList, String.length_toList]
  | .list b, chars => by
    simpa [Math.MNucleus.scalars, nucleus, Nat.add_comm] using list_length b chars ""
  | .alpha _ _ b, chars => by
    simpa [Math.MNucleus.scalars, nucleus, Nat.add_comm] using list_length b chars ""
  | .frac spec num den, chars => by
    have hn := list_length num (match spec.left with
      | none => chars | some c => chars.push c) ""
    have hd := list_length den (Math.MList.scalarsList true (match spec.left with
      | none => chars | some c => chars.push c) num) ""
    have h := fraction_length spec (list "" num) (list "" den)
    simp only [Math.MNucleus.scalars, nucleus]
    cases hl : spec.left <;> cases hr : spec.right <;>
      simp [hl, hr, optionalChar, String.length_empty] at * <;> omega
  | .rad deg b, chars => by
    have hd := list_length deg chars ""
    have hb := list_length b (Math.MList.scalarsList true chars deg) ""
    have h := radical_length (list "" deg) (list "" b)
    simp only [Math.MNucleus.scalars, nucleus, String.length_empty, Nat.add_zero] at *
    omega
  | .delim l r b, chars => by
    have h := list_length b (match r with
      | none => (match l with | none => chars | some c => chars.push c)
      | some c => (match l with | none => chars | some c => chars.push c).push c) ""
    cases l <;> cases r <;>
      simp_all [Math.MNucleus.scalars, nucleus, optionalChar, String.length_append] <;> omega
  | .big d _, chars => by
    cases d <;> simp [Math.MNucleus.scalars, nucleus, optionalChar]
  | .grid _ rs, chars => by
    have h := rows_length rs chars ""
    simp only [Math.MNucleus.scalars, nucleus]
    split
    · rename_i hz
      simp_all
    · simp only [String.length_append]
      simp only [String.length_empty, Nat.add_zero] at h
      omega
  | .accent mark _ b, chars => by
    have h := list_length b (if mark == '\u0305' then chars else chars.push mark) ""
    simp only [Math.MNucleus.scalars, nucleus, grouped, String.length_append,
      String.length_push, String.length_singleton]
    split <;> simp_all <;> omega
  | .cancel mark _ value b, chars => by
    have hb := list_length b chars ""
    have hv := list_length value (Math.MList.scalarsList true chars b) ""
    have h := cancellation_length mark (list "" value) (list "" b)
    simp only [Math.MNucleus.scalars, nucleus, String.length_empty, Nat.add_zero] at *
    omega

private theorem row_length : ∀ (r : Math.MRow) (chars : Array Char) (text : String),
    (r.scalarsRow true chars).size + text.length ≤ (row text r).length + chars.size
  | .nil, _, _ => by simp [row, Math.MRow.scalarsRow, Nat.add_comm]
  | .cons c rest, chars, text => by
    have hc := list_length c chars ""
    have hr := row_length rest (Math.MList.scalarsList true chars c)
      (text ++ list "" c ++ (match rest with | .nil => "" | .cons _ _ => ","))
    simp only [row, Math.MRow.scalarsRow, String.length_append, String.length_empty,
      Nat.add_zero] at *
    omega

private theorem rows_length : ∀ (rs : Math.MRows) (chars : Array Char) (text : String),
    (rs.scalarsRows true chars).size + text.length ≤ (rows text rs).length + chars.size
  | .nil, _, _ => by simp [rows, Math.MRows.scalarsRows, Nat.add_comm]
  | .cons r rest, chars, text => by
    have hc := row_length r chars ""
    have hr := rows_length rest (r.scalarsRow true chars)
      (text ++ "[" ++ row "" r ++ "]" ++ (match rest with | .nil => "" | .cons _ _ => ","))
    simp only [rows, Math.MRows.scalarsRows, String.length_append, String.length_empty,
      Nat.add_zero] at *
    omega

end

mutual

private theorem list_mapInk (f : Ir.Color → Option ColorRef → Ir.Color) :
    ∀ (body : Math.MList) (acc : String), list acc (Math.MList.mapInk f body) = list acc body
  | .nil, _ => rfl
  | .cons x rest, acc => by
    simp only [Math.MList.mapInk, list, item_mapInk f x, list_mapInk f rest]

private theorem item_mapInk (f : Ir.Color → Option ColorRef → Ir.Color) :
    ∀ (x : Math.MItem), item (Math.MItem.mapInk f x) = item x
  | .space _ => rfl
  | .ink _ _ => rfl
  | .atom _ n sup sub _ => by
    simp only [Math.MItem.mapInk, item, nucleus_mapInk f n, list_mapInk f sup,
      list_mapInk f sub]

private theorem nucleus_mapInk (f : Ir.Color → Option ColorRef → Ir.Color) :
    ∀ (n : Math.MNucleus), nucleus (Math.MNucleus.mapInk f n) = nucleus n
  | .sym _ => rfl
  | .styled _ _ => rfl
  | .word _ => rfl
  | .list body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f body]
  | .alpha _ _ body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f body]
  | .frac _ num den => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f num, list_mapInk f den]
  | .rad deg body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f deg, list_mapInk f body]
  | .delim _ _ body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f body]
  | .big _ _ => rfl
  | .grid _ rs => by
    simp only [Math.MNucleus.mapInk, nucleus, rows_mapInk f rs]
  | .accent _ _ body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f body]
  | .cancel _ _ value body => by
    simp only [Math.MNucleus.mapInk, nucleus, list_mapInk f value, list_mapInk f body]

private theorem row_mapInk (f : Ir.Color → Option ColorRef → Ir.Color) :
    ∀ (r : Math.MRow) (acc : String), row acc (Math.MRow.mapInk f r) = row acc r
  | .nil, _ => rfl
  | .cons c rest, acc => by
    simp only [Math.MRow.mapInk, row, list_mapInk f c]
    rw [row_mapInk f rest]
    cases rest <;> rfl

private theorem rows_mapInk (f : Ir.Color → Option ColorRef → Ir.Color) :
    ∀ (rs : Math.MRows) (acc : String), rows acc (Math.MRows.mapInk f rs) = rows acc rs
  | .nil, _ => rfl
  | .cons r rest, acc => by
    simp only [Math.MRows.mapInk, rows, row_mapInk f r]
    rw [rows_mapInk f rest]
    cases rest <;> rfl

end

end FormulaText

/-- The shared plaintext reading of a parsed formula, in AsciiMath's linear notation. -/
public def formulaFloor (body : Math.MList) : String := FormulaText.list "" body

public theorem formulaFloor_content_covers (body : Math.MList) :
    (Math.MList.scalarsList true #[] body).size ≤ (formulaFloor body).length := by
  simpa [formulaFloor] using FormulaText.list_length body #[] ""

public theorem formulaFloor_ink_id (f : Color → Option ColorRef → Color) (body : Math.MList) :
    formulaFloor (Math.MList.mapInk f body) = formulaFloor body :=
  FormulaText.list_mapInk f body ""

public theorem formulaFloor_separates (num den : Math.MList) :
    formulaFloor (.cons (.atom .ord (.frac {} num den) .nil .nil false) .nil) ≠
      formulaFloor num ++ formulaFloor den := by
  intro h
  have hlen := congrArg String.length h
  simp [formulaFloor, FormulaText.list, FormulaText.item, FormulaText.nucleus,
    FormulaText.scripts, FormulaText.fraction, FormulaText.optionalChar, FormulaText.grouped,
    String.length_append] at hlen
  omega

public theorem floorChars_mem (src : String) :
    ∀ c ∈ floorChars src, c ∈ src.toList ∧ c ∉ markupChars := by
  intro c hc
  simp only [floorChars, List.mem_filterMap] at hc
  obtain ⟨p, hp, hq⟩ := hc
  by_cases hk : (floorMask src)[p.2]?.getD true && !markupChars.contains p.1
  · simp only [hk, ite_true] at hq
    cases hq
    refine ⟨?_, ?_⟩
    · have hm : p.1 ∈ (src.toList.zipIdx 0).map Prod.fst := List.mem_map_of_mem hp
      rw [List.zipIdx_map_fst] at hm
      exact hm
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
      simpa using hk.2
  · simp only [Bool.not_eq_true] at hk
    simp only [hk] at hq
    simp at hq

private theorem filterMap_eq_map_fst {α β : Type} (l : List (α × β)) (g : α × β → Option α)
    (hg : ∀ p ∈ l, g p = some p.1) : l.filterMap g = l.map Prod.fst := by
  induction l with
  | nil => simp
  | cons p rest ih =>
    rw [List.filterMap_cons, hg p (by simp), List.map_cons,
      ih (fun q hq => hg q (by simp [hq]))]

public theorem floorMask_id (src : String)
    (h : ∀ c ∈ src.toList, c ≠ '\\' ∧ c ∉ markupChars ∧ c.isWhitespace = false) :
    floorMask src = Array.replicate src.toList.length true := by
  have hat : ∀ i, i < src.toList.length → (src.toList[i]?.getD ' ') ∈ src.toList := by
    intro i hi
    rw [List.getElem?_eq_getElem hi]
    simp [List.getElem_mem]
  have hws : ∀ i, i < src.toList.length →
      (src.toList[i]?.getD ' ').isWhitespace = false :=
    fun i hi => (h _ (hat i hi)).2.2
  have hbs : ∀ i, i < src.toList.length → (src.toList[i]?.getD ' ') ≠ '\\' :=
    fun i hi => (h _ (hat i hi)).1
  have hrep : ∀ j, ((Array.replicate src.toList.length true)[j]?).getD false = true →
      j < src.toList.length := by
    intro j hj
    simp only [Array.getElem?_replicate] at hj
    split at hj
    · assumption
    · simp at hj
  simp only [floorMask, List.size_toArray]
  refine Loop.bind_eq_of_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _
    (Loop.forIn_range_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _ _ rfl ?step1) ?rest
  case step1 =>
    intro i _ _ b hb
    split
    · exact hb
    · rename_i hlt
      split
      · exact hb
      · rename_i hne
        exact absurd (by simpa using hne) (hbs b.2 (by omega))
  case rest =>
  intro b hb
  rw [hb]
  refine Loop.bind_eq_of_inv (fun (st : Array Bool × Bool) =>
      st.1 = Array.replicate src.toList.length true) _ _ _
    (Loop.forIn_range_inv (fun (st : Array Bool × Bool) =>
      st.1 = Array.replicate src.toList.length true) _ _ _ _ rfl ?step2) ?rest2
  case step2 =>
    intro i _ hi c hc
    split
    · split
      · rename_i hw; exact absurd hw (by simp [hws i hi])
      · exact hc
    · exact hc
  case rest2 =>
  intro c hc
  rw [hc]
  refine Loop.bind_eq_of_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _
    (Loop.forIn_range_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _ _ rfl ?step3) ?rest3
  case step3 =>
    intro i _ _ d hd
    split
    · exact hd
    · split
      · rename_i hsv
        have hlt : d.2 - 1 < src.toList.length := hrep _ (by
          simpa using (Bool.and_eq_true _ _ ▸ hsv : _ ∧ _).1)
        split
        · rename_i hw; exact absurd hw (by simp [hws _ hlt])
        · exact hd
      · exact hd
  case rest3 =>
  intro d hd
  exact hd

public theorem floorChars_id (src : String)
    (h : ∀ c ∈ src.toList,
      c ≠ '\\' ∧ c ∉ markupChars ∧ c.isWhitespace = false) :
    floorChars src = src.toList := by
  simp only [floorChars, floorMask_id src h]
  rw [filterMap_eq_map_fst]
  · exact List.zipIdx_map_fst 0 src.toList
  · intro p hp
    have hmem : p.1 ∈ src.toList := by
      have hm := List.mem_map_of_mem (f := Prod.fst) hp
      rwa [List.zipIdx_map_fst] at hm
    simp [Array.getElem?_replicate, (h _ hmem).2.1]
    split <;> simp

public theorem floorInk_mem (src : String) :
    ∀ c ∈ floorInk src,
      (c ∈ src.toList ∨ c ∈ mathFloorPlaceholder) ∧ c ∉ markupChars := by
  intro c hc
  simp only [floorInk] at hc
  split at hc
  · refine ⟨Or.inr hc, ?_⟩
    simp only [mathFloorPlaceholder, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> decide
  · obtain ⟨hsrc, hmk⟩ := floorChars_mem src c hc
    exact ⟨Or.inl hsrc, hmk⟩

public theorem floorInk_accounts (src : String) : floorInk src ≠ [] := by
  simp only [floorInk]
  split
  · simp [mathFloorPlaceholder]
  · rename_i h
    simpa [List.isEmpty_iff] using h

/-- Where a salvage's characters come from, which decides how much of the floor is checkable. -/
public inductive Salvage where
  | filtered
  | translated
  deriving Repr, BEq, DecidableEq

/-- The recovery floor as one judge: whether a salvage delivered what
`Loss.floor` declares a construct's place owes. -/
@[expose] public def FloorHonest (f : Floor) (s : Salvage) (carried ink : List Char) : Prop :=
  (f.ships = false → ink = []) ∧
  (f.inks = true → carried ≠ [] → ink ≠ []) ∧
  (s = .filtered → ∀ c ∈ ink,
    (c ∈ carried ∨ c ∈ mathFloorPlaceholder) ∧ c ∉ markupChars)

public theorem formulaFloor_covers (c : DiagCode) (h : c.floor.ships) (body : Math.MList) :
    FloorHonest c.floor .translated
      (Math.MList.scalarsList true #[] body).toList (formulaFloor body).toList := by
  refine ⟨fun hn => absurd (h.symm.trans hn) (by decide), fun _ hc hi => ?_,
    fun hn => nomatch hn⟩
  have hc' : (Math.MList.scalarsList true #[] body).size > 0 := by
    simpa [← Array.length_toList, List.length_pos_iff] using hc
  have hi' : (formulaFloor body).length = 0 := by
    simpa [String.length_toList] using congrArg List.length hi
  have bound := formulaFloor_content_covers body
  omega

/-- Whether this construct carried content at all: the source's content
characters, read through the floor's mask. -/
public def floorCarries (src : String) : Bool := !(floorChars src).isEmpty

public theorem floorInk_covers (c : DiagCode) (h : c.floor.ships) (src : String) :
    FloorHonest c.floor .filtered src.toList (floorInk src) := by
  refine ⟨fun hn => absurd (h.symm.trans hn) (by decide), fun _ _ => ?_, fun _ => ?_⟩
  · exact floorInk_accounts src
  · exact floorInk_mem src

public theorem floorInk_degraded_covers (src : String) :
    FloorHonest Loss.degraded.floor .filtered src.toList (floorInk src) := by
  exact ⟨fun hn => absurd (Loss.degraded_floor_ships_exact.symm.trans hn) (by decide),
    fun _ _ => floorInk_accounts src,
    fun _ => floorInk_mem src⟩


/-- Typographic punctuation for ordinary text: `--` and `---` as dashes, `...`
as an ellipsis, and TeX's quote ligatures. -/
public def smartPunct (s : String) : String :=
  String.ofList (go s.toList [])
where
  /-- `prev` is the output so far, reversed; two-character ligatures match
  before single characters. -/
  go : List Char → List Char → List Char
    | [], prev => prev.reverse
    | '-' :: '-' :: '-' :: rest, prev => go rest ('—' :: prev)
    | '-' :: '-' :: rest, prev => go rest ('–' :: prev)
    | '.' :: '.' :: '.' :: rest, prev => go rest ('…' :: prev)
    | '`' :: '`' :: rest, prev => go rest ('“' :: prev)
    | '`' :: rest, prev => go rest ('‘' :: prev)
    | '\'' :: '\'' :: rest, prev => go rest ('”' :: prev)
    | '!' :: '`' :: rest, prev => go rest ('¡' :: prev)
    | '?' :: '`' :: rest, prev => go rest ('¿' :: prev)
    | '"' :: rest, prev =>
      let opening := match prev with
        | [] => true
        | c :: _ => c == ' ' || c == '(' || c == '[' || c == '—' || c == '–'
      go rest ((if opening then '“' else '”') :: prev)
    | '\'' :: rest, prev =>
      let opening := match prev with
        | [] => true
        | c :: _ => c == ' ' || c == '(' || c == '[' || c == '“'
      go rest ((if opening then '‘' else '’') :: prev)
    | c :: rest, prev => go rest (c :: prev)

/-- `smartPunct` for text set right after `lead`, the character before it in reading order, which
an opening quote decides against as a quote inside the text decides against its own. -/
public def smartPunctAfter (lead : Option Char) (s : String) : String :=
  match lead with
  | none => smartPunct s
  | some c => String.ofList ((smartPunct.go s.toList [c]).drop 1)

/-- What an object a quote follows reads as: U+FFFC, which no opening test admits. -/
private def objectLead : Char := '\ufffc'

/-- `smartPunct` for text TeX sets whole inside a word, a label's, where a quote opening it closes
as TeX's own ligature sets it. -/
public def smartPunctInWord (s : String) : String := smartPunctAfter (some objectLead) s

/-- The character a lead reads for a white-space character: a space, as `smartPunct` reads it. -/
private def leadChar (c : Char) : Char :=
  if c.isWhitespace || c == '\u00a0' || c == '\u202f' || c == '\u3000' ||
      ('\u2000' ≤ c && c ≤ '\u200a') then ' ' else c

mutual

/-- The last character `x` sets in reading order, `none` where it sets none: a text's last
character, a space for glue or a break, and U+FFFC for other ink, a note's mark too. -/
-- conserves: none — reads the last character set, from the end, a note's body behind its mark.
public def lastSet (x : Inline) : Option Char :=
  match x with
  | .text s => if s.isEmpty then none else some (leadChar s.back)
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
  | .decorated _ body | .boxed _ body | .onSteps _ body => lastSetBefore body body.size
  | .altSteps _ firstPage _ => lastSetBefore firstPage firstPage.size
  | .cited _ _ ink => (lastSetBefore ink ink.size).orElse fun _ => some objectLead
  | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .ref _ _ _ _ | .cite _ _
  | .rule _ _ _ | .pageNumber | .pageCount | .footnote _ _ => some objectLead
  | .fill | .hspace _ _ | .linebreak _ => some ' '
  | .label _ | .strut _ | .italicCorr _ => none
termination_by (sizeOf x, 0)
decreasing_by all_goals (simp_wf; omega)

/-- The last character the inlines of `xs` before index `n` set, read back from there. -/
public def lastSetBefore (xs : Array Inline) (n : Nat) : Option Char :=
  match n with
  | 0 => none
  | k + 1 =>
    if h : k < xs.size then (lastSet xs[k]).orElse fun _ => lastSetBefore xs k
    else none
termination_by (sizeOf xs, n)
decreasing_by
  · simp_wf
    have := Array.sizeOf_getElem xs k h
    omega
  · simp_wf
    exact Prod.Lex.right _ (Nat.lt_succ_self k)

end

/-- The character text set after `xs` follows in reading order, `none` where `xs` sets none. -/
public def quoteLead (xs : Array Inline) : Option Char := lastSetBefore xs xs.size

@[simp] public theorem quoteLead_empty : quoteLead #[] = none := by
  simp [quoteLead, lastSetBefore]

/-- One run onto a merge: a text run after a text run joins it. -/
@[expose] public def mergeStep (out : Array Inline) (x : Inline) : Array Inline :=
  match x, out.back? with
  | .text s, some (.text t) => out.pop.push (.text (t ++ s))
  | _, _ => out.push x

@[simp] public theorem mergeStep_empty (x : Inline) : mergeStep #[] x = #[x] := by
  cases x <;> rfl

/-- Adjacent text runs joined into one, every space kept. -/
@[expose] public def mergeTexts (xs : Array Inline) : Array Inline := xs.foldl mergeStep #[]

mutual

/-- The characters of inline content with every mark stripped. -/
@[expose] public def plainText (xs : Array Inline) : String :=
  plainTextList xs.toList

@[expose] public def plainTextList (xs : List Inline) : String :=
  match xs with
  | [] => ""
  | x :: rest => plainTextOne x ++ plainTextList rest

@[expose] public def plainTextOne (x : Inline) : String :=
  match x with
  | .text s => s
  | .math _ src => mathFloor src
  | .formula _ _ body => formulaFloor body
  | .styled _ body => plainTextList body.toList
  | .colored _ _ body => plainTextList body.toList
  | .located _ body => plainTextList body.toList
  | .role _ body => plainTextList body.toList
  | .link _ body => plainTextList body.toList
  | .decorated _ body | .boxed _ body => plainTextList body.toList
  | .onSteps _ body => plainTextList body.toList
  | .altSteps _ firstPage otherPage =>
    plainTextList firstPage.toList ++ plainTextList otherPage.toList
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount => ""
  | .image _ _ _ => ""
  | .icon _ label => label
  | .label _ => ""
  | .ref _ _ text _ => text
  | .cite _ keys => citeMarks keys
  | .cited _ _ ink => plainTextList ink.toList
  -- The note body is document text; its mark digit is generated ink.
  | .footnote _ body => plainTextList body.toList
  | .linebreak _ => " "

end

mutual

/-- `plainTextList` onto `acc`, in time linear in the characters it reads. -/
public def plainTextOntoList (acc : String) : List Inline → String
  | [] => acc
  | x :: rest => plainTextOntoList (plainTextOntoOne acc x) rest

public def plainTextOntoOne (acc : String) (x : Inline) : String :=
  match x with
  | .text s => acc ++ s
  | .math _ src => acc.append (mathFloor src)
  | .formula _ _ body => acc.append (formulaFloor body)
  | .styled _ body => plainTextOntoList acc body.toList
  | .colored _ _ body => plainTextOntoList acc body.toList
  | .located _ body => plainTextOntoList acc body.toList
  | .role _ body => plainTextOntoList acc body.toList
  | .link _ body => plainTextOntoList acc body.toList
  | .decorated _ body | .boxed _ body => plainTextOntoList acc body.toList
  | .onSteps _ body => plainTextOntoList acc body.toList
  | .altSteps _ firstPage otherPage =>
    plainTextOntoList (plainTextOntoList acc firstPage.toList) otherPage.toList
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount => acc
  | .image _ _ _ => acc
  | .icon _ label => acc ++ label
  | .label _ => acc
  | .ref _ _ text _ => acc ++ text
  | .cite _ keys => acc.append (citeMarks keys)
  | .cited _ _ ink => plainTextOntoList acc ink.toList
  | .footnote _ body => plainTextOntoList acc body.toList
  | .linebreak _ => acc ++ " "

end

mutual

private theorem plainTextOntoList_exact (acc : String) :
    ∀ xs, acc ++ plainTextList xs = plainTextOntoList acc xs
  | [] => by simp [plainTextOntoList, plainTextList]
  | x :: rest => by
    rw [plainTextOntoList, ← plainTextOntoList_exact _ rest, ← plainTextOntoOne_exact acc x,
      plainTextList, String.append_assoc]

private theorem plainTextOntoOne_exact (acc : String) (x : Inline) :
    acc ++ plainTextOne x = plainTextOntoOne acc x := by
  cases x <;> first
    | rfl
    | simp only [plainTextOntoOne, plainTextOne, ← plainTextOntoList_exact, String.append_assoc,
        String.append_empty]

end

/-- `plainTextList` as the compiled program runs it. -/
public def plainTextListOnto (xs : List Inline) : String := plainTextOntoList "" xs

/-- `plainTextOne` as the compiled program runs it. -/
public def plainTextOneOnto (x : Inline) : String := plainTextOntoOne "" x

/-- `plainText` as the compiled program runs it. -/
public def plainTextOnto (xs : Array Inline) : String := plainTextOntoList "" xs.toList

@[csimp] public theorem plainTextList_onto_exact : @plainTextList = @plainTextListOnto := by
  funext xs
  simp [plainTextListOnto, ← plainTextOntoList_exact]

@[csimp] public theorem plainTextOne_onto_exact : @plainTextOne = @plainTextOneOnto := by
  funext x
  simp [plainTextOneOnto, ← plainTextOntoOne_exact]

@[csimp] public theorem plainText_onto_exact : @plainText = @plainTextOnto := by
  funext xs
  simp [plainText, plainTextOnto, ← plainTextOntoList_exact]

mutual

/-- The text an overlay sequence shows with no snap state, onto `acc`, an alternation giving the
floor's group (`HtmlDoc.altPairNodes`), where the generic fold visits both. -/
-- conserves: none — one page's reading.
public def firstPageTextOne (acc : String) (x : Inline) : String :=
  match x with
  | .altSteps spec firstPage otherPage =>
    let blank (xs : Array Inline) : Bool := !(plainText xs).toList.any (!·.isWhitespace)
    if spec.maxStep == 0 || (blank firstPage && !blank otherPage) then
      firstPageTextList acc otherPage.toList
    else firstPageTextList acc firstPage.toList
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body
  | .link _ body | .decorated _ body | .boxed _ body | .onSteps _ body | .footnote _ body | .cited _ _ body =>
    firstPageTextList acc body.toList
  -- A page reference's folio is the layout's, so a reading made before it and one after agree.
  | .ref _ .page _ _ => acc
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .label _
  | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _
  | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
    String.append acc (plainTextOne x)

public def firstPageTextList (acc : String) : List Inline → String
  | [] => acc
  | x :: rest => firstPageTextList (firstPageTextOne acc x) rest

end

/-- The text the first page of an overlay sequence shows. -/
public def firstPageText (xs : Array Inline) : String := firstPageTextList "" xs.toList

/-- A metadata field's characters with the controls no artifact carries alike dropped: C0 and C1
controls but tab, line feed and return, and the two noncharacters XML refuses. -/
public def metaClean (s : String) : String :=
  String.ofList (s.toList.filter fun c =>
    c == '\t' || c == '\n' || c == '\r' ||
      (0x20 ≤ c.toNat && !(0x7F ≤ c.toNat && c.toNat ≤ 0x9F) && c.toNat != 0xFFFE &&
        c.toNat != 0xFFFF))

/-- The text a metadata field holds of inline content: its first page's, quotes as the page sets
them, a tie a space as hyperref reads `~`, and no control `metaClean` drops (`metaEscapeChecks`). -/
public def metaText (xs : Array Inline) : String :=
  metaClean ((firstPageText xs).map fun c => if c == '\u00A0' then ' ' else c)

/-- The words a picture's labels set, in shape order, joined: what a sighted
reader reads in the drawing. -/
public def Pic.Picture.said (pic : Pic.Picture) : String :=
  String.intercalate ", " (pic.labelContents.toList.filterMap fun content =>
    let s := plainText content
    if s.toList.any (!·.isWhitespace) then some s.trimAscii.toString else none)

/-- The alternative a reader of either artifact gets for a picture: the
author's declaration, else its labels' words. -/
public def Pic.Picture.alternative (pic : Pic.Picture) : Alt :=
  match pic.alt with
  | .undeclared => Alt.declare pic.said
  | .decorative => .decorative
  | .described t => .described t
  | .citing runs => .citing runs

public theorem role_plaintext (n : String) (body : Array Inline) :
    plainTextOne (.role n body) = plainTextList body.toList := by rfl

mutual

/-- One leaf-parameterised fold for every collect walk: `fi` reads each inline
node in document order, a node before its content. -/
@[expose] public def foldInline (fi : α → Inline → α) (acc : α) (x : Inline) : α :=
  match x with
  | .styled _ body => foldInlineList fi (fi acc x) body.toList
  | .colored _ _ body => foldInlineList fi (fi acc x) body.toList
  | .located _ body => foldInlineList fi (fi acc x) body.toList
  | .role _ body => foldInlineList fi (fi acc x) body.toList
  | .link _ body => foldInlineList fi (fi acc x) body.toList
  | .decorated _ body | .boxed _ body => foldInlineList fi (fi acc x) body.toList
  | .onSteps _ body => foldInlineList fi (fi acc x) body.toList
  | .altSteps _ firstPage otherPage =>
    foldInlineList fi (foldInlineList fi (fi acc x) firstPage.toList) otherPage.toList
  | .footnote _ body => foldInlineList fi (fi acc x) body.toList
  | .cited _ _ ink => foldInlineList fi (fi acc x) ink.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ => fi acc x

@[expose] public def foldInlineList (fi : α → Inline → α) (acc : α) : List Inline → α
  | [] => acc
  | x :: rest => foldInlineList fi (foldInline fi acc x) rest

end

@[expose] public def foldInlines (fi : α → Inline → α) (acc : α) (xs : Array Inline) : α :=
  foldInlineList fi acc xs.toList

/-- The label keys inlines hold, nested ones included, in order. -/
public def labelKeys (content : Array Inline) : Array String :=
  foldInlines (fun out x => match x with
    | .label key => out.push key
    | _ => out) #[] content

/-- The first contributing source location, in document order. -/
-- conserves: none — reads provenance.
public def inlineSource (content : Array Inline) : Option Span :=
  foldInlines (fun source inline => match inline with
    | .located span _ => source.orElse (fun _ => some span)
    | .text _ | .math _ _ | .formula _ _ _ | .styled _ _
      | .colored _ _ _ | .role _ _ | .link _ _ | .label _
      | .ref _ _ _ _ | .decorated _ _ | .boxed _ _ | .fill | .hspace _ _
      | .rule _ _ _ | .pageNumber | .pageCount | .linebreak _
      | .strut _ | .italicCorr _ | .onSteps _ _ | .altSteps _ _ _
      | .image _ _ _ | .icon _ _ | .cite _ _ | .cited _ _ _ | .footnote _ _ => source)
    none content

/-- `foldInline` over algorithm lines: each line's content, then its comment, in reading order. -/
@[expose] public def foldAlgLines (fi : α → Inline → α) (acc : α) : List AlgLine → α
  | [] => acc
  | l :: rest =>
    foldAlgLines fi (match l.comment with
      | some c => foldInlineList fi (foldInlineList fi acc l.content.toList) c.toList
      | none => foldInlineList fi acc l.content.toList) rest

/-- `foldInline` over a laid-out paragraph's lines, in reading order. -/
@[expose] public def foldLaidLines (fi : α → Inline → α) (acc : α) : List LaidLine → α
  | [] => acc
  | l :: rest => foldLaidLines fi (foldInlineList fi acc l.content.toList) rest

/-- `foldInline` over a reference list's items: each entry's content, in list order. -/
@[expose] public def foldBibItems (fi : α → Inline → α) (acc : α) : List BibItem → α
  | [] => acc
  | it :: rest => foldBibItems fi (foldInlineList fi acc it.content.toList) rest

/-- `foldInline` over a table of contents' entries: each entry's title, in list order. -/
@[expose] public def foldContentsEntries (fi : α → Inline → α) (acc : α) :
    List ContentsEntry → α
  | [] => acc
  | e :: rest => foldContentsEntries fi (foldInlineList fi acc e.title.toList) rest

mutual

/-- The block face of the fold: `fb` reads each block, `fi` each inline, the
node first, a frame's title and a float's caption before their bodies. -/
@[expose] public def foldBlock (fb : α → Block → α) (fi : α → Inline → α) (acc : α) (b : Block) : α :=
  match b with
  | .para content => foldInlineList fi (fb acc b) content.toList
  | .equation number content =>
    foldInlineList fi (foldInlineList fi (fb acc b) content.toList) number.toList
  | .section _ _ _ title => foldInlineList fi (fb acc b) title.toList
  | .list _ _ items => foldBlockItems fb fi (fb acc b) items.toList
  | .center body => foldBlockList fb fi (fb acc b) body.toList
  | .ragged _ body => foldBlockList fb fi (fb acc b) body.toList
  | .quote _ body => foldBlockList fb fi (fb acc b) body.toList
  | .lines ls => foldLaidLines fi (fb acc b) ls.toList
  | .abstract body => foldBlockList fb fi (fb acc b) body.toList
  | .titled _ title body =>
    foldBlockList fb fi (foldInlineList fi (fb acc b) title.toList) body.toList
  | .disclosure title _ body =>
    foldBlockList fb fi (foldInlineList fi (fb acc b) title.toList) body.toList
  | .role _ body => foldBlockList fb fi (fb acc b) body.toList
  | .link _ body => foldBlockList fb fi (fb acc b) body.toList
  | .spaced _ body => foldBlockList fb fi (fb acc b) body.toList
  | .columns cols => foldBlockCols fb fi (fb acc b) cols.toList
  | .onSteps _ body => foldBlockList fb fi (fb acc b) body.toList
  | .altSteps _ firstPage otherPage =>
    foldBlockList fb fi (foldBlockList fb fi (fb acc b) firstPage.toList) otherPage.toList
  | .only _ body => foldBlockList fb fi (fb acc b) body.toList
  | .nav _ body => foldBlockList fb fi (fb acc b) body.toList
  | .note body => foldBlockList fb fi (fb acc b) body.toList
  | .frame title _ _ _ body =>
    foldBlockList fb fi (foldInlineList fi (fb acc b) title.toList) body.toList
  | .framefoot content => foldInlineList fi (fb acc b) content.toList
  | .float _ _ _ body caption =>
    foldBlockList fb fi (foldInlineList fi (fb acc b) caption.toList) body.toList
  | .table _ _ _ rows _ _ => foldTableRows fb fi (fb acc b) rows.toList
  | .algorithm _ _ lines => foldAlgLines fi (fb acc b) lines.toList
  | .logo content => foldInlineList fi (fb acc b) content.toList
  | .bibliography _ _ items => foldBibItems fi (fb acc b) items.toList
  | .contents _ entries => foldContentsEntries fi (fb acc b) entries.toList
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ => fb acc b

@[expose] public def foldBlockList (fb : α → Block → α) (fi : α → Inline → α) (acc : α) :
    List Block → α
  | [] => acc
  | b :: rest => foldBlockList fb fi (foldBlock fb fi acc b) rest

@[expose] public def foldBlockItems (fb : α → Block → α) (fi : α → Inline → α) (acc : α) :
    List (Array Block) → α
  | [] => acc
  | item :: rest => foldBlockItems fb fi (foldBlockList fb fi acc item.toList) rest

@[expose] public def foldBlockCols (fb : α → Block → α) (fi : α → Inline → α) (acc : α) :
    List (BoxWidth × Array Block) → α
  | [] => acc
  | (_, body) :: rest => foldBlockCols fb fi (foldBlockList fb fi acc body.toList) rest

/-- `foldBlock` over a table's rows: each row's cells in order, each cell's blocks. -/
@[expose] public def foldTableRows (fb : α → Block → α) (fi : α → Inline → α) (acc : α) :
    List (Array (Array Block)) → α
  | [] => acc
  | row :: rest => foldTableRows fb fi (foldBlockItems fb fi acc row.toList) rest

end

@[expose] public def foldBlocks (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (xs : Array Block) : α :=
  foldBlockList fb fi acc xs.toList

/-- The label keys blocks hold, nested ones included, in order. -/
public def blockLabelKeys (body : Array Block) : Array String :=
  foldBlocks (fun out _ => out) (fun out x => match x with
    | .label key => out.push key
    | _ => out) #[] body

/-- Whether blocks hold a list anywhere: what beamer's squeeze changes. -/
public def holdsList (body : Array Block) : Bool :=
  foldBlocks (fun acc b => acc || b matches .list ..) (fun acc _ => acc) false body

/-- Whether blocks hold `k` lists, each inside an item of the one before. -/
public def holdsNestedLists : Nat → Array Block → Bool
  | 0, _ => true
  | k + 1, body => foldBlocks (fun acc b => acc || if let .list _ _ items := b then
      items.any (holdsNestedLists k) else false) (fun acc _ => acc) false body

/-- Whether blocks hold a frame anywhere. -/
public def holdsFrame (body : Array Block) : Bool :=
  foldBlocks (fun acc b => acc || b matches .frame ..) (fun acc _ => acc) false body

/-- What a deck sets for a block outside every frame. -/
public inductive Outside where
  /-- A page and a stage of its own: a frame, a section page, a boundary. -/
  | stage
  /-- Content beamer sets on a page of its own, with what stands beside it outside the frames. -/
  | content
  /-- Nothing a page shows: navigation, an anchor, a note, a state change or a mark. -/
  | none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Whether a block sets nothing a page shows: an empty paragraph or one of label anchors, an empty
list, or a container holding only such blocks. -/
public def setsNothing : Block → Bool
  | .para content => content.isEmpty || anchorsOnly content
  | .lines ls => ls.all fun l => l.content.isEmpty || anchorsOnly l.content
  | .list _ _ items => items.isEmpty
  | .center body | .ragged _ body | .spaced _ body | .role _ body | .link _ body | .quote _ body
  | .onSteps _ body | .only _ body => body.attach.all fun ⟨b, _⟩ => setsNothing b
  | .section .. | .abstract _ | .titled .. | .disclosure .. | .equation .. | .verbatim ..
  | .algorithm .. | .columns _ | .altSteps .. | .note _ | .nav .. | .logo _ | .pagebreak
  | .frame .. | .framefoot _ | .setPalette _ | .setTokens _ | .rule .. | .picture _ | .table ..
  | .float .. | .bibliography .. => false
  | .contents _ entries => entries.isEmpty

/-- What a deck sets for a top-level block outside every frame, given the block after it: a stage of
its own, content on a page of its own, or nothing a page shows. -/
public def outsideUnder (next : Option Block) (b : Block) : Outside :=
  if holdsFrame #[b] then .stage
  else if setsNothing b then .none
  else match b with
    | .frame .. | .pagebreak => .stage
    | .setPalette _ | .setTokens _ | .logo _ | .framefoot _ | .note _ => .none
    | .section level _ _ _ =>
      if level == .title then .content
      else if standsOnPage next then .stage
      else .none
    | .para _ | .list .. | .center .. | .ragged .. | .spaced .. | .role .. | .link .. | .quote .. | .lines ..
    | .abstract .. | .titled .. | .disclosure .. | .equation .. | .verbatim .. | .algorithm ..
    | .columns .. | .onSteps .. | .altSteps .. | .only .. | .nav .. | .rule .. | .picture ..
    | .table .. | .float .. | .bibliography .. | .contents .. => .content

/-- What a deck sets for its top-level block `i` outside every frame (`outsideUnder`). -/
public def Doc.outside (doc : Doc) (i : Nat) (b : Block) : Outside := outsideUnder doc.body[i + 1]? b

/-- Each top-level block's short-title record where it is a heading elaboration holds one for,
every unstarred heading counted in document order by its number and words. -/
public def shortEntriesAt (shorts : Array ShortTitle) (body : Array Block) :
    Array (Option ShortTitle) := Id.run do
  if shorts.isEmpty then return body.map fun _ => none
  let byKey : Std.HashMap (Option String × String × Nat) ShortTitle :=
    shorts.foldl (fun m s => if m.contains (s.number, s.words, s.nth) then m
      else m.insert (s.number, s.words, s.nth) s) {}
  let count := fun (m : Std.HashMap (Option String × String) Nat) (b : Block) =>
    if let .section level false num title := b then
      if level == .title then m else
        let k := (num, plainText title)
        m.insert k (m.getD k 0 + 1)
    else m
  let mut seen : Std.HashMap (Option String × String) Nat := {}
  let mut out : Array (Option ShortTitle) := #[]
  for b in body do
    let mut here : Option ShortTitle := none
    if let .section level false num title := b then
      if level != .title then
        let words := plainText title
        here := byKey.get? (num, words, seen.getD (num, words) 0)
    out := out.push here
    seen := foldBlocks count (fun m _ => m) seen #[b]
  return out

/-- Each top-level block's short title where it is a heading that declared one (`shortEntriesAt`). -/
public def shortTitlesAt (shorts : Array ShortTitle) (body : Array Block) :
    Array (Option (Array Inline)) :=
  (shortEntriesAt shorts body).map (·.map (·.short))

/-- The title a flow's contents and bookmarks list for top-level block `i`, a heading setting
`title`: its short title where it declared one (`shortTitlesAt`), else its title. -/
public def listedTitleAt (shorts : Array (Option (Array Inline))) (i : Nat) (title : Array Inline) :
    Array Inline :=
  (shorts[i]?.join).getD title

/-- The spacings a body's lists and quotations declare, each once, in flow order. -/
public def listSetsOf (body : Array Block) : Array ListSet :=
  (foldBlocks (fun (acc : Array ListSet × Std.HashSet ListSet) b =>
      let s : ListSet := match b with
        | .list _ s _ => s
        | .quote q _ => q.spacing
        | _ => {}
      if s == {} || acc.2.contains s then acc else (acc.1.push s, acc.2.insert s))
    (fun acc _ => acc) (#[], {}) body).1

/-- The quotation kinds a body holds, each once, in flow order. -/
public def quoteKindsOf (body : Array Block) : Array QuoteKind :=
  foldBlocks (fun (acc : Array QuoteKind) b => match b with
      | .quote q _ => if acc.contains q.kind then acc else acc.push q.kind
      | _ => acc)
    (fun acc _ => acc) #[] body

/-- Whether an item closes on a nested list, quotation or trivlist, whose skip `\endtrivlist`
re-reads; not where it is the item's one block, which opening in the item's label leaves none. -/
public def itemClosesOnSkip (item : Array Block) : Bool :=
  if item.size < 2 then false else
  match item.back? with
  | some b => b.opensInLabel || match b with
    | .role n #[c] => n == inParagraphRole && c.opensInLabel
    | _ => false
  | none => false

/-- The events a context-threading walk declares. -/
public structure CtxFold (γ : Type) (α : Type) where
  /-- Entering a block: the accumulator, and the context its content is
  read under. -/
  openBlock : γ → α → Block → α × γ
  /-- Leaving a block, under the context the block was entered in. -/
  closeBlock : γ → α → Block → α
  /-- Entering an inline node: the accumulator, and the context its
  content is read under. -/
  openInline : γ → α → Inline → α × γ
  /-- Leaving an inline node, under the context it was entered in. -/
  closeInline : γ → α → Inline → α

mutual

/-- `foldInline`'s descent with a context and a close event: the context
`openInline` returns is in force over that node's content alone. -/
public def foldCtxInline (w : CtxFold γ α) (ctx : γ) (acc : α) (x : Inline) : α :=
  match x with
  | .styled _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .colored _ _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .located _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .role _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .link _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .decorated _ body | .boxed _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .onSteps _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .altSteps _ firstPage otherPage =>
    let r := w.openInline ctx acc x
    w.closeInline ctx
      (foldCtxInlineList w r.2 (foldCtxInlineList w r.2 r.1 firstPage.toList)
        otherPage.toList) x
  | .footnote _ body =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 body.toList) x
  | .cited _ _ ink =>
    let r := w.openInline ctx acc x
    w.closeInline ctx (foldCtxInlineList w r.2 r.1 ink.toList) x
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
    w.closeInline ctx (w.openInline ctx acc x).1 x

public def foldCtxInlineList (w : CtxFold γ α) (ctx : γ) (acc : α) : List Inline → α
  | [] => acc
  | x :: rest => foldCtxInlineList w ctx (foldCtxInline w ctx acc x) rest

end

public def foldCtxInlines (w : CtxFold γ α) (ctx : γ) (acc : α) (xs : Array Inline) : α :=
  foldCtxInlineList w ctx acc xs.toList

/-- `foldCtxInline` over algorithm lines: content then comment. -/
public def foldCtxAlgLines (w : CtxFold γ α) (ctx : γ) (acc : α) : List AlgLine → α
  | [] => acc
  | l :: rest =>
    foldCtxAlgLines w ctx (match l.comment with
      | some c => foldCtxInlineList w ctx (foldCtxInlineList w ctx acc l.content.toList) c.toList
      | none => foldCtxInlineList w ctx acc l.content.toList) rest

/-- `foldCtxInline` over a laid-out paragraph's lines, in reading order. -/
public def foldCtxLaidLines (w : CtxFold γ α) (ctx : γ) (acc : α) : List LaidLine → α
  | [] => acc
  | l :: rest => foldCtxLaidLines w ctx (foldCtxInlineList w ctx acc l.content.toList) rest

/-- `foldCtxInline` over a reference list's items, entry by entry. -/
public def foldCtxBibItems (w : CtxFold γ α) (ctx : γ) (acc : α) : List BibItem → α
  | [] => acc
  | it :: rest => foldCtxBibItems w ctx (foldCtxInlineList w ctx acc it.content.toList) rest

/-- `foldCtxInline` over a table of contents' entries, entry by entry. -/
public def foldCtxContentsEntries (w : CtxFold γ α) (ctx : γ) (acc : α) :
    List ContentsEntry → α
  | [] => acc
  | e :: rest => foldCtxContentsEntries w ctx (foldCtxInlineList w ctx acc e.title.toList) rest

mutual

/-- The block face: `foldBlock`'s descent, with the context `openBlock`
returns in force over the node's content and `closeBlock` called after it. -/
@[expose] public def foldCtxBlock (w : CtxFold γ α) (ctx : γ) (acc : α) (b : Block) : α :=
  match b with
  | .para content =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxInlineList w r.2 r.1 content.toList) b
  | .equation number content =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx
      (foldCtxInlineList w r.2 (foldCtxInlineList w r.2 r.1 content.toList) number.toList) b
  | .section _ _ _ title =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxInlineList w r.2 r.1 title.toList) b
  | .list _ _ items =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockItems w r.2 r.1 items.toList) b
  | .center body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .ragged _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .quote _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .lines ls =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxLaidLines w r.2 r.1 ls.toList) b
  | .abstract body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .titled _ title body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx
      (foldCtxBlockList w r.2 (foldCtxInlineList w r.2 r.1 title.toList) body.toList) b
  | .disclosure title _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx
      (foldCtxBlockList w r.2 (foldCtxInlineList w r.2 r.1 title.toList) body.toList) b
  | .role _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .link _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .spaced _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .columns cols =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockCols w r.2 r.1 cols.toList) b
  | .onSteps _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .altSteps _ firstPage otherPage =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx
      (foldCtxBlockList w r.2 (foldCtxBlockList w r.2 r.1 firstPage.toList)
        otherPage.toList) b
  | .only _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .nav _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .note body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBlockList w r.2 r.1 body.toList) b
  | .frame title _ _ _ body =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx
      (foldCtxBlockList w r.2 (foldCtxInlineList w r.2 r.1 title.toList) body.toList) b
  | .framefoot content =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxInlineList w r.2 r.1 content.toList) b
  | .float _ _ _ body caption =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx
      (foldCtxBlockList w r.2 (foldCtxInlineList w r.2 r.1 caption.toList) body.toList) b
  | .table _ _ _ rows _ _ =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxTableRows w r.2 r.1 rows.toList) b
  | .algorithm _ _ lines =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxAlgLines w r.2 r.1 lines.toList) b
  | .logo content =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxInlineList w r.2 r.1 content.toList) b
  | .bibliography _ _ items =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxBibItems w r.2 r.1 items.toList) b
  | .contents _ entries =>
    let r := w.openBlock ctx acc b
    w.closeBlock ctx (foldCtxContentsEntries w r.2 r.1 entries.toList) b
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ =>
    w.closeBlock ctx (w.openBlock ctx acc b).1 b

public def foldCtxBlockList (w : CtxFold γ α) (ctx : γ) (acc : α) : List Block → α
  | [] => acc
  | b :: rest => foldCtxBlockList w ctx (foldCtxBlock w ctx acc b) rest

public def foldCtxBlockItems (w : CtxFold γ α) (ctx : γ) (acc : α) : List (Array Block) → α
  | [] => acc
  | item :: rest => foldCtxBlockItems w ctx (foldCtxBlockList w ctx acc item.toList) rest

public def foldCtxBlockCols (w : CtxFold γ α) (ctx : γ) (acc : α) :
    List (BoxWidth × Array Block) → α
  | [] => acc
  | (_, body) :: rest => foldCtxBlockCols w ctx (foldCtxBlockList w ctx acc body.toList) rest

public def foldCtxTableRows (w : CtxFold γ α) (ctx : γ) (acc : α) :
    List (Array (Array Block)) → α
  | [] => acc
  | row :: rest => foldCtxTableRows w ctx (foldCtxBlockItems w ctx acc row.toList) rest

end

public def foldCtxBlocks (w : CtxFold γ α) (ctx : γ) (acc : α) (xs : Array Block) : α :=
  foldCtxBlockList w ctx acc xs.toList

/-- The leaf fold as a context walk: nothing descends, nothing happens on
the way out. -/
public def CtxFold.ofFold (fb : α → Block → α) (fi : α → Inline → α) : CtxFold Unit α where
  openBlock := fun _ acc b => (fb acc b, ())
  closeBlock := fun _ acc _ => acc
  openInline := fun _ acc x => (fi acc x, ())
  closeInline := fun _ acc _ => acc

@[simp] public theorem CtxFold.ofFold_openBlock (fb : α → Block → α) (fi : α → Inline → α)
    (u : Unit) (acc : α) (b : Block) :
    (CtxFold.ofFold fb fi).openBlock u acc b = (fb acc b, ()) := by rfl

@[simp] public theorem CtxFold.ofFold_closeBlock (fb : α → Block → α) (fi : α → Inline → α)
    (u : Unit) (acc : α) (b : Block) : (CtxFold.ofFold fb fi).closeBlock u acc b = acc := by rfl

@[simp] public theorem CtxFold.ofFold_openInline (fb : α → Block → α) (fi : α → Inline → α)
    (u : Unit) (acc : α) (x : Inline) :
    (CtxFold.ofFold fb fi).openInline u acc x = (fi acc x, ()) := by rfl

@[simp] public theorem CtxFold.ofFold_closeInline (fb : α → Block → α) (fi : α → Inline → α)
    (u : Unit) (acc : α) (x : Inline) :
    (CtxFold.ofFold fb fi).closeInline u acc x = acc := by rfl

mutual

public theorem foldCtxInline_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (x : Inline) : foldCtxInline (CtxFold.ofFold fb fi) () acc x = foldInline fi acc x := by
  match x with
  | .styled _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .colored _ _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .located _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .role _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .link _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .decorated kind body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .boxed b body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .onSteps _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .altSteps _ firstPage otherPage =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    rw [foldCtxInlineList_covers fb fi _ firstPage.toList,
      foldCtxInlineList_covers fb fi _ otherPage.toList]
  | .footnote _ body =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ body.toList
  | .cited _ _ ink =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]
    exact foldCtxInlineList_covers fb fi _ ink.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
    simp only [foldCtxInline, foldInline, CtxFold.ofFold_openInline,
      CtxFold.ofFold_closeInline]

public theorem foldCtxInlineList_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (xs : List Inline) :
    foldCtxInlineList (CtxFold.ofFold fb fi) () acc xs = foldInlineList fi acc xs := by
  match xs with
  | [] => rfl
  | x :: rest =>
    rw [foldCtxInlineList, foldInlineList, foldCtxInline_covers,
      foldCtxInlineList_covers fb fi _ rest]

end

public theorem foldCtxBibItems_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (items : List BibItem) :
    foldCtxBibItems (CtxFold.ofFold fb fi) () acc items = foldBibItems fi acc items := by
  induction items generalizing acc with
  | nil => rfl
  | cons it rest ih => rw [foldCtxBibItems, foldBibItems, foldCtxInlineList_covers, ih]

public theorem foldCtxContentsEntries_covers (fb : α → Block → α) (fi : α → Inline → α)
    (acc : α) (entries : List ContentsEntry) :
    foldCtxContentsEntries (CtxFold.ofFold fb fi) () acc entries =
      foldContentsEntries fi acc entries := by
  induction entries generalizing acc with
  | nil => rfl
  | cons e rest ih => rw [foldCtxContentsEntries, foldContentsEntries, foldCtxInlineList_covers, ih]

public theorem foldCtxAlgLines_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (lines : List AlgLine) :
    foldCtxAlgLines (CtxFold.ofFold fb fi) () acc lines = foldAlgLines fi acc lines := by
  induction lines generalizing acc with
  | nil => rfl
  | cons l rest ih =>
    rw [foldCtxAlgLines, foldAlgLines]
    cases l.comment with
    | none => simp only [foldCtxInlineList_covers, ih]
    | some c => simp only [foldCtxInlineList_covers, ih]

public theorem foldCtxLaidLines_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (lines : List LaidLine) :
    foldCtxLaidLines (CtxFold.ofFold fb fi) () acc lines = foldLaidLines fi acc lines := by
  induction lines generalizing acc with
  | nil => rfl
  | cons l rest ih => rw [foldCtxLaidLines, foldLaidLines, foldCtxInlineList_covers, ih]

mutual

public theorem foldCtxBlock_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (b : Block) : foldCtxBlock (CtxFold.ofFold fb fi) () acc b = foldBlock fb fi acc b := by
  match b with
  | .para content =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxInlineList_covers fb fi _ content.toList
  | .equation number content =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    rw [foldCtxInlineList_covers fb fi _ content.toList,
      foldCtxInlineList_covers fb fi _ number.toList]
  | .section _ _ _ title =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxInlineList_covers fb fi _ title.toList
  | .list _ _ items =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockItems_covers fb fi _ items.toList
  | .center body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .ragged _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .quote _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .lines ls =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxLaidLines_covers fb fi _ ls.toList
  | .abstract body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .titled _ title body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    rw [foldCtxInlineList_covers fb fi _ title.toList,
      foldCtxBlockList_covers fb fi _ body.toList]
  | .disclosure title _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    rw [foldCtxInlineList_covers fb fi _ title.toList,
      foldCtxBlockList_covers fb fi _ body.toList]
  | .role _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .link _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .spaced _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .columns cols =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockCols_covers fb fi _ cols.toList
  | .onSteps _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .altSteps _ firstPage otherPage =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    rw [foldCtxBlockList_covers fb fi _ firstPage.toList,
      foldCtxBlockList_covers fb fi _ otherPage.toList]
  | .only _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .nav _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .note body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBlockList_covers fb fi _ body.toList
  | .frame title _ _ _ body =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    rw [foldCtxInlineList_covers fb fi _ title.toList,
      foldCtxBlockList_covers fb fi _ body.toList]
  | .framefoot content =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxInlineList_covers fb fi _ content.toList
  | .float _ _ _ body caption =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    rw [foldCtxInlineList_covers fb fi _ caption.toList,
      foldCtxBlockList_covers fb fi _ body.toList]
  | .table _ _ _ rows _ _ =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxTableRows_covers fb fi _ rows.toList
  | .algorithm _ _ lines =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxAlgLines_covers fb fi _ lines.toList
  | .logo content =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxInlineList_covers fb fi _ content.toList
  | .bibliography _ _ items =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxBibItems_covers fb fi _ items.toList
  | .contents _ entries =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]
    exact foldCtxContentsEntries_covers fb fi _ entries.toList
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ =>
    simp only [foldCtxBlock, foldBlock, CtxFold.ofFold_openBlock,
      CtxFold.ofFold_closeBlock]

public theorem foldCtxBlockList_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (bs : List Block) :
    foldCtxBlockList (CtxFold.ofFold fb fi) () acc bs = foldBlockList fb fi acc bs := by
  match bs with
  | [] => rfl
  | b :: rest =>
    rw [foldCtxBlockList, foldBlockList, foldCtxBlock_covers,
      foldCtxBlockList_covers fb fi _ rest]

public theorem foldCtxBlockItems_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (items : List (Array Block)) :
    foldCtxBlockItems (CtxFold.ofFold fb fi) () acc items = foldBlockItems fb fi acc items := by
  match items with
  | [] => rfl
  | item :: rest =>
    rw [foldCtxBlockItems, foldBlockItems, foldCtxBlockList_covers,
      foldCtxBlockItems_covers fb fi _ rest]

public theorem foldCtxBlockCols_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (cols : List (BoxWidth × Array Block)) :
    foldCtxBlockCols (CtxFold.ofFold fb fi) () acc cols = foldBlockCols fb fi acc cols := by
  match cols with
  | [] => rfl
  | (_, body) :: rest =>
    rw [foldCtxBlockCols, foldBlockCols, foldCtxBlockList_covers,
      foldCtxBlockCols_covers fb fi _ rest]

public theorem foldCtxTableRows_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (rows : List (Array (Array Block))) :
    foldCtxTableRows (CtxFold.ofFold fb fi) () acc rows = foldTableRows fb fi acc rows := by
  match rows with
  | [] => rfl
  | row :: rest =>
    rw [foldCtxTableRows, foldTableRows, foldCtxBlockItems_covers,
      foldCtxTableRows_covers fb fi _ rest]

end

public theorem foldCtxBlocks_covers (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (xs : Array Block) :
    foldCtxBlocks (CtxFold.ofFold fb fi) () acc xs = foldBlocks fb fi acc xs :=
  foldCtxBlockList_covers fb fi acc xs.toList

@[expose] public def anyInline (p : Inline → Bool) (xs : Array Inline) : Bool :=
  foldInlines (fun b x => b || p x) false xs

/-- An inline that emits an HTML anchor now or after reference and citation resolution. -/
public def Inline.anchorBearing : Inline → Bool
  | .link _ _ | .ref _ _ _ _ | .cite _ _ | .cited _ _ _ | .footnote _ _ => true
  | .text _ | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _
  | .located _ _ | .role _ _ | .decorated _ _ | .boxed _ _ | .fill | .hspace _ _ | .rule _ _ _
  | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ | .onSteps _ _ | .altSteps _ _ _
  | .image _ _ _ | .icon _ _ | .label _ => false

/-- Whether a block body already contains an anchor-bearing construct. -/
public def hasBlockAnchor (xs : Array Block) : Bool :=
  foldBlocks (fun found b => found || (b matches .link _ _))
    (fun found x => found || x.anchorBearing) false xs

/-- Whether an inline leaf bears text ink a link affordance should mark. -/
public def Inline.bearsLinkText : Inline → Bool
  | .text _ | .math _ _ | .formula _ _ _ | .ref _ _ _ _ | .cite _ _
  | .icon _ _ | .pageNumber | .pageCount => true
  | .image _ _ _ | .label _ | .fill | .hspace _ _ | .rule _ _ _
  | .strut _ | .italicCorr _ | .linebreak _
  | .styled _ _ | .colored _ _ _ | .located _ _ | .role _ _ | .link _ _ | .decorated _ _ | .boxed _ _
  | .onSteps _ _ | .altSteps _ _ _ | .footnote _ _ | .cited _ _ _ => false

/-- One link-body leaf given its kind's affordance: a text-bearing leaf is
underlined and set in the kind's declared ink. -/
public def Styles.linkLeafAfford (s : Styles) (kind : String) (x : Inline) : Inline :=
  if x.bearsLinkText then
    match (s.find? kind).bind (·.color) with
    | some (c, n) => .colored c n #[.decorated .underline #[x]]
    | none => .decorated .underline #[x]
  else x

public theorem Styles.linkLeafAfford_afford (s : Styles) (kind : String) (x : Inline)
    (h : x.bearsLinkText = true) :
    s.linkLeafAfford kind x
      = (match (s.find? kind).bind (·.color) with
         | some (c, n) => .colored c n #[.decorated .underline #[x]]
         | none => .decorated .underline #[x]) := by
  simp only [Styles.linkLeafAfford, h, ite_true]
  rfl

public theorem Styles.linkLeafAfford_id (s : Styles) (kind : String) (x : Inline)
    (h : x.bearsLinkText = false) : s.linkLeafAfford kind x = x := by
  simp [Styles.linkLeafAfford, h]

public theorem Styles.linkLeafAfford_text (s : Styles) (kind : String) (x : Inline) :
    plainTextOne (s.linkLeafAfford kind x) = plainTextOne x := by
  rw [Styles.linkLeafAfford]
  split
  · split <;> simp [plainTextOne, plainTextList]
  · rfl


/-- The accessible reading of a block link, from the generic fold that censuses the block tree. -/
private def blockLinkInlineReading (acc : String) (x : Inline) : String :=
  match x with
  | .styled _ _ | .colored _ _ _ | .located _ _ | .role _ _ | .link _ _ | .decorated _ _ | .boxed _ _
  | .onSteps _ _ | .altSteps _ _ _ | .footnote _ _ | .cited _ _ _ => acc
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _
  | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ => String.append acc (plainTextOne x)

private def blockLinkBlockReading (acc : String) (b : Block) : String :=
  match b with
  | .verbatim _ content spec =>
    let caption := match spec.caption with
      | some (_, cap) => plainText cap
      | none => ""
    String.append (String.append acc caption) content
  | .picture pic => String.append acc pic.alternative.text
  | .bibliography _ _ _ | .contents _ _
  | .para _ | .section _ _ _ _ | .list _ _ _ | .center _ | .ragged _ _ | .spaced _ _
  | .role _ _ | .link _ _ | .quote _ _ | .lines _ | .abstract _ | .titled _ _ _ | .disclosure _ _ _ | .equation _ _
  | .algorithm _ _ _ | .columns _ | .onSteps _ _ | .altSteps _ _ _ | .note _ | .only _ _
  | .nav _ _ | .logo _ | .pagebreak | .frame _ _ _ _ _ | .framefoot _ | .setPalette _
  | .setTokens _ | .rule _ _ _ | .table _ _ _ _ _ _ | .float _ _ _ _ _ => acc

/-- What assistive technology can name a block link from. -/
public def blockLinkReading (body : Array Block) : String :=
  foldBlocks blockLinkBlockReading blockLinkInlineReading "" body


/-- Unicode `White_Space` (PropList.txt): 0009–000D, 0020, 0085, 00A0, 1680,
2000–200A, 2028, 2029, 202F, 205F, 3000. -/
public def isWhiteSpaceUni (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || n == 0x20 || n == 0x85 || n == 0xA0 ||
  n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
  n == 0x202F || n == 0x205F || n == 0x3000

/-- One character of an anchor: ASCII letters and digits lowercased, other
non-ASCII scalars kept, `none` a separator. -/
private def slugCharKeep (k : Char) : Option Char :=
  if isWhiteSpaceUni k then none
  else if k.isAlpha || k.isDigit then some k
  else if 0x80 ≤ k.toNat then some k
  else none

private def slugChar (c : Char) : Option Char :=
  slugCharKeep (if c.isAlpha || c.isDigit then c.toLower else c)

/-- The slug walk: separators collapse to one hyphen, emitted only between kept characters. -/
private def slugGo (acc : Array Char) (sep : Bool) : List Char → Array Char
  | [] => acc
  | c :: rest =>
    match slugChar c with
    | some k =>
      if sep && !acc.isEmpty then slugGo ((acc.push '-').push k) false rest
      else slugGo (acc.push k) false rest
    | none => slugGo acc true rest

/-- An anchor id from a title's own text. -/
public def slug (title : Array Inline) : String :=
  String.ofList (slugGo #[] false (firstPageText title).toList).toList

/-- The anchor a top-level section claims: its title's slug or `section`, the first form of it no
earlier section holds, and the earlier holder of the base whose title differs. -/
public structure SectionAnchor where
  base : String
  id : String
  clash : Option String
  deriving Repr, BEq

private theorem slugCharKeep_not_whitespace (k k' : Char) (h : slugCharKeep k = some k') :
    isWhiteSpaceUni k' = false := by
  unfold slugCharKeep at h
  (repeat' split at h) <;> simp_all

private theorem slugChar_not_whitespace (c k : Char) (h : slugChar c = some k) :
    isWhiteSpaceUni k = false :=
  slugCharKeep_not_whitespace _ _ h

private theorem slugGo_no_whitespace (l : List Char) (acc : Array Char) (sep : Bool)
    (hacc : ∀ c ∈ acc.toList, isWhiteSpaceUni c = false) :
    ∀ c ∈ (slugGo acc sep l).toList, isWhiteSpaceUni c = false := by
  induction l generalizing acc sep with
  | nil => simpa [slugGo] using hacc
  | cons c rest ih =>
    simp only [slugGo]
    split
    · next k hk =>
      have hkw := slugChar_not_whitespace c k hk
      split
      · apply ih
        intro d hd
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hd
        rcases hd with (hd | hd) | hd
        · exact hacc d hd
        · subst hd; decide
        · subst hd; exact hkw
      · apply ih
        intro d hd
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hd
        rcases hd with hd | hd
        · exact hacc d hd
        · subst hd; exact hkw
    · exact ih acc true hacc

public theorem slug_no_whitespace (title : Array Inline) :
    ∀ c ∈ (slug title).toList, isWhiteSpaceUni c = false := by
  intro c hc
  simp only [slug, String.toList_ofList] at hc
  exact slugGo_no_whitespace _ _ _ (by simp) c hc

public theorem slug_altSteps_exact (spec : OverlaySpec) (firstPage otherPage : Array Inline)
    (hs : spec.maxStep ≠ 0) (hw : (plainText firstPage).toList.any (!·.isWhitespace) = true) :
    slug #[.altSteps spec firstPage otherPage] = slug firstPage := by
  have hs' : (spec.maxStep == 0) = false := by simpa using hs
  simp only [slug, firstPageText, firstPageTextList, firstPageTextOne, hs', hw, Bool.false_or,
    Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- A title that is one alternation with a blank first-page group anchors by the other. -/
public theorem slug_altSteps_floor_exact (spec : OverlaySpec) (firstPage otherPage : Array Inline)
    (hb : (plainText firstPage).toList.any (!·.isWhitespace) = false)
    (hw : (plainText otherPage).toList.any (!·.isWhitespace) = true) :
    slug #[.altSteps spec firstPage otherPage] = slug otherPage := by
  simp only [slug, firstPageText, firstPageTextList, firstPageTextOne, hb, hw, Bool.not_false,
    Bool.not_true, Bool.true_and, Bool.or_true, ↓reduceIte]

mutual

/-- Every link of a navigation landmark's body, in document order, as (text,
target); notes and footnotes are never navigation, and a link is read
whole. -/
-- conserves: none — projects the links alone.
private def navLinkList (out : Array (String × String)) : List Block → Array (String × String)
  | [] => out
  | b :: rest => navLinkList (navLinkOne out b) rest

private def navLinkOne (out : Array (String × String)) : Block → Array (String × String)
  | .para content => navLinkInlineList out content.toList
  | .equation number content =>
    navLinkInlineList (navLinkInlineList out content.toList) number.toList
  | .section _ _ _ title => navLinkInlineList out title.toList
  | .verbatim _ _ _ => out
  | .logo _ => out
  | .framefoot _ => out
  | .setPalette _ => out
  | .setTokens _ => out
  | .pagebreak => out
  | .rule _ _ _ => out
  | .picture _ => out
  | .list _ _ items => navLinkItems out items.toList
  | .center body => navLinkList out body.toList
  | .ragged _ body => navLinkList out body.toList
  | .quote _ body => navLinkList out body.toList
  | .lines ls => navLinkLaid out ls.toList
  | .abstract body => navLinkList out body.toList
  | .titled _ title body => navLinkList (navLinkInlineList out title.toList) body.toList
  | .disclosure title _ body => navLinkList (navLinkInlineList out title.toList) body.toList
  | .role _ body => navLinkList out body.toList
  | .link target body => out.push (blockLinkReading body, target)
  | .spaced _ body => navLinkList out body.toList
  | .columns cols => navLinkColumns out cols.toList
  | .onSteps _ body => navLinkList out body.toList
  | .altSteps _ firstPage otherPage =>
    navLinkList (navLinkList out firstPage.toList) otherPage.toList
  | .note _ => out
  | .only _ body => navLinkList out body.toList
  | .nav _ body => navLinkList out body.toList
  | .frame title _ _ _ body => navLinkList (navLinkInlineList out title.toList) body.toList
  | .table _ _ _ rows _ _ => navLinkRows out rows.toList
  | .float _ _ _ body caption => navLinkInlineList (navLinkList out body.toList) caption.toList
  | .algorithm _ _ lines => navLinkAlgLines out lines.toList
  | .bibliography _ _ items => navLinkBibItems out items.toList
  | .contents _ _ => out

private def navLinkBibItems (out : Array (String × String)) :
    List BibItem → Array (String × String)
  | [] => out
  | item :: rest => navLinkBibItems (navLinkInlineList out item.content.toList) rest

private def navLinkRows (out : Array (String × String)) :
    List (Array (Array Block)) → Array (String × String)
  | [] => out
  | row :: rest => navLinkRows (navLinkItems out row.toList) rest

private def navLinkItems (out : Array (String × String)) :
    List (Array Block) → Array (String × String)
  | [] => out
  | item :: rest => navLinkItems (navLinkList out item.toList) rest

private def navLinkColumns (out : Array (String × String)) :
    List (BoxWidth × Array Block) → Array (String × String)
  | [] => out
  | (_, body) :: rest => navLinkColumns (navLinkList out body.toList) rest

private def navLinkAlgLines (out : Array (String × String)) :
    List AlgLine → Array (String × String)
  | [] => out
  | l :: rest =>
    navLinkAlgLines (match l.comment with
      | some c => navLinkInlineList (navLinkInlineList out l.content.toList) c.toList
      | none => navLinkInlineList out l.content.toList) rest

private def navLinkLaid (out : Array (String × String)) :
    List LaidLine → Array (String × String)
  | [] => out
  | l :: rest => navLinkLaid (navLinkInlineList out l.content.toList) rest

private def navLinkInlineList (out : Array (String × String)) :
    List Inline → Array (String × String)
  | [] => out
  | x :: rest => navLinkInlineList (navLinkInline out x) rest

private def navLinkInline (out : Array (String × String)) : Inline → Array (String × String)
  | .link url body => out.push (plainTextList body.toList, url)
  | .styled _ body => navLinkInlineList out body.toList
  | .colored _ _ body => navLinkInlineList out body.toList
  | .located _ body => navLinkInlineList out body.toList
  | .role _ body => navLinkInlineList out body.toList
  | .decorated _ body | .boxed _ body => navLinkInlineList out body.toList
  | .onSteps _ body => navLinkInlineList out body.toList
  | .altSteps _ firstPage otherPage =>
    navLinkInlineList (navLinkInlineList out firstPage.toList) otherPage.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .cited _ _ _
  | .footnote _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ => out

end

public def navLinks (body : Array Block) : Array (String × String) :=
  navLinkList #[] body.toList

/-- An overlay range for the dump: a single interval as a step's, a union by
every declared interval, and `invisible` where its content is so off its steps. -/
private def dumpOverlayRange (kind : String) (spec : OverlaySpec) : String :=
  kind ++ " " ++ String.intercalate "," (spec.ranges.map fun (n, last) =>
    match last with
    | some u => s!"{n}-{u}"
    | none => toString n) ++ (if spec.invisible then " invisible" else "")

/-- A box length for goldens: its literals as `dumpGlue` spells them, its references by name. -/
private def dumpBoxLength : Affine BoxMeasure → String
  | .lit g => dumpGlue g
  | .ref (.page m) => m.label
  | .ref .height => "\\height"
  | .ref .depth => "\\depth"
  | .ref .width => "\\width"
  | .ref .totalHeight => "\\totalheight"
  | .scale n d e => s!"{n}/{d}*({dumpBoxLength e})"
  | .add a b => s!"{dumpBoxLength a}+{dumpBoxLength b}"
  | .sub a b => s!"{dumpBoxLength a}-({dumpBoxLength b})"

/-- A box for goldens: its raise, declared extents, paints and padding. -/
public def InlineBox.dump (b : InlineBox) : String :=
  let paint (c : Color) (n : Option ColorRef) : String :=
    c.hex ++ (match n with | some n => s!"({n.key})" | none => "")
  String.intercalate " " (
    [s!"raise {dumpBoxLength b.raise}"] ++
    (b.height.map fun h => s!"height {dumpBoxLength h}").toList ++
    (b.depth.map fun d => s!"depth {dumpBoxLength d}").toList ++
    (b.ground.map fun (c, n) => s!"ground {paint c n}").toList ++
    (b.frame.map fun f => match f with
      | .ink => "frame ink"
      | .color c n => s!"frame {paint c n}").toList ++
    (if b.ground.isSome || b.frame.isSome then [s!"pad {dumpGlue b.pad}"] else []) ++
    (if b.frame.isSome then [s!"rule {dumpGlue b.rule}"] else []))

mutual

/-- One line of a formula's structure for the IR dump: every atom's class, scalar and scripts. -/
private def dumpMathItem (acc : String) (x : Math.MItem) : String :=
  match x with
  | .atom cls nuc sup sub lim =>
    let acc := acc ++ s!"{cls.label}:" ++ (if lim then "lim:" else "")
    dumpMathSub (dumpMathSup (dumpMathNucleus acc nuc) sup) sub
  | .space mu => acc ++ s!"mu:{mu}"
  | .ink c n => acc ++ s!"ink:{c.hex}"
      ++ (match n with | some n => s!"({n.key})" | none => "")

private def dumpMathNucleus (acc : String) (n : Math.MNucleus) : String :=
  match n with
  | .sym c => acc.push c
  | .styled sty c => ((acc ++ s!"styled:{sty.mathvariant}\{").push c).push '}'
  | .word s => acc ++ s.quote
  | .list body => (dumpMathList (acc.push '{') body).push '}'
  | .alpha a _ body => (dumpMathList (acc ++ s!"alpha:{a.name}\{") body).push '}'
  | .frac spec num den =>
    let name (c : Option Char) : String := match c with
      | some c => String.ofList [c]
      | none => "."
    let head := if spec == {} then "frac{" else
      s!"frac[{name spec.left}{name spec.right}" ++
        (match spec.rule with | some t => s!" rule:{t.toPtString}pt" | none => "") ++
        (match spec.style with | some s => s!" style:{s.rank}" | none => "") ++ "]{"
    ((dumpMathList (acc ++ head) num ++ "}{" |> fun a =>
      dumpMathList a den)).push '}'
  | .rad deg body =>
    let acc := match deg with
      | .nil => acc ++ "sqrt"
      | _ => (dumpMathList (acc ++ "sqrt[") deg) ++ "]"
    (dumpMathList (acc.push '{') body).push '}'
  | .delim l r body =>
    let name (c : Option Char) : String := match c with
      | some c => String.ofList [c]
      | none => "."
    (dumpMathList (acc ++ s!"left{name l}\{") body) ++ s!"}right{name r}"
  | .big d step =>
    acc ++ s!"big{step}:" ++ (match d with | some c => String.ofList [c] | none => ".")
  | .accent mark stretch body =>
    -- The combining mark by scalar value: pushed bare it would combine with the dump's text.
    let tag := if stretch then "acc*" else "acc"
    (dumpMathList (acc ++ s!"{tag}:{mark.toNat}\{") body).push '}'
  | .grid kind rows =>
    let tag := match kind with
      | .align => "align"
      | .aligned t => if t then "aligned:trail" else "aligned"
      | .gather => "gather"
      | .array cols s =>
        "array:" ++ String.join (cols.toList.map fun a => match a with
          | .left => "l"
          | .center => "c"
          | .right => "r") ++ (if s == 1000 then "" else s!"*{s}")
      | .small => "small"
    dumpMathRows (acc ++ tag ++ "[") rows ++ "]"
  | .cancel mark spec value body =>
    let tag := match mark with
      | .up => "cancel"
      | .down => "bcancel"
      | .cross => "xcancel"
      | .to => "cancelto"
    let size := match spec.size with
      | .same => " samesize"
      | .step => ""
      | .sup => " Smaller"
    let opts := (if spec.thick then " thick" else "") ++ (if spec.room then "" else " overlap")
      ++ size ++ (match spec.color with
        | some (c, _) => s!" {c.hex}"
        | none => "")
    let acc := (dumpMathList (acc ++ tag ++ (if opts.isEmpty then "" else s!"[{(opts.drop 1).toString}]") ++ "{")
      body).push '}'
    match value with
    | .nil => acc
    | _ => (dumpMathList (acc ++ "to{") value).push '}'

private def dumpMathRows (acc : String) (rs : Math.MRows) : String :=
  match rs with
  | .nil => acc
  | .cons r rest =>
    dumpMathRows (dumpMathRow (acc ++ "(") r ++ ")") rest

private def dumpMathRow (acc : String) (r : Math.MRow) : String :=
  match r with
  | .nil => acc
  | .cons cell rest =>
    dumpMathRow (dumpMathList (acc ++ "|") cell) rest

private def dumpMathSup (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => (dumpMathRest (dumpMathItem (acc ++ "^{") x) rest).push '}'

private def dumpMathSub (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => (dumpMathRest (dumpMathItem (acc ++ "_{") x) rest).push '}'

private def dumpMathList (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => dumpMathRest (dumpMathItem acc x) rest

private def dumpMathRest (acc : String) (l : Math.MList) : String :=
  match l with
  | .nil => acc
  | .cons x rest => dumpMathRest (dumpMathItem (acc ++ " ") x) rest

end

/-- A citation's dump line after its tag: the command, its notes, its keys. -/
private def dumpCiteHead (form : CiteForm) (keys : Array String) : String :=
  let note (tag s : String) := if s.isEmpty then "" else s!" {tag} {s.quote}"
  let named := keys.toList.map (·.quote)
  s!"{form.command}{if form.full then "*" else ""}{note "pre" form.pre}\
{note "post" form.post}{if named.isEmpty then "" else " " ++ String.intercalate " " named}"

mutual

private def dumpInlines (ind : String) (xs : Array Inline) : String :=
  dumpInlineList ind xs.toList

private def dumpInlineList (ind : String) (xs : List Inline) : String :=
  match xs with
  | [] => ""
  | x :: rest => dumpInline ind x ++ dumpInlineList ind rest

private def dumpInline (ind : String) (x : Inline) : String :=
  match x with
  | .text s => s!"{ind}text {s.quote}\n"
  | .math d src =>
    let kind := if d then "display" else "inline"
    s!"{ind}math {kind} {src.quote}\n"
  | .formula d src body =>
    let kind := if d then "display" else "inline"
    s!"{ind}formula {kind} {src.quote}\n{ind}  {dumpMathList "" body}\n"
  | .styled st body => s!"{ind}styled {st.label}\n" ++ dumpInlines (ind ++ "  ") body
  | .colored c name body =>
    let tag := match name with
      | some n => s!"{n.key} {c.hex}"
      | none => c.hex
    s!"{ind}color {tag}\n" ++ dumpInlines (ind ++ "  ") body
  | .located _ body => dumpInlines ind body
  | .role n body =>
    s!"{ind}role {n}\n" ++ dumpInlines (ind ++ "  ") body
  | .link url body =>
    s!"{ind}link {url.quote}\n" ++ dumpInlines (ind ++ "  ") body
  | .decorated kind body =>
    let label := match kind with
      | .underline => "underline"
      | .lineThrough => "line-through"
      | .highlight c name =>
        let hex := c.hex
        match name with
        | some n => s!"highlight {n.key} {hex}"
        | none => s!"highlight {hex}"
    s!"{ind}decoration {label}\n" ++ dumpInlines (ind ++ "  ") body
  | .boxed b body => s!"{ind}box {b.dump}\n" ++ dumpInlines (ind ++ "  ") body
  | .onSteps spec body =>
    s!"{ind}{dumpOverlayRange "step" spec}\n" ++ dumpInlines (ind ++ "  ") body
  | .altSteps spec firstPage otherPage =>
    s!"{ind}{dumpOverlayRange "alt" spec}\n" ++
    s!"{ind}  first page\n" ++ dumpInlines (ind ++ "    ") firstPage ++
    s!"{ind}  other page\n" ++ dumpInlines (ind ++ "    ") otherPage
  | .fill => s!"{ind}fill\n"
  | .hspace g keep =>
    s!"{ind}hspace{if keep then "*" else ""} {Track.css (.affine g)}\n"
  | .rule w h r =>
    s!"{ind}rule {Track.css (.affine w)} × {Track.css (.affine h)} raise {Track.css (.affine r)}\n"
  | .strut _ => s!"{ind}strut\n"
  | .italicCorr maybe => s!"{ind}italicCorr{if maybe then " maybe" else ""}\n"
  | .label key => s!"{ind}label {key.quote}\n"
  | .ref key form text target =>
    let form := form.spelling
    let tgt := match target with
      | some a => s!" -> #{a}"
      | none => ""
    s!"{ind}{form} {key.quote} shows {text.quote}{tgt}\n"
  | .pageNumber => s!"{ind}pagenumber\n"
  | .pageCount => s!"{ind}pagecount\n"
  | .image src size alt =>
    let dim (label : String) (l : Image.Len) : String :=
      let v := match l.value with
        | .lit g => g.width.fixed.toPtString ++ "pt"
        | .scale n d (.ref .textHeight) => s!"{n * 1000 / d}/1000th"
        | .scale n d (.ref _) => s!"{n * 1000 / d}/1000tw"
        | .ref .textHeight => "1000/1000th"
        | .ref _ => "1000/1000tw"
        | e => Track.css (.affine e)
      s!" {label} {v}"
    let parts :=
      (match size.width with | some l => dim "width" l | none => "") ++
      (match size.height with | some l => dim "height" l | none => "") ++
      (if size.scaleNum != 1 || size.scaleDen != 1 then
        s!" scale {size.scaleNum}/{size.scaleDen}" else "") ++
      (if size.keepAspect then " keepaspect" else "") ++ alt.dumpSuffix
    s!"{ind}image {src.quote}{parts}\n"
  | .icon c label =>
    s!"{ind}icon {(String.ofList [c]).quote} label {label.quote}\n"
  | .cite form keys => s!"{ind}cite {dumpCiteHead form keys}\n"
  | .cited form keys ink =>
    s!"{ind}cited {dumpCiteHead form keys}\n" ++ dumpInlines (ind ++ "  ") ink
  | .footnote num body =>
    let tag := match num with
      | some n => s!" {n}"
      | none => ""
    s!"{ind}footnote{tag}\n" ++ dumpInlines (ind ++ "  ") body
  | .linebreak extra =>
    if extra == ({} : SymGlue) then s!"{ind}linebreak\n"
    else s!"{ind}linebreak {dumpGlue extra}\n"

end

/-- One column spec for the dump: the align letter, then the declared width;
`~` after the letter marks a ragged column. -/
private def dumpColSpec (c : ColSpec) : String :=
  let al := match c.align with
    | .left => "l"
    | .center => "c"
    | .right => "r"
  let al := if c.ragged then al ++ "~" else al
  let al := if c.narrows then al ++ "<" else al
  match c.width with
  | .natural => al
  | .sized e =>
    let width := match e with
      | .scale n d (.ref _) => s!"{n * 1000 / d}/1000"
      | .ref _ => "1000/1000"
      | .lit g => g.width.fixed.toPtString ++ "pt"
      | other => Track.css (.affine other)
    s!"{al}:{width}"
  | .flex target => s!"{al}:flex:{target.css}"

private def dumpTableRule (r : TableRule) : String :=
  match r with
  | .top => "top"
  | .mid => "mid"
  | .bottom => "bottom"
  | .cmid a b tl tr =>
    let trim := (if tl then "l" else "") ++ (if tr then "r" else "")
    s!"cmid {a}-{b}{if trim.isEmpty then "" else s!"({trim})"}"
  | .gap g => s!"gap {dumpGlue g}"
  | .measured => "measured"

mutual

public def dumpBlocks (ind : String) (xs : Array Block) : String :=
  dumpBlockList ind xs.toList

private def dumpBlockList (ind : String) (xs : List Block) : String :=
  match xs with
  | [] => ""
  | b :: rest => dumpBlock ind b ++ dumpBlockList ind rest

private def dumpItems (ind : String) (items : List (Array Block)) : String :=
  match items with
  | [] => ""
  | item :: rest =>
    s!"{ind}item\n" ++ dumpBlocks (ind ++ "  ") item ++ dumpItems ind rest

private def dumpColumns (ind : String) (cols : List (BoxWidth × Array Block)) : String :=
  match cols with
  | [] => ""
  | (w, body) :: rest =>
    let pos := match w.pos with
      | .top => ""
      | .first => " [t]"
      | .center => " [c]"
      | .last => " [b]"
    let pos := pos ++ match w.box with
      | some b => s!" in {b.dump}"
      | none => ""
    let self := (match w.size with
      | .sized (.scale n d (.ref _)) =>
        s!"{ind}column {n * 1000 / d}/1000{pos}\n"
      | .sized (.ref _) => s!"{ind}column 1000/1000{pos}\n"
      | .sized (.lit g) => s!"{ind}column {g.width.fixed.toPtString}pt{pos}\n"
      | .sized e => s!"{ind}column {Track.css (.affine e)}{pos}\n"
      | .share => s!"{ind}column{pos}\n") ++ dumpBlocks (ind ++ "  ") body
    let tail := dumpColumns ind rest
    self ++ tail

private def dumpTableCells (ind : String) (acc : String) : List (Array Block) -> String
  | [] => acc
  | cell :: rest =>
    let inner := match cellLine? cell with
      | some xs => dumpInlines (ind ++ "  ") xs
      | none => dumpBlocks (ind ++ "  ") cell
    dumpTableCells ind (acc ++ s!"{ind}cell\n" ++ inner) rest

private def dumpTableRows (ind : String) (acc : String) :
    List (Array (Array Block)) -> String
  | [] => acc
  | row :: rest =>
    dumpTableRows ind (dumpTableCells (ind ++ "  ") (acc ++ s!"{ind}row\n") row.toList) rest

private def dumpBlock (ind : String) (b : Block) : String :=
  match b with
  | .para content => s!"{ind}para\n" ++ dumpInlines (ind ++ "  ") content
  | .equation number content =>
    (match number with
      | #[.text s] => s!"{ind}equation {s.quote}\n"
      | _ => s!"{ind}equation\n{ind}  number\n" ++ dumpInlines (ind ++ "    ") number) ++
    dumpInlines (ind ++ "  ") content
  | .section level starred num title =>
    let star := if starred then "*" else ""
    let n := match num with
      | some n => s!" number {n.quote}"
      | none => ""
    s!"{ind}section{star} {level}{n}\n" ++ dumpInlines (ind ++ "  ") title
  | .list ordered _ items =>
    let kind := if ordered then "ordered" else "unordered"
    s!"{ind}list {kind}\n" ++ dumpItems (ind ++ "  ") items.toList
  | .center body => s!"{ind}center\n" ++ dumpBlocks (ind ++ "  ") body
  | .ragged s body => s!"{ind}ragged {s.align}\n" ++ dumpBlocks (ind ++ "  ") body
  | .quote q body =>
    let kind := if q.kind == .quote then "" else " " ++ q.kind.name
    s!"{ind}quote{kind}\n" ++ dumpBlocks (ind ++ "  ") body
  | .lines ls => s!"{ind}lines\n" ++
    String.join (ls.toList.map fun l => s!"{ind}  line {l.depth}\n" ++ dumpInlines (ind ++ "    ") l.content)
  | .abstract body => s!"{ind}abstract\n" ++ dumpBlocks (ind ++ "  ") body
  | .titled kind title body =>
    s!"{ind}titled {kind.name}\n" ++
    (if title.isEmpty then ""
     else s!"{ind}  title\n" ++ dumpInlines (ind ++ "    ") title) ++
    dumpBlocks (ind ++ "  ") body
  | .disclosure summary expanded body =>
    s!"{ind}disclosure{if expanded then " open" else ""}\n" ++
    (if summary.isEmpty then ""
     else s!"{ind}  summary\n" ++ dumpInlines (ind ++ "    ") summary) ++
    dumpBlocks (ind ++ "  ") body
  | .role n body => s!"{ind}role {n}\n" ++ dumpBlocks (ind ++ "  ") body
  | .link target body =>
    s!"{ind}block-link {target.quote}\n" ++ dumpBlocks (ind ++ "  ") body
  | .columns cols => s!"{ind}columns\n" ++ dumpColumns (ind ++ "  ") cols.toList
  | .onSteps spec body =>
    s!"{ind}{dumpOverlayRange "step" spec}\n" ++ dumpBlocks (ind ++ "  ") body
  | .altSteps spec firstPage otherPage =>
    s!"{ind}{dumpOverlayRange "alt" spec}\n" ++
    s!"{ind}  first page\n" ++ dumpBlocks (ind ++ "    ") firstPage ++
    s!"{ind}  other page\n" ++ dumpBlocks (ind ++ "    ") otherPage
  | .note body => s!"{ind}note\n" ++ dumpBlocks (ind ++ "  ") body
  | .only targets body =>
    s!"{ind}only {String.intercalate "," targets.toList}\n" ++ dumpBlocks (ind ++ "  ") body
  | .nav spec body =>
    let label := match spec.label with
      | some l => s!" label {l.quote}"
      | none => ""
    let pin := match spec.pin with
      | some p =>
        s!" pin {if p.top then "top" else "bottom"} \
{if p.left then "left" else "right"} offset {dumpGlue p.offset}" ++
        (if p.reveal then
          match p.revealBy with
          | some g => s!" reveal {dumpGlue g}"
          | none => " reveal scroll"
        else "")
      | none => ""
    s!"{ind}nav{label}{pin}\n" ++ dumpBlocks (ind ++ "  ") body
  | .logo content =>
    if content.isEmpty then s!"{ind}logo clear\n"
    else s!"{ind}logo\n" ++ dumpInlines (ind ++ "  ") content
  | .spaced before body =>
    s!"{ind}block before {dumpSourcedGlue before}\n" ++ dumpBlocks (ind ++ "  ") body
  | .verbatim covered s spec =>
    s!"{ind}verbatim{if covered.isSome then " covered" else ""}\
{if spec.numbers then " numbers" else ""}" ++
    (match spec.caption with
      | some (n, _) => s!" listing {n}"
      | none => "") ++
    (match spec.langToken with
      | some l => s!" language {l}"
      | none => "") ++
    (match spec.ground with
      | some (c, ref) => " ground " ++ ((ref.map (·.key ++ " ")).getD "") ++
          c.hex
      | none => "") ++ "\n" ++
    (match spec.caption with
      | some (_, cap) => s!"{ind}  caption\n" ++ dumpInlines (ind ++ "    ") cap
      | none => "") ++
    String.join ((verbatimLines s).toList.map
      fun l => s!"{ind}  {l.quote}\n")
  | .algorithm numbered semis lines =>
    s!"{ind}algorithm{if numbered then " numbered" else ""}{if semis then "" else " nosemi"}\n" ++
    String.join (lines.toList.map fun l =>
      s!"{ind}  line {l.depth} {l.kind.name}\n" ++
      dumpInlines (ind ++ "    ") l.content ++
      (match l.comment with
       | some c => s!"{ind}    comment\n" ++ dumpInlines (ind ++ "      ") c
       | none => ""))
  | .frame title standout valign _ body =>
    let va := match valign with
      | .center => ""
      | .top => " top"
      | .bottom => " bottom"
      | .golden => " golden"
    s!"{ind}frame{if standout then " standout" else ""}{va}\n" ++
    (if title.isEmpty then ""
     else s!"{ind}  title\n" ++ dumpInlines (ind ++ "    ") title) ++
    dumpBlocks (ind ++ "  ") body
  | .framefoot content =>
    s!"{ind}framefoot\n" ++ dumpInlines (ind ++ "  ") content
  | .setPalette pal =>
    s!"{ind}setPalette\n" ++
    String.join (pal.entries.toList.map fun (n, c) =>
      s!"{ind}  {n.key} = {c.hex}\n")
  | .setTokens tk =>
    s!"{ind}setTokens\n" ++
    String.join (tk.entries.toList.map fun (n, g) =>
      s!"{ind}  {n} = {dumpGlue g}\n")
  | .pagebreak => s!"{ind}pagebreak\n"
  | .rule color name thickness =>
    let nm := match name with
      | some n => s!" {n.key}"
      | none => s!" {color.hex}"
    s!"{ind}rule{nm} {dumpSourcedGlue thickness}\n"
  | .picture pic =>
    let boxS := fun (b : Pic.Box) =>
      s!"{b.1.1.toBpString} {b.1.2.toBpString} {b.2.1.toBpString} {b.2.2.toBpString}"
    s!"{ind}picture {pic.shapes.size} shapes{pic.alt.dumpSuffix}\n" ++
    (match pic.declared with
      | some b => s!"{ind}  declared {boxS b}\n"
      | none => "") ++
    (match pic.baseline with
      | some y => s!"{ind}  baseline {y.toBpString}\n"
      | none => "") ++
    String.join (pic.borders.toList.map fun b => s!"{ind}  border {boxS b}\n") ++
    String.join (pic.shapes.toList.map fun s =>
      match s with
      | .ink n => Pic.dumpNode (ind ++ "  ") "" n
      | .label x y content c sc al =>
        let alS := match al with
          | .center => ""
          | .west => " west"
          | .east => " east"
          | .south => " south"
          | .north => " north"
        s!"{ind}  label {x.toBpString} {y.toBpString} \
{c.hex} {sc}{alS}\n" ++
        dumpInlines (ind ++ "    ") content)
  | .table cols padL padR rows rules spans =>
    let spec := String.intercalate "," (cols.toList.map dumpColSpec)
    let pads := (if padL then "" else "@{}") ++ spec ++ (if padR then "" else "@{}")
    let ruleLines := String.join (rules.toList.map fun (i, r) =>
      s!"{ind}  rule {i} {dumpTableRule r}\n")
    let spanLines := String.join (spans.toList.map fun sp =>
      s!"{ind}  span {sp.row}:{sp.col} x{sp.n} {dumpColSpec sp.spec}\n")
    dumpTableRows (ind ++ "  ") (s!"{ind}table {pads}\n" ++ ruleLines ++ spanLines) rows.toList
  | .float kind num capAbove body caption =>
    let k := match kind with
      | .figure => "figure"
      | .table => "table"
      | .sub => "sub"
      | .algorithm => "algorithm"
    let n := match num with
      | some n => s!" {n.render}"
      | none => ""
    s!"{ind}float {k}{n}{if capAbove then " caption-above" else ""}\n" ++
    (if caption.isEmpty then ""
     else s!"{ind}  caption\n" ++ dumpInlines (ind ++ "    ") caption) ++
    dumpBlocks (ind ++ "  ") body
  | .bibliography src style items =>
    let st := match style with
      | some s => s!" style {s.quote}"
      | none => ""
    s!"{ind}bibliography {src.quote}{st}\n" ++
    String.join (items.toList.map fun item =>
      let mark := match item.marker with
        | some m => s!"[{m}] "
        | none => ""
      s!"{ind}  {mark}{item.key.quote}\n" ++
        dumpInlines (ind ++ "    ") item.content)
  | .contents spec entries =>
    s!"{ind}contents depth {spec.depth} current {spec.current.1}.{spec.current.2.1}.\
{spec.current.2.2}\n" ++
    String.join (entries.toList.map fun e =>
      s!"{ind}  entry {e.depth} {(e.number.getD "-").quote} {(e.target.getD "-").quote}" ++
        (if e.shaded then " shaded\n" else "\n") ++ dumpInlines (ind ++ "    ") e.title)

end

section DesignResolve

public def Design.declared? (pal : Palette) (r : Role) : Option Color :=
  pal.lookup (.role r)

/-- The palette the class's default seeds generate at a depth in a scheme. -/
@[expose] public def Design.classDefaults (d : GroundDepth) (s : Scheme) :
    SeedPalette.Seeds × Option SeedPalette.Colors :=
  let s := if s == .print then .light else s
  match PaletteData.classGenerated.find? (fun e => e.1 == d && e.2.1 == s) with
  | some e => (e.2.2.1, some e.2.2.2)
  | none =>
    let seeds := SeedPalette.classSeedsIn s
    (seeds, ((SeedPalette.generate seeds (seeds.targetsIn d s)).toOption).map (·.colors))

/-- The colour the palette's seeds generate for a role in a scheme: the
document's own seeds where declared, else the class's. -/
@[expose] public def Design.seededColor (pal : Palette) (s : Scheme) (r : Role) : Option Color :=
  let raw := match pal.seeded with
    | some st => SeedPalette.Colors.role st.seeds st.colors r
    | none =>
      let cd := Design.classDefaults pal.classColors.depth s
      (SeedPalette.seedRole cd.1 r).or (cd.2.bind fun c => SeedPalette.Colors.role cd.1 c r)
  raw.map fun c => (Color.ofHtml c.r c.g c.b).engine

/-- One default, read through `look` for the roles it names, and through
`printLook` for a role it reads as printed. -/
@[expose] public def Design.fallbackWith (s : Scheme) (need : Need)
    (gen look printLook : Role → Option Color) : Fallback → Option Color
  | .first rs => rs.findSome? look
  | .readable bar cands unbarred =>
    match look bar with
    | some g =>
      let vals := cands.filterMap look
      (vals.find? fun c => decide (Contrast.requiredIn s need ≤ Contrast.contrastMilli c g)).or
        vals.head?
    | none => unbarred.findSome? look
  | .inPrint r => printLook r
  | .const c => some c
  | .absent => none
  | .code => none
  | .seeded r => gen r

/-- The resolver at a stratum: a role of depth `d` reads the roles its default names at `d - 1`. -/
@[expose] public def Design.atDepth (pal : Palette) : Nat → Scheme → Role → Option Color
  | 0, s, r => (Design.declared? pal r).or
      (Design.fallbackWith s r.row.need (Design.seededColor pal s) (fun _ => none) (fun _ => none)
        (r.row.fallback pal.classColors.row s))
  | n + 1, s, r => (Design.declared? pal r).or
      (Design.fallbackWith s r.row.need (Design.seededColor pal s) (Design.atDepth pal n s)
        (Design.atDepth pal n .print) (r.row.fallback pal.classColors.row s))

/-- A role's colour in a scheme: the palette's declaration, else its row's
default there; `none` for a role nothing paints. -/
@[expose] public def Design.at (pal : Palette) (s : Scheme) (r : Role) : Option Color :=
  Design.atDepth pal r.depth s r

/-- Whether the document itself declares the focus role, not a theme it loads. -/
public def Doc.declaresFocus (doc : Doc) : Bool := doc.ownRoles.contains .focus

private theorem filterMap_ext_mem {α β : Type} (f g : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: rest, h => by
    simp only [List.filterMap_cons]
    rw [h a (List.mem_cons_self ..),
      filterMap_ext_mem f g rest (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]

private theorem findSome?_ext_mem {α β : Type} (f g : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.findSome? f = l.findSome? g
  | [], _ => rfl
  | a :: rest, h => by
    simp only [List.findSome?_cons]
    rw [h a (List.mem_cons_self ..),
      findSome?_ext_mem f g rest (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]

private theorem Design.fallbackWith_congr (s : Scheme) (need : Need) (gen f g f' g' : Role → Option Color)
    (fb : Fallback) (h : ∀ r ∈ fb.refs, f r = g r) (h' : ∀ r ∈ fb.refs, f' r = g' r) :
    Design.fallbackWith s need gen f f' fb = Design.fallbackWith s need gen g g' fb := by
  cases fb with
  | first rs => exact findSome?_ext_mem f g rs h
  | readable bar cands unbarred =>
    simp only [Design.fallbackWith]
    have hb : f bar = g bar := h bar (by simp [Fallback.refs])
    have hc := filterMap_ext_mem f g cands fun r hr => h r (by simp [Fallback.refs, hr])
    have hu := findSome?_ext_mem f g unbarred fun r hr => h r (by simp [Fallback.refs, hr])
    rw [hb, hc, hu]
  | inPrint r => exact h' r (by simp [Fallback.refs])
  | const c => rfl
  | absent => rfl
  | code => rfl
  | seeded r => rfl

private theorem Role.refs_shallower (r : Role) (c : ClassRow) (s : Scheme) :
    ∀ r' ∈ (r.row.fallback c s).refs, r'.depth < r.depth := by
  have h := List.all_eq_true.mp Role.fallback_depth_monotone r
    (List.contains_iff_mem.mp (Role.all_complete r))
  have hc := List.all_eq_true.mp h c (by cases c <;> simp [ClassRow.all])
  have hs := List.all_eq_true.mp hc s (by cases s <;> simp [Scheme.all])
  intro r' hr'
  exact of_decide_eq_true (List.all_eq_true.mp hs r' hr')

private theorem Design.atDepth_stable (pal : Palette) :
    ∀ (n : Nat) (s : Scheme) (r : Role), r.depth ≤ n →
      Design.atDepth pal n s r = Design.at pal s r := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s r hr
    have refs := Role.refs_shallower r pal.classColors.row s
    have rhs : Design.at pal s r = (Design.declared? pal r).or
        (Design.fallbackWith s r.row.need (Design.seededColor pal s) (Design.at pal s)
          (Design.at pal .print) (r.row.fallback pal.classColors.row s)) := by
      show Design.atDepth pal r.depth s r = _
      cases hd : r.depth with
      | zero =>
        simp only [Design.atDepth]
        congr 1
        apply Design.fallbackWith_congr
        · intro r' hr'
          have := refs r' hr'
          omega
        · intro r' hr'
          have := refs r' hr'
          omega
      | succ d =>
        simp only [Design.atDepth]
        congr 1
        apply Design.fallbackWith_congr
        · intro r' hr'
          have := refs r' hr'
          exact ih d (by omega) s r' (by omega)
        · intro r' hr'
          have := refs r' hr'
          exact ih d (by omega) .print r' (by omega)
    rw [rhs]
    cases n with
    | zero =>
      simp only [Design.atDepth]
      congr 1
      apply Design.fallbackWith_congr
      · intro r' hr'
        have := refs r' hr'
        omega
      · intro r' hr'
        have := refs r' hr'
        omega
    | succ m =>
      simp only [Design.atDepth]
      congr 1
      apply Design.fallbackWith_congr
      · intro r' hr'
        have := refs r' hr'
        exact ih m (by omega) s r' (by omega)
      · intro r' hr'
        have := refs r' hr'
        exact ih m (by omega) .print r' (by omega)

public theorem Design.resolve_unfold_exact (pal : Palette) (s : Scheme) (r : Role) :
    Design.at pal s r = (Design.declared? pal r).or
      (Design.fallbackWith s r.row.need (Design.seededColor pal s) (Design.at pal s)
        (Design.at pal .print) (r.row.fallback pal.classColors.row s)) := by
  have refs := Role.refs_shallower r pal.classColors.row s
  show Design.atDepth pal r.depth s r = _
  cases hd : r.depth with
  | zero =>
    simp only [Design.atDepth]
    congr 1
    apply Design.fallbackWith_congr
    · intro r' hr'
      have := refs r' hr'
      omega
    · intro r' hr'
      have := refs r' hr'
      omega
  | succ d =>
    simp only [Design.atDepth]
    congr 1
    apply Design.fallbackWith_congr
    · intro r' hr'
      have := refs r' hr'
      exact Design.atDepth_stable pal d s r' (by omega)
    · intro r' hr'
      have := refs r' hr'
      exact Design.atDepth_stable pal d .print r' (by omega)

/-- The declared roles, in declaration order. -/
public def Palette.declaredRoles (p : Palette) : Array (Role × Color) :=
  p.entries.filterMap fun
    | (.role r, c) => some (r, c)
    | (.color _, _) => none

/-- One foreground/background pairing a themed element ships. -/
public structure ColorPair where
  fg : Color
  bg : Color
  deriving Repr, BEq

/-- A region's declared paint: missing channels inherit independently, and an
absent background requests no fill. -/
public structure SurfaceLook where
  fg : Option Color := none
  bg : Option Color := none
  deriving Repr, BEq

/-- Resolve a region on its enclosing surface; `look.bg` alone decides whether
to paint a new surface. -/
@[expose] public def SurfaceLook.resolve (look : SurfaceLook) (parent : ColorPair) : ColorPair :=
  { fg := look.fg.getD parent.fg, bg := look.bg.getD parent.bg }

public theorem SurfaceLook.resolve_contract (look : SurfaceLook) (parent : ColorPair) :
    (look.resolve parent).fg = look.fg.getD parent.fg ∧
    (look.resolve parent).bg = look.bg.getD parent.bg := by
  exact ⟨rfl, rfl⟩

/-- beamer's block colour boxes' `colsep*=.75ex`, shared by a painted title and body. -/
@[expose] public def titledPadding : SymLength := { ex := 750 }

public theorem titledPadding_contract (fontSize xHeight : Length) :
    titledPadding.resolve fontSize xHeight = 3 * xHeight / 4 := by
  simp only [titledPadding, SymLength.resolve]
  length_omega

/-- A painted title meeting a painted body: `\nointerlineskip\vskip-0.5pt`,
the body box overlapping the title box by half a point. -/
public def blockSeam : Length := Dim.pt 1 / 2

/-- `n` tenths of TeX's millimetre, as tcolorbox's lengths are TeX's. -/
public def texMmTenths (n : Int) : Length := Dim.pt (n * 7227) / 25400

/-- tcolorbox's box under `size=normal` (tcolorbox.sty): `boxrule=0.5mm`,
`boxsep=1mm`, `left=right=4mm`, `top=bottom=2mm`. -/
public def tcbRule : Length := texMmTenths 5
public def tcbBoxsep : Length := texMmTenths 10
public def tcbSide : Length := texMmTenths 40
public def tcbTop : Length := texMmTenths 20
public def tcbBottom : Length := texMmTenths 20

/-- How far a box's text stands inside its edges, on both sides: the rule,
`boxsep` and `left` (`right`). -/
public def tcbInset : Length := tcbRule + tcbBoxsep + tcbSide

/-- An unpainted body box opens on `\vskip-.25ex\vbox{}`, a quarter ex above its own top. -/
public def blockBodyRaise : SymLength := { ex := 250 }

/-- Beamer's three block body colours, which start empty; the palette's
bindings declare any fill. -/
@[expose] public def titledBodyLook (pal : Palette) (kind : TitledKind) : SurfaceLook :=
  { fg := Design.declared? pal (Role.bodyInk kind)
    bg := Design.declared? pal (Role.bodyGround kind) }

/-- A titled block's resolved look: the title's ink, and the bar behind it
when the palette declares one. -/
public structure TitledLook where
  fg : Color
  bar : Option Color
  deriving Repr, BEq

/-- The titled block's title look per kind, in print, along beamer's own parent chain. -/
@[expose] public def titledLook (pal : Palette) (kind : TitledKind) : TitledLook :=
  { fg := (Design.at pal .print (Role.titleInk kind)).getD Color.black
    bar := Design.at pal .print (Role.titleBar kind) }


/-- The document's resolved design: every semantic role the backends read,
with every default applied here. -/
public structure Design where
  fg : Color
  bg : Color
  fgDeclared : Bool
  bgDeclared : Bool
  /-- Pending overlay content covers to this fraction (percent) of its
  own ink over the surface, per colour. -/
  coveredFraction : Nat
  /-- A declared constant cover for runs with no colour of their own; `none`
  covers them at `coveredFraction` of `fg`. -/
  covered : Option Color
  /-- Quieted secondary furniture, as the chrome footer's small text; the body
  ink when undeclared. -/
  muted : Color
  /-- The frame-title bar, when the design has one. -/
  frametitle : Option ColorPair
  /-- The title's ink when no bar is declared, and the subtitle's ink on the same title surface. -/
  frameTitleFg : Color
  framesubtitle : Color
  /-- The section divider's heading, on the page's ground. -/
  sectionTitle : Color
  /-- The chrome footline's ink and optional band background. -/
  footline : TitledLook
  /-- The titled block's title look, one per kind. -/
  blockTitle : TitledLook
  alertTitle : TitledLook
  exampleTitle : TitledLook
  /-- Each body inherits the enclosing surface unless its own channels are declared. -/
  blockBody : SurfaceLook
  alertBody : SurfaceLook
  exampleBody : SurfaceLook
  /-- The themed section page and its progress bar, when the design has one. -/
  progress : Option ColorPair
  /-- The section page's progress colours: the base ones unless it overrides a channel. -/
  sectionProgress : Option ColorPair
  /-- A `[standout]` frame's pair; without the keys it inverts the page's own colours. -/
  standout : ColorPair
  /-- The title page's own ground and ink, when the design declares one. -/
  titlepage : Option ColorPair
  /-- The title-page rule's colour; the ink when undeclared. -/
  separator : Color
  /-- Thickness of the progress bar, resolved at layout like any token. -/
  progressheight : SymGlue
  styles : Styles
  deriving Repr, BEq

/-- The design record in one scheme, every colour field a projection of `Design.at`. -/
@[expose] public def Design.resolve (pal : Palette) (s : Scheme) : Design :=
  let res := Design.at pal s
  let fg := (res .ink).getD Color.black
  let bg := (res .page).getD Color.white
  let muted := (res .muted).getD fg
  let footBg := res .footBand
  let titled (k : TitledKind) : TitledLook :=
    { fg := (res (Role.titleInk k)).getD fg, bar := res (Role.titleBar k) }
  { fg := fg
    bg := bg
    fgDeclared := (Design.declared? pal .ink).isSome
    bgDeclared := (Design.declared? pal .page).isSome
    coveredFraction := pal.coveredFraction.getD
      (if (res .covered).isSome then transparentShare else coveredFractionDefault)
    covered := res .covered
    muted := muted
    frametitle := (res .frameTitleBar).map fun barBg =>
      { fg := (res .frameTitleInk).getD bg, bg := barBg : ColorPair }
    frameTitleFg := (res .frameTitleInk).getD fg
    framesubtitle := (res .frameSubtitleInk).getD fg
    sectionTitle := (res .sectionTitleInk).getD fg
    footline := { fg := (res .footInk).getD muted, bar := footBg }
    blockTitle := titled .block
    alertTitle := titled .alert
    exampleTitle := titled .example
    blockBody := titledBodyLook pal .block
    alertBody := titledBodyLook pal .alert
    exampleBody := titledBodyLook pal .example
    progress := (res .progressFill).map fun f => { fg := f, bg := (res .progressTrack).getD bg }
    sectionProgress := (res .sectionProgressFill).map fun f =>
      { fg := f, bg := (res .sectionProgressTrack).getD bg }
    standout := { fg := (res .standoutInk).getD bg, bg := (res .standoutGround).getD fg }
    titlepage := (res .titlePageGround).map fun ground =>
      { fg := (res .titlePageInk).getD bg, bg := ground }
    separator := (res .separator).getD fg
    progressheight := { width := Dim.SymLength.ofLength (Dim.pt 1) }
    styles := {} }

/-- The print design, which the PDF paints and the contrast judge reads. -/
@[expose] public def Design.ofPalette (pal : Palette) : Design := Design.resolve pal .print

/-- The printed ink alone: `(Design.ofPalette pal).fg` without resolving the
rest of the design. -/
@[expose] public def Design.printInk (pal : Palette) : Color :=
  (Design.at pal .print .ink).getD Color.black

/-- The printed page alone: `(Design.ofPalette pal).bg`. -/
@[expose] public def Design.printPage (pal : Palette) : Color :=
  (Design.at pal .print .page).getD Color.white

public theorem Design.printInk_agree (pal : Palette) :
    (Design.ofPalette pal).fg = Design.printInk pal := rfl

public theorem Design.printPage_agree (pal : Palette) :
    (Design.ofPalette pal).bg = Design.printPage pal := rfl

/-- The ground a listing stands on in a scheme: its declared `bgcolor`, else
the verbatim ground the class paints. -/
@[expose] public def ListingSpec.groundIn (spec : ListingSpec) (pal : Palette) (s : Scheme) :
    Option (Color × Option ColorRef) :=
  spec.ground.orElse fun _ => (Design.at pal s .codeSurface).map (·, some (.role .codeSurface))

private theorem Design.resolve_congr (p q : Palette) (s : Scheme)
    (hd : ∀ r, Design.declared? p r = Design.declared? q r)
    (hc : p.coveredFraction = q.coveredFraction)
    (hg : Design.seededColor p = Design.seededColor q)
    (hk : p.classColors = q.classColors) :
    Design.resolve p s = Design.resolve q s := by
  have hdepth : ∀ m, Design.atDepth p m = Design.atDepth q m := by
    intro m
    induction m with
    | zero => funext s r; simp only [Design.atDepth, hd, hg, hk]
    | succ m ih => funext s r; simp only [Design.atDepth, hd, ih, hg, hk]
  have hat : Design.at p s = Design.at q s := by
    funext r
    simp only [Design.at, hdepth]
  simp only [Design.resolve, titledBodyLook, hat, hd, hc]

public theorem Palette.defineColor_design_id (pal : Palette) (n : String) (c : Color)
    (d : Bool) (s : Scheme) :
    Design.resolve (pal.declare (.color n) c d) s = Design.resolve pal s :=
  Design.resolve_congr _ _ s
    (fun r => Palette.declare_keeps_others pal (.color n) (.role r) c d (by simp)) rfl rfl rfl

/-- The names an xcolor definition of `n` declares: the author colour, and the role of that key
an xcolor name declares, a code role's or the alert's mark. -/
@[expose] public def Palette.xcolorRefs (n : String) : List ColorRef :=
  .color n :: ((Role.ofXcolor? n).map ColorRef.role).toList

/-- An xcolor definition of `n`: every name it declares, at one colour. -/
@[expose] public def Palette.defineXcolor (pal : Palette) (n : String) (c : Color)
    (d : Bool := false) : Palette :=
  (Palette.xcolorRefs n).foldl (fun p k => p.declare k c d) pal

public theorem Palette.defineXcolor_role_exact (pal : Palette) (n : String) (c : Color)
    (d : Bool) (r : Role) (h : Role.ofXcolor? n = some r) :
    Design.declared? (pal.defineXcolor n c d) r = some c := by
  simp only [Palette.defineXcolor, Palette.xcolorRefs, h, Option.map_some, Option.toList_some,
    List.foldl_cons, List.foldl_nil, Design.declared?]
  exact Palette.declare_find_exact _ _ _ _

public theorem Palette.defineXcolor_resolve_exact (pal : Palette) (n : String) (c : Color)
    (d : Bool) (s : Scheme) (r : Role) (h : Role.ofXcolor? n = some r) :
    Design.resolve (pal.defineXcolor n c d) s = Design.resolve (pal.declare (.role r) c d) s := by
  simp only [Palette.defineXcolor, Palette.xcolorRefs, h, Option.map_some, Option.toList_some,
    List.foldl_cons, List.foldl_nil]
  refine Design.resolve_congr _ _ s (fun r' => ?_) rfl rfl rfl
  simp only [Design.declared?]
  by_cases hr : r' = r
  · subst hr
    rw [Palette.declare_find_exact, Palette.declare_find_exact]
  · have hne : ColorRef.role r' ≠ .role r := fun he => hr (ColorRef.role.inj he)
    rw [Palette.declare_keeps_others _ _ _ _ _ hne, Palette.declare_keeps_others _ _ _ _ _ hne,
      Palette.declare_keeps_others pal (.color n) (.role r') c d (by simp)]

public theorem Palette.defineXcolor_design_id (pal : Palette) (n : String) (c : Color)
    (d : Bool) (s : Scheme) (h : Role.ofXcolor? n = none) :
    Design.resolve (pal.defineXcolor n c d) s = Design.resolve pal s := by
  simp only [Palette.defineXcolor, Palette.xcolorRefs, h, Option.map_none, Option.toList_none,
    List.foldl_cons, List.foldl_nil]
  exact Palette.defineColor_design_id pal n c d s

public theorem Design.marker_print_light_exact (pal : Palette) :
    Design.at pal .light .marker = Design.at pal .print .marker := by
  rw [Design.resolve_unfold_exact pal .light, Design.resolve_unfold_exact pal .print]
  cases pal.classColors.row <;>
    simp [Role.row, Row.engine, Row.markerFallback, Design.fallbackWith]

public theorem Design.marker_printInk_exact (pal : Palette) (h : Design.declared? pal .marker = none) :
    Design.at pal .light .marker = Design.at pal .print .ink := by
  rw [Design.resolve_unfold_exact pal .light, h]
  cases pal.classColors.row <;>
    simp [Role.row, Row.engine, Row.markerFallback, Design.fallbackWith]

public theorem Design.at_declared (pal : Palette) (s : Scheme) (r : Role) (c : Color)
    (h : Design.declared? pal r = some c) : Design.at pal s r = some c := by
  rw [Design.resolve_unfold_exact, h]
  rfl

public theorem Design.at_ink_isSome (pal : Palette) (s : Scheme) :
    (Design.at pal s .ink).isSome = true := by
  rw [Design.resolve_unfold_exact]
  cases Design.declared? pal .ink with
  | some _ => rfl
  | none =>
    cases s
    · rfl
    all_goals
      simp only [Option.none_or, Role.row, Row.keyed, Row.screen, Design.fallbackWith,
        Design.seededColor]
      cases pal.seeded <;> simp [SeedPalette.Colors.role, SeedPalette.seedRole]

public theorem Design.at_page_isSome (pal : Palette) (s : Scheme) :
    (Design.at pal s .page).isSome = true := by
  rw [Design.resolve_unfold_exact]
  cases Design.declared? pal .page with
  | some _ => rfl
  | none =>
    cases s
    · rfl
    all_goals
      simp only [Option.none_or, Role.row, Row.keyed, Row.screen, Design.fallbackWith,
        Design.seededColor]
      cases pal.seeded <;> simp [SeedPalette.Colors.role, SeedPalette.seedRole]

/-- One pair a design ships: a role's ink on the ground it stands on, and what
the ink owes there. -/
public structure Site where
  role : Role
  ink : Color
  on : Role
  ground : Color
  need : Need
  scheme : Scheme
  deriving Repr, BEq

/-- A site's pair meets its need in its scheme (WCAG 2.2's ratio). -/
@[expose] public def Site.passes (st : Site) : Bool :=
  decide (Contrast.requiredIn st.scheme st.need ≤ Contrast.contrastMilli st.ink st.ground)

/-- A site's pair meets its need at its medium's size (`Need.atStage`). -/
@[expose] public def Site.passesAt (stage : Bool) (st : Site) : Bool :=
  decide (Contrast.requiredIn st.scheme (st.need.atStage stage) ≤
    Contrast.contrastMilli st.ink st.ground)

/-- The site one role ships in a scheme, when its row pairs it with a ground,
its presence holds and its ink resolves. -/
@[expose] public def Design.site? (pal : Palette) (s : Scheme) (r : Role) : Option Site :=
  r.row.ground.bind fun g =>
    if r.row.need.paired && r.row.presence.holds (Design.at pal s) then
      (Design.at pal s r).map fun ink =>
        match Design.at pal s g with
        | some c => { role := r, ink, on := g, ground := c, need := r.row.need, scheme := s }
        | none =>
          { role := r, ink, on := .page, ground := (Design.at pal s .page).getD Color.white,
            need := r.row.need, scheme := s }
    else none

/-- Every pair a design ships, generated from the registry's rows in registry order. -/
@[expose] public def Design.sites (pal : Palette) (s : Scheme) : List Site :=
  Role.all.filterMap (Design.site? pal s)

public theorem Design.sites_covers (pal : Palette) (s : Scheme) (r g : Role) (c : Color)
    (hg : r.row.ground = some g) (hn : r.row.need.paired = true)
    (hp : r.row.presence.holds (Design.at pal s) = true) (hc : Design.at pal s r = some c) :
    ∃ st ∈ Design.sites pal s, st.role = r ∧ st.ink = c := by
  have hmem : r ∈ Role.all := List.contains_iff_mem.mp (Role.all_complete r)
  cases hgr : Design.at pal s g with
  | some b =>
    exact ⟨{ role := r, ink := c, on := g, ground := b, need := r.row.need, scheme := s },
      List.mem_filterMap.mpr ⟨r, hmem, by simp [Design.site?, hg, hn, hp, hc, hgr]⟩, rfl, rfl⟩
  | none =>
    exact ⟨{ role := r, ink := c, on := .page
             ground := (Design.at pal s .page).getD Color.white, need := r.row.need, scheme := s },
      List.mem_filterMap.mpr ⟨r, hmem, by simp [Design.site?, hg, hn, hp, hc, hgr]⟩, rfl, rfl⟩

/-- One role property's declaration: a colour, or the role it aliases. -/
public inductive CssDecl where
  | value (c : Color)
  | alias (r : Role)
  deriving Repr, BEq, Inhabited

/-- A declaration read through `look` for the role an alias names. -/
@[expose] public def CssDecl.resolve (look : Role → Option Color) : CssDecl → Option Color
  | .value c => some c
  | .alias r => look r

/-- The alias a default resolves through, read as `Design.fallbackWith` reads its roles. -/
@[expose] public def Design.fallbackDecl (s : Scheme) (need : Need) (pal : Palette)
    (look printLook : Role → Option Color) : Fallback → Option CssDecl
  | .first rs => (rs.find? fun r => (look r).isSome).map .alias
  | .readable bar cands unbarred =>
    match look bar with
    | some g =>
      let live := cands.filter fun r => (look r).isSome
      ((live.find? fun r => (look r).any fun c =>
          decide (Contrast.requiredIn s need ≤ Contrast.contrastMilli c g)).or live.head?).map .alias
    | none => (unbarred.find? fun r => (look r).isSome).map .alias
  | .inPrint r =>
    match Design.declared? pal r with
    | some _ => some (.alias r)
    | none => (printLook r).map .value
  | .const c => some (.value c)
  | .absent => none
  | .code => none
  | .seeded r => (Design.seededColor pal s r).map .value

/-- The declaration a role's property carries in a scheme: its declared
colour, else its row's default as an alias or a constant. -/
@[expose] public def Design.cssDecl (pal : Palette) (s : Scheme) (r : Role) : Option CssDecl :=
  match Design.declared? pal r with
  | some c => some (.value c)
  | none => Design.fallbackDecl s r.row.need pal (Design.at pal s) (Design.at pal .print)
      (r.row.fallback pal.classColors.row s)

/-- Chasing a table of declarations at a stratum: a value is itself, an alias
the chase of its target one stratum down. -/
@[expose] public def Design.chaseAt (t : Role → Option CssDecl) : Nat → Role → Option Color
  | 0, r => (t r).bind fun
    | .value c => some c
    | .alias _ => none
  | n + 1, r => (t r).bind fun
    | .value c => some c
    | .alias r' => Design.chaseAt t n r'

/-- A table chased from a role's own stratum. -/
@[expose] public def Design.chase (t : Role → Option CssDecl) (r : Role) : Option Color :=
  Design.chaseAt t r.depth r

private theorem find?_isSome_bind {α β : Type} (f : α → Option β) :
    ∀ (l : List α), ((l.find? fun a => (f a).isSome).bind f) = l.findSome? f
  | [] => rfl
  | a :: rest => by
    simp only [List.find?_cons, List.findSome?_cons]
    cases hf : f a with
    | none => simpa [hf] using find?_isSome_bind f rest
    | some b => simp [hf]

private theorem live_find? (look : Role → Option Color) (Q : Color → Bool) :
    ∀ (l : List Role),
      (((l.filter fun r => (look r).isSome).find? fun r => (look r).any Q).bind look) =
        (l.filterMap look).find? Q
  | [] => rfl
  | a :: rest => by
    cases ha : look a with
    | none => simpa [List.filter_cons, List.filterMap_cons, ha] using live_find? look Q rest
    | some c =>
      by_cases hq : Q c = true
      · simp [ha, hq]
      · simpa [List.filter_cons, List.filterMap_cons, ha, hq] using live_find? look Q rest

private theorem live_head? (look : Role → Option Color) :
    ∀ (l : List Role),
      ((l.filter fun r => (look r).isSome).head?.bind look) = (l.filterMap look).head?
  | [] => rfl
  | a :: rest => by
    cases ha : look a with
    | none => simpa [List.filter_cons, List.filterMap_cons, ha] using live_head? look rest
    | some c => simp [ha]

private theorem or_bind_of_live {α β : Type} (f : α → Option β) (a b : Option α)
    (h : ∀ x, a = some x → (f x).isSome) : (a.or b).bind f = (a.bind f).or (b.bind f) := by
  cases a with
  | none => rfl
  | some x =>
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x rfl)
    simp [hy]

private theorem Design.fallbackDecl_resolve (s : Scheme) (need : Need) (pal : Palette)
    (look printLook : Role → Option Color)
    (hdecl : ∀ r c, Design.declared? pal r = some c → look r = some c ∧ printLook r = some c)
    (fb : Fallback) :
    (Design.fallbackDecl s need pal look printLook fb).bind (CssDecl.resolve look) =
      Design.fallbackWith s need (Design.seededColor pal s) look printLook fb := by
  cases fb with
  | first rs =>
    simp only [Design.fallbackDecl, Design.fallbackWith, Option.bind_map]
    exact find?_isSome_bind look rs
  | readable bar cands unbarred =>
    simp only [Design.fallbackDecl, Design.fallbackWith]
    cases hb : look bar with
    | none =>
      simp only [Option.bind_map]
      exact find?_isSome_bind look unbarred
    | some g =>
      simp only [Option.bind_map]
      have hlive : ∀ x, ((cands.filter fun r => (look r).isSome).find? fun r =>
          (look r).any fun c => decide (Contrast.requiredIn s need ≤ Contrast.contrastMilli c g)) =
            some x → (look x).isSome := by
        intro x hx
        exact (List.mem_filter.mp (List.mem_of_find?_eq_some hx)).2
      have hfun : (CssDecl.resolve look ∘ CssDecl.alias) = look := by funext r; rfl
      rw [hfun, or_bind_of_live look _ _ hlive, live_find?, live_head?]
  | inPrint r =>
    cases hd : Design.declared? pal r with
    | some c =>
      obtain ⟨h1, h2⟩ := hdecl r c hd
      simp [Design.fallbackDecl, Design.fallbackWith, hd, CssDecl.resolve, h1, h2]
    | none =>
      simp only [Design.fallbackDecl, Design.fallbackWith, hd]
      cases printLook r <;> rfl
  | const c => rfl
  | absent => rfl
  | code => rfl
  | seeded r =>
    simp only [Design.fallbackDecl, Design.fallbackWith]
    cases Design.seededColor pal s r <;> rfl

private theorem Design.fallbackDecl_alias_mem (s : Scheme) (need : Need) (pal : Palette)
    (look printLook : Role → Option Color) (fb : Fallback) (r : Role)
    (h : Design.fallbackDecl s need pal look printLook fb = some (.alias r)) :
    r ∈ fb.refs := by
  cases fb with
  | first rs =>
    simp only [Design.fallbackDecl, Option.map_eq_some_iff, CssDecl.alias.injEq] at h
    obtain ⟨r', hr', rfl⟩ := h
    exact List.mem_of_find?_eq_some hr'
  | readable bar cands unbarred =>
    simp only [Design.fallbackDecl] at h
    cases hb : look bar with
    | none =>
      simp only [hb, Option.map_eq_some_iff, CssDecl.alias.injEq] at h
      obtain ⟨r', hr', rfl⟩ := h
      simp [Fallback.refs, List.mem_of_find?_eq_some hr']
    | some g =>
      simp only [hb, Option.map_eq_some_iff, CssDecl.alias.injEq] at h
      obtain ⟨r', hr', rfl⟩ := h
      have hmem : r' ∈ cands.filter fun r => (look r).isSome := by
        cases hf : (cands.filter fun r => (look r).isSome).find? fun r =>
            (look r).any fun c => decide (Contrast.requiredIn s need ≤ Contrast.contrastMilli c g) with
        | some x =>
          rw [hf] at hr'
          cases hr'
          exact List.mem_of_find?_eq_some hf
        | none =>
          rw [hf] at hr'
          exact List.mem_of_mem_head? hr'
      simp [Fallback.refs, (List.mem_filter.mp hmem).1]
  | inPrint r' =>
    simp only [Design.fallbackDecl] at h
    cases hd : Design.declared? pal r' with
    | some c =>
      rw [hd] at h
      cases h
      simp [Fallback.refs]
    | none =>
      rw [hd] at h
      cases hp : printLook r' with
      | none => rw [hp] at h; cases h
      | some c => rw [hp] at h; cases h
  | const c => simp [Design.fallbackDecl] at h
  | absent => simp [Design.fallbackDecl] at h
  | code => simp [Design.fallbackDecl] at h
  | seeded r' => simp [Design.fallbackDecl] at h

private theorem bind_congr_some {α β : Type} (o : Option α) (f g : α → Option β)
    (h : ∀ x, o = some x → f x = g x) : o.bind f = o.bind g := by
  cases o with
  | none => rfl
  | some x => exact h x rfl

public theorem Design.cssDecl_alias_shallower (pal : Palette) (s : Scheme) (r r' : Role)
    (h : Design.cssDecl pal s r = some (.alias r')) : r'.depth < r.depth := by
  unfold Design.cssDecl at h
  cases hd : Design.declared? pal r with
  | some c => simp [hd] at h
  | none =>
    rw [hd] at h
    exact Role.refs_shallower r pal.classColors.row s r'
      (Design.fallbackDecl_alias_mem _ _ _ _ _ _ r' h)

public theorem Design.cssDecl_resolve (pal : Palette) (s : Scheme) (r : Role) :
    (Design.cssDecl pal s r).bind (CssDecl.resolve (Design.at pal s)) = Design.at pal s r := by
  rw [Design.resolve_unfold_exact]
  unfold Design.cssDecl
  cases hd : Design.declared? pal r with
  | some c => rfl
  | none =>
    simpa using Design.fallbackDecl_resolve s r.row.need pal (Design.at pal s) (Design.at pal .print)
      (fun r c h => ⟨Design.at_declared pal s r c h, Design.at_declared pal .print r c h⟩)
      (r.row.fallback pal.classColors.row s)

private theorem Design.chaseAt_stable (pal : Palette) (s : Scheme) :
    ∀ (n : Nat) (r : Role), r.depth ≤ n →
      Design.chaseAt (Design.cssDecl pal s) n r = Design.at pal s r := by
  intro n
  induction n with
  | zero =>
    intro r hr
    rw [← Design.cssDecl_resolve pal s r]
    simp only [Design.chaseAt]
    apply bind_congr_some
    intro x hx
    cases x with
    | value c => rfl
    | alias r' =>
      have := Design.cssDecl_alias_shallower pal s r r' hx
      omega
  | succ n ih =>
    intro r hr
    rw [← Design.cssDecl_resolve pal s r]
    simp only [Design.chaseAt]
    apply bind_congr_some
    intro x hx
    cases x with
    | value c => rfl
    | alias r' =>
      have := Design.cssDecl_alias_shallower pal s r r' hx
      exact ih r' (by omega)

public theorem Design.cssDecl_chase_exact (pal : Palette) (s : Scheme) (r : Role) :
    Design.chase (Design.cssDecl pal s) r = Design.at pal s r :=
  Design.chaseAt_stable pal s r.depth r (Nat.le_refl _)

/-- The role a role's property aliases in a scheme, if it aliases one. -/
@[expose] public def Design.aliasOf (pal : Palette) (s : Scheme) (r : Role) : Option Role :=
  match Design.cssDecl pal s r with
  | some (.alias p) => some p
  | _ => none

/-- The roles a role's aliases reach in some scheme of a list, itself included. -/
@[expose] public def Design.reachAt (pal : Palette) (schemes : List Scheme) :
    Nat → Role → List Role
  | 0, r => [r]
  | n + 1, r => r :: (schemes.filterMap (Design.aliasOf pal · r)).flatMap (Design.reachAt pal schemes n)

/-- The roles a role's aliases reach, from its own stratum. -/
@[expose] public def Design.reach (pal : Palette) (schemes : List Scheme) (r : Role) : List Role :=
  Design.reachAt pal schemes r.depth r

private theorem Design.aliasOf_shallower (pal : Palette) (s : Scheme) (r p : Role)
    (h : Design.aliasOf pal s r = some p) : p.depth < r.depth := by
  unfold Design.aliasOf at h
  split at h
  · rename_i hd
    cases h
    exact Design.cssDecl_alias_shallower pal s r _ hd
  · cases h

private theorem Design.self_mem_reachAt (pal : Palette) (schemes : List Scheme) (n : Nat)
    (r : Role) : r ∈ Design.reachAt pal schemes n r := by
  cases n <;> simp [Design.reachAt]

private theorem Design.reachAt_closed (pal : Palette) (schemes : List Scheme) :
    ∀ (n : Nat) (q r p : Role) (s : Scheme), q.depth ≤ n → s ∈ schemes →
      r ∈ Design.reachAt pal schemes n q → Design.aliasOf pal s r = some p →
        p ∈ Design.reachAt pal schemes n q := by
  intro n
  induction n with
  | zero =>
    intro q r p s hq _ hr hp
    simp only [Design.reachAt, List.mem_singleton] at hr
    subst hr
    have := Design.aliasOf_shallower pal s r p hp
    omega
  | succ n ih =>
    intro q r p s hq hs hr hp
    simp only [Design.reachAt, List.mem_cons, List.mem_flatMap, List.mem_filterMap] at hr ⊢
    rcases hr with rfl | ⟨q', ⟨s', hs', hq'⟩, hr'⟩
    · right
      exact ⟨p, ⟨s, hs, hp⟩, Design.self_mem_reachAt pal schemes n p⟩
    · right
      refine ⟨q', ⟨s', hs', hq'⟩, ?_⟩
      have hd := Design.aliasOf_shallower pal s' q q' hq'
      exact ih q' r p s (by omega) hs hr' hp

public theorem Design.reach_covers (pal : Palette) (schemes : List Scheme) (q r p : Role)
    (s : Scheme) (hs : s ∈ schemes) (hr : r ∈ Design.reach pal schemes q)
    (hp : Design.cssDecl pal s r = some (.alias p)) : p ∈ Design.reach pal schemes q :=
  Design.reachAt_closed pal schemes q.depth q r p s (Nat.le_refl _) hs hr
    (by simp [Design.aliasOf, hp])

/-- A table restricted to a set of roles. -/
@[expose] public def Design.restrict (t : Role → Option CssDecl) (roles : List Role) (r : Role) :
    Option CssDecl :=
  if roles.contains r then t r else none

private theorem Design.chaseAt_restrict (t : Role → Option CssDecl) (roles : List Role)
    (hclosed : ∀ r ∈ roles, ∀ p, t r = some (.alias p) → p ∈ roles) :
    ∀ (n : Nat) (r : Role), r ∈ roles →
      Design.chaseAt (Design.restrict t roles) n r = Design.chaseAt t n r := by
  intro n
  induction n with
  | zero =>
    intro r hr
    simp [Design.chaseAt, Design.restrict, hr]
  | succ n ih =>
    intro r hr
    have hc : roles.contains r = true := List.contains_iff_mem.mpr hr
    simp only [Design.chaseAt, Design.restrict, hc, ite_true]
    apply bind_congr_some
    intro x hx
    cases x with
    | value c => rfl
    | alias p => exact ih p (hclosed r hr p hx)

public theorem Design.chase_restrict_exact (t : Role → Option CssDecl) (roles : List Role)
    (hclosed : ∀ r ∈ roles, ∀ p, t r = some (.alias p) → p ∈ roles) (r : Role)
    (hr : r ∈ roles) : Design.chase (Design.restrict t roles) r = Design.chase t r :=
  Design.chaseAt_restrict t roles hclosed r.depth r hr

/-- The muted role's resolving chain: the palette's `muted`, else its `fg`, else black. -/
public def mutedOf (pal : Palette) : Color :=
  (Design.at pal .print .muted).getD Color.black

/-- One generated declaration installed, at its 8-bit sRGB colour, the engine's. -/
@[expose] public def Palette.declareSeeded (p : Palette) (e : Role × Color) : Palette :=
  p.declare (.role e.1) (Color.ofHtml e.2.r e.2.g e.2.b).engine

/-- One seed a palette declares installed, at its 8-bit sRGB colour. -/
@[expose] public def Palette.declareSeed (p : Palette) (e : Role × Color) : Palette :=
  p.declare (.role e.1) (Color.ofHtml e.2.r e.2.g e.2.b)

/-- One derived role installed, unless the document declared it (`keep`). -/
private def Palette.installDerived (keep : Role → Bool) (p : Palette) (e : Role × Color) :
    Palette :=
  if keep e.1 then p else p.declareSeeded e

/-- One element role a style binds, at its source role's installed colour,
unless the document declared the element (`keep`). -/
private def Palette.installBound (keep : Role → Bool) (p : Palette) (e : Role × Role) : Palette :=
  if keep e.1 then p else
    match Design.declared? p e.2 with
    | some c => p.declare (.role e.1) c
    | none => p

/-- A generated palette installed (`\palette[seeds]`): the seeds as the page's
ground, text and accent, then every role generation derives. -/
public def Palette.applySeedsUnder (pal : Palette) (st : SeedPalette.SeedState)
    (keep : Role → Bool) : Palette :=
  let seeds : List (Role × Color) :=
    [(.page, st.seeds.paper), (.ink, st.seeds.ink), (.accent, st.seeds.accent)]
  let withSeeds := seeds.foldl Palette.declareSeed { pal with seeded := some st }
  let withDerived := (SeedPalette.derivedEntries st).foldl (Palette.installDerived keep) withSeeds
  (SeedPalette.bound st).foldl (Palette.installBound keep) withDerived

/-- A generated palette installed over a palette that declares nothing the seeds derive. -/
public def Palette.applySeeds (pal : Palette) (st : SeedPalette.SeedState) : Palette :=
  pal.applySeedsUnder st fun _ => false

/-- Whether `el` is an element ink a generated palette chooses for the ground `g`. -/
@[expose] public def Role.boundTo (el g : Role) : Bool :=
  SeedPalette.elementRoles.contains el && el.row.ground == some g

/-- The colour a generated palette installs for a role, as the palette holds it (8-bit). -/
@[expose] public def Design.installed (st : SeedPalette.SeedState) (r : Role) :
    Option Color :=
  (SeedPalette.Colors.role st.seeds st.colors (((SeedPalette.bound st).lookup r).getD r)).map
    fun c => (Color.ofHtml c.r c.g c.b).engine

/-- The palette with each bound element ink the document does not declare
erased where its ground stands off its generated colour, and reinstated where
the ground is back on it. -/
public def Palette.yieldGrounds (pal : Palette) (keep : Role → Bool) : Palette :=
  match pal.seeded with
  | none => pal
  | some st =>
    (SeedPalette.bound st).foldl (fun p (el, _) =>
      if keep el then p else
      let off := el.row.ground.any fun g =>
        el.boundTo g && Design.declared? p g != Design.installed st g
      if off && Design.declared? p el == Design.installed st el then p.erase (.role el)
      else if !off && (Design.declared? p el).isNone then
        match Design.installed st el with
        | some c => p.declare (.role el) c
        | none => p
      else p) pal

/-- Whether a colour reads more against white text than against black. -/
private def Color.darkGround (c : Color) : Bool :=
  decide (Contrast.contrastMilli c Color.black < Contrast.contrastMilli c Color.white)

/-- A palette's generated roles moved from one generated state to the next, each role a declaration
or `keep` holds off its generated colour left as it stands. -/
public def Palette.replaceGenerated (pal : Palette) (keep : Role → Bool)
    (st st' : SeedPalette.SeedState) : Palette :=
  let roles := (SeedPalette.entries st).map (·.1) ++ (SeedPalette.bound st).map (·.1)
  roles.foldl (fun p r =>
    if keep r || Design.declared? p r != Design.installed st r then p else
    match Design.installed st' r with
    | some c => p.declare (.role r) c
    | none => p) { pal with seeded := some st' }

/-- A bundle's generated palette regenerated, at the cover share it was generated at, from the seeds
the document's page, ink and accent now declare. -/
public def Palette.reseed (pal : Palette) (keep : Role → Bool) : Palette :=
  match pal.seeded with
  | none => pal
  | some st =>
    if !st.bundle then pal else
    let paper := if keep .page then (Design.declared? pal .page).getD st.seeds.paper
      else st.seeds.paper
    let turned := paper.darkGround != st.seeds.paper.darkGround
    let ink := if keep .ink then (Design.declared? pal .ink).getD st.seeds.ink
      else if turned then st.seeds.paper else st.seeds.ink
    let accent := if keep .accent then (Design.declared? pal .accent).getD st.seeds.accent
      else st.seeds.accent
    let seeds := { st.seeds with paper, ink, accent }
    if seeds == st.seeds then pal else
    let targets := { seeds.targets pal.classColors.depth with cover := st.targets.cover }
    match SeedPalette.generate seeds targets with
    | .error _ => pal
    | .ok g => pal.replaceGenerated keep st { st with seeds, targets, colors := g.colors }

private theorem Palette.installDerived_keeps (keep : Role → Bool) (es : List (Role × Color))
    (p : Palette) (r : Role) (h : ∀ e ∈ es, e.1 ≠ r) :
    (es.foldl (Palette.installDerived keep) p).lookup (.role r) = p.lookup (.role r) := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    rw [List.foldl_cons, ih _ (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    unfold Palette.installDerived Palette.declareSeeded
    split
    · rfl
    · exact Palette.declare_keeps_others _ _ _ _ _ fun heq =>
        h e (List.mem_cons_self ..) (ColorRef.role.inj heq).symm

private theorem Palette.installBound_keeps (keep : Role → Bool) (es : List (Role × Role))
    (p : Palette) (r : Role) (h : ∀ e ∈ es, e.1 ≠ r) :
    (es.foldl (Palette.installBound keep) p).lookup (.role r) = p.lookup (.role r) := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    rw [List.foldl_cons, ih _ (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    unfold Palette.installBound
    split
    · rfl
    · split
      · exact Palette.declare_keeps_others _ _ _ _ _ fun heq =>
          h e (List.mem_cons_self ..) (ColorRef.role.inj heq).symm
      · rfl

private theorem Palette.installDerived_kept (keep : Role → Bool) (es : List (Role × Color))
    (p : Palette) (r : Role) (hk : keep r = true) :
    (es.foldl (Palette.installDerived keep) p).lookup (.role r) = p.lookup (.role r) := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    rw [List.foldl_cons, ih]
    unfold Palette.installDerived Palette.declareSeeded
    split
    · rfl
    · rename_i hne
      refine Palette.declare_keeps_others _ _ _ _ _ fun heq => hne ?_
      rw [← ColorRef.role.inj heq]
      exact hk

private theorem Palette.installBound_kept (keep : Role → Bool) (es : List (Role × Role))
    (p : Palette) (r : Role) (hk : keep r = true) :
    (es.foldl (Palette.installBound keep) p).lookup (.role r) = p.lookup (.role r) := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    rw [List.foldl_cons, ih]
    unfold Palette.installBound
    split
    · rfl
    · rename_i hne
      split
      · refine Palette.declare_keeps_others _ _ _ _ _ fun heq => hne ?_
        rw [← ColorRef.role.inj heq]
        exact hk
      · rfl

public theorem Palette.applySeedsUnder_keep_exact (pal : Palette) (st : SeedPalette.SeedState)
    (keep : Role → Bool) (r : Role) (hk : keep r = true)
    (hs : r ≠ .ink ∧ r ≠ .page ∧ r ≠ .accent) :
    (pal.applySeedsUnder st keep).lookup (.role r) = pal.lookup (.role r) := by
  simp only [Palette.applySeedsUnder, List.foldl_cons, List.foldl_nil]
  rw [Palette.installBound_kept _ _ _ _ hk, Palette.installDerived_kept _ _ _ _ hk]
  unfold Palette.declareSeed
  rw [Palette.declare_keeps_others _ (.role .accent) (.role r) _ _ (by simpa using hs.2.2),
    Palette.declare_keeps_others _ (.role .ink) (.role r) _ _ (by simpa using hs.1),
    Palette.declare_keeps_others _ (.role .page) (.role r) _ _ (by simpa using hs.2.1)]
  rfl

public theorem Palette.applySeedsUnder_seeds_exact (pal : Palette) (st : SeedPalette.SeedState)
    (keep : Role → Bool) :
    Design.declared? (pal.applySeedsUnder st keep) .ink =
        some (Color.ofHtml st.seeds.ink.r st.seeds.ink.g st.seeds.ink.b) ∧
      Design.declared? (pal.applySeedsUnder st keep) .page =
        some (Color.ofHtml st.seeds.paper.r st.seeds.paper.g st.seeds.paper.b) ∧
      Design.declared? (pal.applySeedsUnder st keep) .accent =
        some (Color.ofHtml st.seeds.accent.r st.seeds.accent.g st.seeds.accent.b) := by
  have hd := (SeedPalette.generate_seeds_exact st).1
  have hb := (SeedPalette.generate_seeds_exact st).2
  simp only [Design.declared?, Palette.applySeedsUnder, List.foldl_cons, List.foldl_nil]
  refine ⟨?_, ?_, ?_⟩
  · rw [Palette.installBound_keeps _ _ _ _ fun e he => (hb e he).1,
      Palette.installDerived_keeps _ _ _ _ fun e he => (hd e he).1]
    unfold Palette.declareSeed
    rw [Palette.declare_keeps_others _ (.role .accent) (.role .ink) _ _ (by simp),
      Palette.declare_last_wins]
  · rw [Palette.installBound_keeps _ _ _ _ fun e he => (hb e he).2.1,
      Palette.installDerived_keeps _ _ _ _ fun e he => (hd e he).2.1]
    unfold Palette.declareSeed
    rw [Palette.declare_keeps_others _ (.role .accent) (.role .page) _ _ (by simp),
      Palette.declare_keeps_others _ (.role .ink) (.role .page) _ _ (by simp),
      Palette.declare_last_wins]
  · rw [Palette.installBound_keeps _ _ _ _ fun e he => (hb e he).2.2,
      Palette.installDerived_keeps _ _ _ _ fun e he => (hd e he).2.2]
    unfold Palette.declareSeed
    rw [Palette.declare_last_wins]

/-- The text target a generated run owes on a ground: the ink's own on the ink, the page's
elsewhere. -/
@[expose] public def groundNeed (st : SeedPalette.SeedState) (g : Color) : Nat :=
  if g == st.seeds.ink then st.targets.inverse else st.targets.text

/-- A run coloured by a generated role, on a ground it does not read on at `groundNeed`: its
family's tone there. -/
public def Palette.groundRun (pal : Palette) (g : Color) (x : Inline) : Inline :=
  match x, pal.seeded with
  | .colored c (some (.role r)) body, some st =>
    if SeedPalette.Colors.role st.seeds st.colors r == some c && Design.declared? pal r == some c &&
        decide (Contrast.contrastMilli c g < groundNeed st g) then
      match st.toneOn r g with
      | some (c', ref) => .colored c' (ref.map ColorRef.role) body
      | none => x
    else x
  | _, _ => x

public theorem Palette.groundRun_text (pal : Palette) (g : Color) (x : Inline) :
    plainTextOne (pal.groundRun g x) = plainTextOne x := by
  unfold Palette.groundRun
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

/-- Whether a palette's page is dark; an undeclared page is the class's white. -/
@[expose] public def Palette.darkPage (pal : Palette) : Bool :=
  match Design.declared? pal .page with
  | some p => decide (Contrast.contrastMilli p Color.black < Contrast.contrastMilli p Color.white)
  | none => false

/-- The plain screen scheme of a palette's page's polarity. -/
@[expose] public def Palette.homeScreen (pal : Palette) : Scheme :=
  if pal.darkPage then .dark else .light

/-- The palette a generated palette's seeds generate in a scheme at a cover share: kept in
`PaletteData` where no share binds, else derived. -/
public def Design.generatedIn (seeds : SeedPalette.Seeds) (d : GroundDepth) (s : Scheme)
    (cover : Option Nat) : Option SeedPalette.Colors :=
  let kept := (PaletteData.bundleGenerated.find? fun e => e.1 == seeds && e.2.1 == d && e.2.2.1 == s).bind
    fun e => if cover.isNone then some e.2.2.2 else none
  kept.orElse fun _ =>
    ((SeedPalette.generate seeds { seeds.targetsIn d s with cover }).toOption).map (·.colors)

/-- A generated palette in a scheme: its seeds carried to the other polarity
where the scheme's flips the document's, at the document's cover share. -/
public def Design.carrySeeds (st : SeedPalette.SeedState) (d : GroundDepth)
    (s : Scheme) (flip : Bool) : Option SeedPalette.SeedState := do
  let carried ← st.seeds.carry (st.seeds.dark != flip)
  let ink ← if !s.more then some carried.ink
    else ContrastSolve.realizeNearest (Contrast.requiredIn s .text) carried.paper carried.ink
  let seeds := { carried with ink }
  let colors ← Design.generatedIn seeds d s st.targets.cover
  pure { st with seeds, targets := { seeds.targetsIn d s with cover := st.targets.cover }, colors }

/-- What a document's colours are carried by in one scheme: the scheme,
whether its polarity flips, and the document's page there. -/
public structure SchemeFrame where
  scheme : Scheme
  flip : Bool
  homePage : Color
  page : Color
  stage : Bool
  deriving Repr, BEq, Inhabited

/-- A document's frame in a scheme: its page on its own screen, and in the
other polarity the page its seeds carry there. -/
public def Palette.frame (doc : Palette) (s : Scheme) (stage : Bool := false) : SchemeFrame :=
  let homeS := doc.homeScreen
  let homePage := (Design.at doc homeS .page).getD Color.white
  let flip := s != .print && s.onDark != doc.darkPage
  let own : SeedPalette.Seeds :=
    { ink := (Design.at doc homeS .ink).getD Color.black, paper := homePage
      accent := (Design.at doc homeS .accent).getD ClassColors.accent }
  let page : Color := if !flip then homePage else
    match doc.seeded.bind (Design.carrySeeds · doc.classColors.depth s true) with
    | some st => st.seeds.paper
    | none => SeedPalette.schemePaper own s.onDark
  { scheme := s, flip, homePage, page, stage }

/-- Whether a frame ships a palette as declared: in print, and on the
document's own plain screen. -/
@[expose] public def SchemeFrame.home (f : SchemeFrame) : Bool :=
  f.scheme == .print || (!f.flip && !f.scheme.more)

public theorem Palette.frame_print_home (doc : Palette) (stage : Bool) :
    (doc.frame .print stage).home = true := by
  simp [Palette.frame, SchemeFrame.home]

/-- A declared ground as a scheme carries it: itself on the document's
polarity, else its distance from the page carried over. -/
public def SchemeFrame.ground (f : SchemeFrame) (c : Color) : Color :=
  if !f.flip then c else if c == f.homePage then f.page else ContrastSolve.reflect f.homePage f.page c

/-- A colour a scheme could not carry legibly: its name, the role it was
judged on, and what was measured. -/
public structure Unrealized where
  name : ColorRef
  on : Role
  measured : Option (Nat × Nat) := none
  deriving Repr, BEq, Inhabited

/-- One declared ink carried to a scheme, adapted at the gate on its ground. -/
public def Design.carryInk (flip : Bool) (req : Nat) (homePage page ground c : Color) :
    Option Color :=
  if flip then ContrastSolve.adapt req homePage page c ground
  else if req ≤ Contrast.contrastMilli c ground then some c
  else ContrastSolve.realizeNearest req ground c

public theorem Design.adapt_between {flip : Bool} {req : Nat} {homePage page ground c c' : Color}
    (h : Design.carryInk flip req homePage page ground c = some c') :
    req ≤ Contrast.contrastMilli c' ground ∧
      (c' = c ∨ ∃ o : Oklab.Okl, o.a = (Oklab.labOf c).a ∧ o.b = (Oklab.labOf c).b ∧
        o.f ≤ Oklab.fracOne ∧ c' = o.toColor) := by
  unfold Design.carryInk at h
  split at h
  · obtain ⟨hm, hh⟩ := ContrastSolve.adapt_between h
    exact ⟨hm, Or.inr hh⟩
  · split at h
    · cases h
      exact ⟨‹_›, Or.inl rfl⟩
    · exact ⟨ContrastSolve.realizeNearest_meets h, ContrastSolve.realize_hue_between h⟩

/-- A colour no palette names, as a scheme carries it: itself where palettes
ship as declared, else carried as a declared ink. -/
public def Design.literalIn (f : SchemeFrame) (c : Color) : Color :=
  if f.home then c else
  (Design.carryInk f.flip (Contrast.requiredIn f.scheme (Need.text.atStage f.stage)) f.homePage
    f.page f.page c).getD (if f.flip then ContrastSolve.reflect f.homePage f.page c else c)

/-- A colour no palette names standing on a declared ground, `ground` as the scheme carries it:
itself where palettes ship as declared, else carried as a declared ink on that ground. -/
public def Design.literalOn (f : SchemeFrame) (ground c : Color) : Color :=
  if f.home then c else
  (Design.carryInk f.flip (Contrast.requiredIn f.scheme (Need.text.atStage f.stage)) f.homePage
    f.page ground c).getD (if f.flip then ContrastSolve.reflect f.homePage f.page c else c)

/-- The roles a colour stands on: the page and every role a row names as
its ground. -/
public def Role.grounds : List Role :=
  Role.all.filter fun g => g == .page || Role.all.any (·.row.ground == some g)

/-- The ground a use stands on, as a scheme ships it. -/
public def Palette.useGround (pal view : Palette) (f : SchemeFrame) (g : Color)
    (role : Option Role := none) : Color × Role :=
  match role.orElse fun _ => Role.grounds.find? (fun r => Design.at pal .light r == some g ||
      Design.at pal .print r == some g) with
  | some r => ((Design.at view f.scheme r).getD (f.ground g), r)
  | none => (f.ground g, .page)

/-- The grounds an ink must read on in a scheme's view, each with its role and
what reading on it owes. -/
public def Palette.inkGrounds (pal : Palette) (f : SchemeFrame)
    (used : List (ColorRef × List (Color × Bool × Option Role))) (p : Palette) (k : ColorRef) :
    List (Color × Role × Nat) :=
  let s := f.scheme
  let row : List (Color × Role × Nat) := match k with
    | .role r =>
      let on := r.row.ground.getD .page
      [((Design.at p s on).getD ((Design.at p s .page).getD f.page), on,
        Contrast.requiredIn s (r.row.need.atStage f.stage))]
    | .color _ => []
  row ++ ((((used.lookup k).getD []).eraseDups.filter fun (_, _, role) =>
      role != some .alertMark || (Design.at p s .alertMark).isSome).map fun (g, large, role) =>
    let (g', on) := pal.useGround p f g role
    (g', on, Contrast.requiredIn s ((if large then Need.largeText else .text).atStage f.stage)))

/-- One ink carried to a scheme's view on its grounds: itself where it reads
on every one, else the first carrying that does. -/
public def Palette.carryOn (pal : Palette) (f : SchemeFrame)
    (used : List (ColorRef × List (Color × Bool × Option Role))) (p : Palette) (k : ColorRef)
    (c : Color) (fresh : Bool := false) : Except (Role × Option (Nat × Nat)) (Option Color) :=
  let gs := pal.inkGrounds f used p k
  if gs.isEmpty then .ok none else
  let passes (x : Color) : Bool := gs.all fun (g, _, req) => req ≤ Contrast.contrastMilli x g
  let flip := f.flip && !fresh
  let tries := (if flip then [] else [c]) ++
    gs.filterMap fun (g, _, req) => Design.carryInk flip req f.homePage f.page g c
  match tries.find? passes with
  | some c' => .ok (some c')
  | none =>
    let best := tries.headD c
    match gs.find? fun (g, _, req) => Contrast.contrastMilli best g < req with
    | some (g, on, req) => .error (on, some (Contrast.contrastMilli best g, req))
    | none => .error (.page, none)

public theorem Palette.carryOn_between {pal : Palette} {f : SchemeFrame}
    {used : List (ColorRef × List (Color × Bool × Option Role))} {p : Palette} {k : ColorRef}
    {c c' : Color} {fresh : Bool} (h : pal.carryOn f used p k c fresh = .ok (some c')) :
    (∀ x ∈ pal.inkGrounds f used p k, x.2.2 ≤ Contrast.contrastMilli c' x.1) ∧
      (c' = c ∨ ∃ o : Oklab.Okl, o.a = (Oklab.labOf c).a ∧ o.b = (Oklab.labOf c).b ∧
        o.f ≤ Oklab.fracOne ∧ c' = o.toColor) := by
  unfold Palette.carryOn at h
  simp only at h
  split at h
  · cases h
  · split at h
    · rename_i c'' hfind
      cases h
      have hp := List.find?_some hfind
      have hm := List.mem_of_find?_eq_some hfind
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [List.all_eq_true, decide_eq_true_eq] at hp
        exact hp x hx
      · simp only [List.mem_append, List.mem_filterMap] at hm
        rcases hm with hc | ⟨_, _, hcarry⟩
        · split at hc
          · simp at hc
          · left; simpa using hc
        · exact (Design.adapt_between hcarry).2
    · split at h <;> cases h

/-- A palette carried to a scheme other than its home, with the colours it could not carry. -/
private def Palette.carried (pal : Palette) (f : SchemeFrame)
    (used : List (ColorRef × List (Color × Bool × Option Role))) : Palette × Array Unrealized :=
  let s := f.scheme
  let uses (k : ColorRef) : List (Color × Bool × Option Role) := (used.lookup k).getD []
  let carried : Option (Option SeedPalette.SeedState) :=
    pal.seeded.map (Design.carrySeeds · pal.classColors.depth s f.flip)
  let generated (r : Role) (c : Color) : Bool := (carried.bind id).isSome &&
    pal.seeded.any fun st => Design.installed st r == some c
  let inkLike (k : ColorRef) : Bool := !(uses k).isEmpty || match k with
    | .role r => r.row.need.paired
    | .color _ => true
  let grounds : Array (ColorRef × Color) × Array Unrealized :=
    pal.entries.foldl (fun (acc : Array (ColorRef × Color) × Array Unrealized) (k, c) =>
      match k with
      | .role r =>
        if generated r c then
          match carried.bind id |>.bind (Design.installed · r) with
          | some c' => (acc.1.push (k, c'), acc.2)
          | none => (acc.1.push (k, c), acc.2.push { name := k, on := r.row.ground.getD .page })
        else if inkLike k then (acc.1.push (k, c), acc.2)
        else (acc.1.push (k, f.ground c), acc.2)
      | .color _ => (acc.1.push (k, c), acc.2)) (#[], #[])
  let staged : Palette := { pal with entries := grounds.1, seeded := carried.bind id }
  let reqOf (k : ColorRef) : Nat := Contrast.requiredIn s ((match k with
    | .role r => r.row.need
    | .color _ => .text).atStage f.stage)
  let groundsOf (p : Palette) (k : ColorRef) : List (Color × Role × Nat) := pal.inkGrounds f used p k
  let carryOn (p : Palette) (k : ColorRef) (c : Color) (fresh : Bool := false) :
      Except (Role × Option (Nat × Nat)) (Option Color) := pal.carryOn f used p k c fresh
  let inks : Array (ColorRef × Color) × Array Unrealized :=
    (pal.entries.zip grounds.1).foldl (fun (acc : Array (ColorRef × Color) × Array Unrealized)
        ((k, c), (_, c0)) =>
      let isGenerated := match k with
        | .role r => generated r c
        | .color _ => false
      -- A generated ink that already meets the gate stays: more contrast never lowers it.
      let gs := if isGenerated && inkLike k && !f.flip then groundsOf staged k else []
      if !gs.isEmpty && gs.all (fun (g, _, req) =>
          req ≤ Contrast.contrastMilli c g && Contrast.contrastMilli c0 g ≤ Contrast.contrastMilli c g)
      then (acc.1.push (k, c), acc.2) else
      if !inkLike k || (isGenerated && (uses k).isEmpty) then (acc.1.push (k, c0), acc.2) else
      match carryOn staged k (if isGenerated then c0 else c) isGenerated with
      | .ok (some c') => (acc.1.push (k, c'), acc.2)
      | .ok none => (acc.1.push (k, c0), acc.2)
      | .error (on, measured) => (acc.1.push (k, c0), acc.2.push { name := k, on, measured }))
      (#[], grounds.2)
  let undeclaredOn (base : Palette) (start : Array (ColorRef × Color) × Array Unrealized) :
      Array (ColorRef × Color) × Array Unrealized :=
    used.foldl (fun (acc : Array (ColorRef × Color) × Array Unrealized) (k, _) =>
      match k with
      | .color _ => acc
      | .role r =>
        if pal.entries.any (·.1 == k) || !r.row.need.paired then acc else
        match Design.at base s r with
        | none => acc
        | some c =>
          match carryOn base k c true with
          | .ok (some c') => if c' == c then acc else (acc.1.push (k, c'), acc.2)
          | .ok none => acc
          | .error (on, measured) => (acc.1, acc.2.push { name := k, on, measured })) start
  let inks := undeclaredOn staged inks
  let out : Palette := { staged with entries := inks.1 }
  if !s.more || inks.2.isEmpty then (out, inks.2) else
  -- Where no tone of an ink's hue reaches the gate, its ground moves instead.
  let moves : Array (Role × Color) := inks.2.foldl (fun acc u =>
    if acc.any (·.1 == u.on) then acc else
    match Design.declared? out u.on, out.lookup u.name with
    | some g, some c =>
      let req := (u.measured.map (·.2)).getD (reqOf u.name)
      if (Design.carryInk f.flip req f.homePage f.page g c).isSome then acc else
      match ContrastSolve.realizeNearest req c g with
      | some g' => acc.push (u.on, g')
      | none => acc
    | _, _ => acc) #[]
  if moves.isEmpty then (out, inks.2) else
  let moved : Palette := { out with entries := out.entries.map fun (k, c) =>
    match k with
    | .role r => ((moves.find? (·.1 == r)).map fun (_, g) => (k, g)).getD (k, c)
    | .color _ => (k, c) }
  let rejudged : Array (ColorRef × Color) × Array Unrealized :=
    (pal.entries.zip moved.entries).foldl (fun (acc : Array (ColorRef × Color) × Array Unrealized)
        ((k, c), (_, c1)) =>
      let isGenerated := match k with
        | .role r => generated r c
        | .color _ => false
      if !inkLike k || (isGenerated && (uses k).isEmpty) ||
          (groundsOf moved k).all (fun (g, _, req) => req ≤ Contrast.contrastMilli c1 g) then
        (acc.1.push (k, c1), acc.2)
      else match carryOn moved k (if isGenerated then c1 else c) isGenerated with
        | .ok (some c') => (acc.1.push (k, c'), acc.2)
        | .ok none => (acc.1.push (k, c1), acc.2)
        | .error (on, measured) => (acc.1.push (k, c1), acc.2.push { name := k, on, measured }))
        (#[], grounds.2)
  let again := undeclaredOn { moved with entries := rejudged.1 } rejudged
  ({ moved with entries := again.1 }, again.2)

/-- A palette as a scheme ships it, with the colours it could not carry; a scheme of the other
polarity ships no mark, where the accent reads as text. -/
public def Palette.view (pal : Palette) (f : SchemeFrame)
    (used : List (ColorRef × List (Color × Bool × Option Role)) := []) : Palette × Array Unrealized :=
  if f.home then (pal, #[]) else
  (if f.flip then { pal with entries := pal.entries.filter (·.1 != .role .alertMark) } else pal).carried
    f used

public theorem Palette.view_home (pal : Palette) (f : SchemeFrame) (h : f.home = true) :
    pal.view f = (pal, #[]) := by
  unfold Palette.view
  simp [h]

/-- A role's colour in a scheme as the scheme ships it. -/
public def Design.inScheme (pal : Palette) (f : SchemeFrame) (r : Role) : Option Color :=
  Design.at (pal.view f).1 f.scheme r

public theorem Design.light_print_exact (doc pal : Palette) (r : Role) (c : Color) (stage : Bool)
    (hd : doc.darkPage = false) (h : Design.declared? pal r = some c) :
    Design.inScheme pal (doc.frame .print stage) r = some c ∧
      Design.inScheme pal (doc.frame .light stage) r = some c := by
  have hp : (doc.frame .print stage).home = true := Palette.frame_print_home doc stage
  have hl : (doc.frame .light stage).home = true := by
    simp [Palette.frame, SchemeFrame.home, hd, Scheme.onDark, Scheme.more]
  have sp : (doc.frame .print stage).scheme = .print := by simp [Palette.frame]
  have sl : (doc.frame .light stage).scheme = .light := by simp [Palette.frame]
  unfold Design.inScheme
  rw [Palette.view_home pal _ hp, Palette.view_home pal _ hl, sp, sl]
  exact ⟨Design.at_declared pal .print r c h, Design.at_declared pal .light r c h⟩

end DesignResolve

/-- The colour schemes a document asks its page to offer: its
`\output{ schemes = … }`, else its class's. -/
public def Doc.requestedSchemes (doc : Doc) : List Scheme :=
  match doc.output.schemes with
  | some l => l.toList
  | none => match doc.docClass.record.schemes with
    | .every => Scheme.all
    | .own =>
      let home := doc.palette.homeScreen
      [.print, home, if home == .dark then .darkMore else .lightMore]

/-- The body's declaration projected from the resolved design. -/
@[expose] public def Design.titledBody (d : Design) : TitledKind → SurfaceLook
  | .block | .box => d.blockBody
  | .alert => d.alertBody
  | .example => d.exampleBody

public theorem Design.titledBody_projects (pal : Palette) (kind : TitledKind) :
    (Design.ofPalette pal).titledBody kind = titledBodyLook pal kind := by
  cases kind <;> rfl

/-- A titled body's paint: its declared channels over the enclosing pair. -/
@[expose] public def Design.titledBodyPaint (d : Design) (kind : TitledKind)
    (parent : ColorPair) : ColorPair :=
  (d.titledBody kind).resolve parent

public theorem Design.titledBodyPaint_contract (d : Design) (kind : TitledKind)
    (parent : ColorPair) :
    (d.titledBodyPaint kind parent).bg = (d.titledBody kind).bg.getD parent.bg := by
  rfl

/-- The ground a frame's body stands on when the frame declares one of its
own: a title page's; `none` on the page's own ground. -/
@[expose] public def titleGroundOf (pal : Palette) (valign : VAlign) : Option Color :=
  if valign matches .golden then (Design.ofPalette pal).titlepage.map (·.bg) else none

/-- The ground a frame's pages stand on, off the palette in force where the frame stands. -/
public def frameGroundOf (pal : Palette) (standout : Bool) (valign : VAlign) : Option Color :=
  if standout then some (Design.ofPalette pal).standout.bg
  else (titleGroundOf pal valign).orElse fun _ => Design.declared? pal .page

/-- The document's resolved design: `ofPalette` over its palette, with the
two declarations a palette does not carry. -/
@[expose] public def Design.ofDoc (doc : Doc) : Design :=
  { Design.ofPalette doc.palette with
    -- Fallback: `progressbar linewidth=1pt`, the outer theme's own default.
    progressheight := (doc.tokens.find? "progressheight").getD
      { width := Dim.SymLength.ofLength (Dim.pt 1) }
    styles := doc.styles }

/-- The footer look of a frame: a restored standout footer stands on the
standout canvas in its foreground. -/
public def Design.frameFootLook (d : Design) (standout : Bool) : TitledLook :=
  if standout then { fg := d.standout.fg, bar := some d.standout.bg } else d.footline

public theorem Design.standoutFootLook_projects (d : Design) :
    (d.frameFootLook true).fg = d.standout.fg ∧
    (d.frameFootLook true).bar = some d.standout.bg := ⟨rfl, rfl⟩

public theorem frametitle_agree (doc : Doc) :
    (Design.ofDoc doc).frametitle = (Design.ofPalette doc.palette).frametitle := by rfl

public theorem beamerColors_agree (doc : Doc) :
    ((Design.ofDoc doc).framesubtitle, (Design.ofDoc doc).sectionTitle,
      (Design.ofDoc doc).sectionProgress, (Design.ofDoc doc).footline) =
    ((Design.ofPalette doc.palette).framesubtitle, (Design.ofPalette doc.palette).sectionTitle,
      (Design.ofPalette doc.palette).sectionProgress, (Design.ofPalette doc.palette).footline) := by rfl

public theorem titlepage_agree (doc : Doc) :
    (Design.ofDoc doc).titlepage = (Design.ofPalette doc.palette).titlepage := by rfl

public theorem Design.titleGround_exact (pal : Palette) :
    (Design.ofPalette pal).titlepage.map (·.bg) = Design.declared? pal .titlePageGround := by
  have h : Design.at pal .print .titlePageGround = Design.declared? pal .titlePageGround := by
    rw [Design.resolve_unfold_exact]
    cases Design.declared? pal .titlePageGround <;> rfl
  unfold Design.ofPalette Design.resolve
  simp only [h]
  cases Design.declared? pal .titlePageGround <;> rfl

/-- Per-element style, total: the empty style is the default. -/
public def Design.style (d : Design) (element : String) : ElementStyle :=
  (d.styles.find? element).getD {}

/-- The palette keys the registry resolves. -/
public def Design.consumedRoles : List String :=
  Role.all.filterMap (·.row.key)

/-- How covering paints: the per-colour cover, and a declared constant cover for runs with no
colour of their own. -/
public structure Cover where
  of : Color → Color
  covered : Option Color
  /-- A share of none: a pending step is invisible, as `\visible` sets it, its place kept. -/
  hidden : Bool

/-- The cover of a run with no colour of its own, set in `ink`. -/
@[expose] public def Cover.plainOf (c : Cover) (ink : Color) : Color := c.covered.getD (c.of ink)

/-- The paint of ink that keeps its place and ships nothing, its CMYK rider outside every
document's range. -/
@[expose] public def hiddenPaint : Color :=
  { r := 0, g := 0, b := 0, cmyk := some (1001, 1001, 1001, 1001) }

/-- Covering: the per-colour cover at the design's fraction toward its surface; a share of none
hides the step instead, as beamer's `invisible` does. -/
public def Design.cover (d : Design) : Cover :=
  if d.coveredFraction == 0 then { of := fun _ => hiddenPaint, covered := none, hidden := true }
  else { of := Oklab.coverOver d.coveredFraction (Oklab.labOf d.bg), covered := d.covered, hidden := false }

/-- The cover a pending step starting under this palette takes. -/
@[expose] public def Palette.cover (p : Palette) : Cover := (Design.ofPalette p).cover

public theorem Design.cover_hidden (d : Design) : d.cover.hidden = (d.coveredFraction == 0) := by
  unfold Design.cover
  split <;> simp_all

/-- The cover of the design's own ink, which a run with no colour of its own takes. -/
@[expose] public def Design.inkCover (d : Design) : Color := d.cover.plainOf d.fg

/-- What the dimming walk reads where it stands: the cover a step starting here takes, and the ink
a run with no colour of its own sets in. -/
public structure DimHere where
  cover : Cover
  ink : Color
  /-- `cover.plainOf ink`, read once. -/
  plain : Color

/-- The dimming walk's reading of a cover where runs set in `ink`. -/
@[expose] public def DimHere.under (cover : Cover) (ink : Color) : DimHere :=
  { cover, ink, plain := cover.plainOf ink }

/-- The dimming walk's reading under the palette in force. -/
@[expose] public def DimHere.of (p : Palette) : DimHere := DimHere.under p.cover (Design.printInk p)

/-- The paint a pending inline step's runs take: the cover of the colour in force, or of the ink. -/
@[expose] public def DimHere.paint (h : DimHere) (own : Option Color) : Color :=
  match own with
  | some c => h.cover.of c
  | none => h.plain

/-- The paint of a run with no colour of its own in a step covered by the reading `region`, set in
the ink in force at `here`. -/
@[expose] public def DimHere.plainUnder (region here : DimHere) : Color :=
  if region.ink = here.ink then region.plain else region.cover.plainOf here.ink

/-- One component of a numbered overlay: a number, a closed range or an open range. -/
private def overlayInterval (w : String) : Option (Nat × Option Nat) := do
  match w.trimAscii.toString.splitOn "-" with
  | [n] =>
    let n ← n.toNat?
    pure (n, some n)
  | [a, b] =>
    if a.isEmpty && b.isEmpty then none else do
      let n ← if a.isEmpty then some 1 else a.toNat?
      if b.isEmpty then pure (n, none) else do
        let u ← b.toNat?
        pure (n, some u)
  | _ => none

/-- The reader for every numbered overlay entry: a comma is union, and an
unsupported component refuses the whole selector. -/
public def overlayRange (w : String) : Option OverlaySpec := do
  if !(w.startsWith "<" && w.endsWith ">" && w.length ≥ 3) then none else do
    let ranges ← (((w.drop 1).dropEnd 1).toString.splitOn ",").mapM overlayInterval
    match ranges with
    | (n, last) :: more => pure { first := n, last := last, more := more }
    | [] => none

/-- The single-interval projection of `OverlaySpec.showsFirst`. -/
@[expose] public def altShowsFirst (n : Nat) (last : Option Nat) (k : Nat) : Bool :=
  (OverlaySpec.mk n last [] false).showsFirst k

public theorem altShowsFirst_id (n : Nat) (last : Option Nat) :
    altShowsFirst n last 1 = true :=
  OverlaySpec.showsFirst_id _

/-- Whether the group stored first is the one a pending step inks. -/
public def altFirstWhenPending (n : Nat) (last : Option Nat) : Bool :=
  (OverlaySpec.mk n last [] false).pending 1

public theorem altShowsFirst_side (n : Nat) (last : Option Nat) (k : Nat) :
    altShowsFirst n last k = (stepPending n last k == altFirstWhenPending n last) := by
  simp [altShowsFirst, altFirstWhenPending, OverlaySpec.showsFirst]

mutual

/-- The last step a frame's body reaches; a frame nested below another block keeps one page. -/
public def maxStepBlocks (xs : Array Block) : Nat := maxStepBlockList xs.toList

private def maxStepBlockList : List Block → Nat
  | [] => 1
  | b :: rest => max (maxStepBlock b) (maxStepBlockList rest)

/-- The `1` arms are furniture and the note side channel, outside the overlay model. -/
private def maxStepBlock : Block → Nat
  | .para content => maxStepInlines content
  | .equation _ content => maxStepInlines content
  | .list _ _ items => maxStepItems items.toList
  | .center body => maxStepBlockList body.toList
  | .ragged _ body => maxStepBlockList body.toList
  | .quote _ body => maxStepBlockList body.toList
  | .lines ls => maxStepLaid ls.toList
  | .abstract body => maxStepBlockList body.toList
  | .titled _ title body => max (maxStepInlines title) (maxStepBlockList body.toList)
  | .disclosure summary _ body => max (maxStepInlines summary) (maxStepBlockList body.toList)
  | .role _ body => maxStepBlockList body.toList
  | .link _ body => maxStepBlockList body.toList
  | .spaced _ body => maxStepBlockList body.toList
  | .columns cols => maxStepColumns cols.toList
  | .onSteps spec body => max (spec.maxStep) (maxStepBlockList body.toList)
  | .altSteps spec firstPage otherPage =>
    max (spec.maxStep)
      (max (maxStepBlockList firstPage.toList) (maxStepBlockList otherPage.toList))
  | .only _ body => maxStepBlockList body.toList
  | .nav _ body => maxStepBlockList body.toList
  | .section _ _ _ title => maxStepInlines title
  | .verbatim _ _ spec => (spec.caption.map fun (_, cap) => maxStepInlines cap).getD 1
  | .algorithm _ _ lines => maxStepAlgLines lines.toList
  | .note _ => 1
  | .frame _ _ _ _ _ => 1
  | .framefoot _ => 1
  | .setPalette _ => 1
  | .setTokens _ => 1
  | .pagebreak => 1
  | .logo _ => 1
  | .rule _ _ _ => 1
  | .picture _ => 1
  | .table _ _ _ rows _ _ => maxStepTableRows rows.toList
  | .float _ _ _ body cap => max (maxStepInlines cap) (maxStepBlockList body.toList)
  | .bibliography _ _ _ => 1
  | .contents _ entries => entries.foldl (fun n e => max n (maxStepInlines e.title)) 1

private def maxStepTableRows : List (Array (Array Block)) → Nat
  | [] => 1
  | row :: rest => max (maxStepItems row.toList) (maxStepTableRows rest)

private def maxStepItems : List (Array Block) → Nat
  | [] => 1
  | item :: rest => max (maxStepBlockList item.toList) (maxStepItems rest)

private def maxStepColumns : List (BoxWidth × Array Block) → Nat
  | [] => 1
  | (_, body) :: rest => max (maxStepBlockList body.toList) (maxStepColumns rest)

private def maxStepAlgLines : List AlgLine → Nat
  | [] => 1
  | l :: rest =>
    max (max (maxStepInlineList l.content.toList)
      (match l.comment with
       | some c => maxStepInlineList c.toList
       | none => 1))
      (maxStepAlgLines rest)

private def maxStepLaid : List LaidLine → Nat
  | [] => 1
  | l :: rest => max (maxStepInlineList l.content.toList) (maxStepLaid rest)

public def maxStepInlines (xs : Array Inline) : Nat := maxStepInlineList xs.toList

private def maxStepInlineList : List Inline → Nat
  | [] => 1
  | x :: rest => max (maxStepInline x) (maxStepInlineList rest)

private def maxStepInline : Inline → Nat
  | .styled _ body => maxStepInlineList body.toList
  | .colored _ _ body => maxStepInlineList body.toList
  | .located _ body => maxStepInlineList body.toList
  | .role _ body => maxStepInlineList body.toList
  | .link _ body => maxStepInlineList body.toList
  | .decorated _ body | .boxed _ body => maxStepInlineList body.toList
  | .footnote _ body => maxStepInlineList body.toList
  | .cited _ _ ink => maxStepInlineList ink.toList
  | .onSteps spec body => max (spec.maxStep) (maxStepInlineList body.toList)
  | .altSteps spec firstPage otherPage =>
    max (spec.maxStep)
      (max (maxStepInlineList firstPage.toList) (maxStepInlineList otherPage.toList))
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ | .cite _ _ => 1

end

/-- The declared overlay extent of a top-level frame's title and body, or zero
for any other block. -/
public def frameSteps (b : Block) : Nat :=
  if let .frame title _ _ _ body := b then
    max 1 (max (maxStepInlines title) (maxStepBlocks body))
  else 0

public theorem frameSteps_covers (title : Array Inline) (standout : Bool)
    (valign : VAlign) (breakable : Bool) (body : Array Block) :
    maxStepInlines title ≤ frameSteps (.frame title standout valign breakable body) ∧
    maxStepBlocks body ≤ frameSteps (.frame title standout valign breakable body) := by
  simp only [frameSteps]
  constructor <;> omega

/-- Alternation groups no step of their own frame inks, counted over the
document's frames, the handout's under a selector selecting no step aside; zero is the
contract. -/
public def altUnreachable (doc : Doc) : Nat :=
  doc.body.foldl (init := 0) fun n b =>
    match b with
    | .frame _ _ _ _ body =>
      let steps := frameSteps b
      let reached (spec : OverlaySpec) (o : Bool) : Bool :=
        spec.reachesOther steps || o || (spec.selectedSteps steps).isEmpty
      n + foldBlocks
        (fun k blk => match blk with
          | .altSteps spec _ o => if reached spec o.isEmpty then k else k + 1
          | .para _ | .section _ _ _ _ | .list _ _ _ | .center _ | .ragged _ _
          | .spaced _ _ | .role _ _ | .link _ _ | .quote _ _ | .lines _ | .abstract _
          | .titled _ _ _ | .disclosure _ _ _ | .equation _ _ | .verbatim _ _ _ | .algorithm _ _ _
          | .columns _ | .onSteps _ _ | .note _ | .only _ _ | .nav _ _ | .logo _
          | .pagebreak | .frame _ _ _ _ _ | .framefoot _ | .setPalette _ | .setTokens _
          | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ | .float _ _ _ _ _
          | .bibliography _ _ _ | .contents _ _ => k)
        (fun k x => match x with
          | .altSteps spec _ o => if reached spec o.isEmpty then k else k + 1
          | .text _ | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _
          | .located _ _ | .role _ _ | .link _ _ | .label _ | .ref _ _ _ _
          | .decorated _ _ | .boxed _ _ | .fill | .hspace _ _ | .rule _ _ _
          | .pageNumber | .pageCount | .linebreak _ | .strut _ | .italicCorr _
          | .onSteps _ _ | .image _ _ _ | .icon _ _ | .cite _ _ | .cited _ _ _
          | .footnote _ _ => k)
        0 body
    | .para _ | .section _ _ _ _ | .list _ _ _ | .center _ | .ragged _ _
    | .spaced _ _ | .role _ _ | .link _ _ | .quote _ _ | .lines _ | .abstract _
    | .titled _ _ _ | .disclosure _ _ _ | .equation _ _ | .verbatim _ _ _ | .algorithm _ _ _
    | .columns _ | .onSteps _ _ | .altSteps _ _ _ | .note _ | .only _ _
    | .nav _ _ | .logo _ | .pagebreak | .framefoot _ | .setPalette _ | .setTokens _
    | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ | .float _ _ _ _ _
    | .bibliography _ _ _ | .contents _ _ => n

/-- A decoration as a covered step shows it: a mark quieted by the cover, as
the text it stands behind is; a rule as it is, in the run's covered ink. -/
private def Decoration.dimmed (d : Decoration) (pend : Option DimHere) : Decoration :=
  match d with
  | .underline => .underline
  | .lineThrough => .lineThrough
  | .highlight c nm => match pend with
    | some cv => .highlight (cv.cover.of c) none
    | none => .highlight c nm

/-- A box's declared paints under a cover, as a mark's is. -/
private def InlineBox.dimmed (b : InlineBox) (pend : Option DimHere) : InlineBox :=
  match pend with
  | some cv =>
    { b with ground := b.ground.map fun (c, _) => (cv.cover.of c, none)
             frame := b.frame.map fun
               | .ink => .ink
               | .color c _ => .color (cv.cover.of c) none }
  | none => b

mutual

/-- One overlay walk over inline content in two modes: off, step `k` of the frame's overlay,
covering what lies outside its range; on (`pend`), everything covered by the cover of the step it
lies in; only colours change, `own` the colour in force. -/
private def dimInlineList (k : Nat) (pend : Option DimHere) (here : DimHere) (own : Option Color)
    (out : Array Inline) : List Inline → Array Inline
  | [] => out
  | x :: rest =>
    dimInlineList k pend here own (out.push (dimInline k pend here own x)) rest

private def dimInline (k : Nat) (pend : Option DimHere) (here : DimHere) (own : Option Color) :
    Inline → Inline
  | .styled st body => .styled st (dimInlineList k pend here own #[] body.toList)
  | .colored c nm body =>
    match pend with
    | some cv => .colored (cv.cover.of c) none (dimInlineList k pend here (some c) #[] body.toList)
    | none => .colored c nm (dimInlineList k none here (some c) #[] body.toList)
  | .located n body => .located n (dimInlineList k pend here own #[] body.toList)
  | .role n body => .role n (dimInlineList k pend here own #[] body.toList)
  | .link u body => .link u (dimInlineList k pend here own #[] body.toList)
  -- a covered mark is quieted with the text it stands behind
  | .decorated kind body =>
    .decorated (kind.dimmed pend) (dimInlineList k pend here own #[] body.toList)
  | .boxed b body => .boxed (b.dimmed pend) (dimInlineList k pend here own #[] body.toList)
  -- A pending inline step brings its own cover; a covered paragraph's comes from its block.
  | .onSteps spec body =>
    if here.cover.hidden then
      .onSteps { spec with invisible := true } (dimInlineList k pend here own #[] body.toList)
    else if !spec.invisible && pend.isNone && spec.pending k then
      .onSteps spec #[.colored (here.paint own) none
        (dimInlineList k (some here) here own #[] body.toList)]
    else .onSteps spec (dimInlineList k pend here own #[] body.toList)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (dimInlineList k pend here own #[] firstPage.toList)
      (dimInlineList k pend here own #[] otherPage.toList)
  | .text s => .text s
  | .math d src => .math d src
  -- Formula and image nodes stay whole: the backends dim them.
  | .formula d src body => .formula d src body
  | .image src size alt => .image src size alt
  | .icon s l => .icon s l
  | .label k => .label k
  | .ref k p t tg => .ref k p t tg
  | .fill => .fill
  | .hspace g keep => .hspace g keep
  | .rule w h r => .rule w h r
  | .strut h => .strut h
  | .italicCorr m => .italicCorr m
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak e => .linebreak e
  | .cite t keys => .cite t keys
  | .cited t keys ink => .cited t keys (dimInlineList k pend here own #[] ink.toList)
  | .footnote n body => .footnote n (dimInlineList k pend here own #[] body.toList)

end

/-- A run a pending step covers under `cv`: its runs with no colour of their own in the cover of
the ink. -/
private def coverRun (k : Nat) (cv : DimHere) (here : DimHere) (xs : Array Inline) : Array Inline :=
  #[.colored (cv.plainUnder here) none (dimInlineList k (some cv) here none #[] xs.toList)]

/-- Inline content as step `k` shows it: covered whole inside a pending step, a description's
run-in label covered in its own role so it runs in as it does shown, else stepwise. -/
private def dimContent (k : Nat) (pend : Option DimHere) (here : DimHere) (xs : Array Inline) :
    Array Inline :=
  match pend with
  | some cv =>
    match descLabel? xs with
    | some (label, rest) =>
      let shown := coverRun k cv here rest
      #[.role descLabelRole (coverRun k cv here label)] ++ shown
    | none => coverRun k cv here xs
  | none => dimInlineList k none here none #[] xs.toList

/-- `dimContent` for content an empty run leaves as it stands. -/
private def dimFilled (k : Nat) (pend : Option DimHere) (here : DimHere) (xs : Array Inline) :
    Array Inline :=
  if pend.isSome && xs.isEmpty then xs else dimContent k pend here xs

private def dimAlgLines (k : Nat) (pend : Option DimHere) (here : DimHere) (out : Array AlgLine) :
    List AlgLine → Array AlgLine
  | [] => out
  | l :: rest =>
    dimAlgLines k pend here (out.push
      { depth := l.depth
        kind := l.kind
        content := dimFilled k pend here l.content
        comment := l.comment.map (dimFilled k pend here) }) rest

private def dimLaid (k : Nat) (pend : Option DimHere) (here : DimHere) (out : Array LaidLine) :
    List LaidLine → Array LaidLine
  | [] => out
  | l :: rest =>
    dimLaid k pend here (out.push { depth := l.depth, content := dimFilled k pend here l.content }) rest

mutual

/-- One overlay walk in two modes: off, step `k` covering what lies outside its range; on
(`pend`), everything covered by the cover read where its step starts, `here` the palette in force,
in flow order, which the walk returns. -/
private def dimBlockList (k : Nat) (pend : Option DimHere) (here : DimHere) (out : Array Block) :
    List Block → Array Block × DimHere
  | [] => (out, here)
  | b :: rest =>
    let r := dimBlock k pend here b
    dimBlockList k pend r.2 (out.push r.1) rest
termination_by structural bs => bs

private def dimBlock (k : Nat) (pend : Option DimHere) (here : DimHere) : Block → Block × DimHere
  | .para content => (.para (dimContent k pend here content), here)
  | .equation num content => (.equation num (dimContent k pend here content), here)
  | .list o s items =>
    let r := dimItems k pend here #[] items.toList
    (.list o s r.1, r.2)
  | .center body =>
    let r := dimBlockList k pend here #[] body.toList
    (.center r.1, r.2)
  | .ragged s body =>
    let r := dimBlockList k pend here #[] body.toList
    (.ragged s r.1, r.2)
  | .quote q body =>
    let r := dimBlockList k pend here #[] body.toList
    (.quote q r.1, r.2)
  | .lines ls => (.lines (dimLaid k pend here #[] ls.toList), here)
  | .abstract body =>
    let r := dimBlockList k pend here #[] body.toList
    (.abstract r.1, r.2)
  | .titled kind title body =>
    let r := dimBlockList k pend here #[] body.toList
    (.titled kind (dimInlineList k pend here none #[] title.toList) r.1, r.2)
  | .disclosure summary expanded body =>
    let r := dimBlockList k pend here #[] body.toList
    (.disclosure (dimInlineList k pend here none #[] summary.toList) expanded r.1, r.2)
  | .role n body =>
    let r := dimBlockList k pend here #[] body.toList
    (.role n r.1, r.2)
  | .link target body =>
    let r := dimBlockList k pend here #[] body.toList
    (.link target r.1, r.2)
  | .spaced g body =>
    let r := dimBlockList k pend here #[] body.toList
    (.spaced g r.1, r.2)
  | .columns cols =>
    let r := dimColumns k pend here #[] cols.toList
    (.columns r.1, r.2)
  -- A step covers by the cover read where it starts, one inside a covered step by the outer's.
  | .onSteps spec body =>
    let opens := !here.cover.hidden && !spec.invisible && spec.pending k
    let r := dimBlockList k (if pend.isNone && opens then some here else pend) here #[]
      body.toList
    (.onSteps (if here.cover.hidden then { spec with invisible := true } else spec) r.1, r.2)
  | .altSteps spec firstPage otherPage =>
    let f := dimBlockList k pend here #[] firstPage.toList
    let o := dimBlockList k pend here #[] otherPage.toList
    (.altSteps spec f.1 o.1, if spec.showsFirst k then f.2 else o.2)
  | .only targets body =>
    let r := dimBlockList k pend here #[] body.toList
    (.only targets r.1, r.2)
  | .nav spec body =>
    let r := dimBlockList k pend here #[] body.toList
    (.nav spec r.1, r.2)
  | .section l st num title => (.section l st num (dimInlineList k pend here none #[] title.toList), here)
  | .verbatim c s spec =>
    (.verbatim (match pend with
        | some cv => some (cv.plainUnder here)
        | none => c) s
      { spec with caption := spec.caption.map fun (n, cap) =>
          (n, dimInlineList k pend here none #[] cap.toList) }, here)
  | .algorithm n sm lines => (.algorithm n sm (dimAlgLines k pend here #[] lines.toList), here)
  | .note body => (.note body, here)
  | .frame t st v br body => (.frame t st v br body, here)
  | .framefoot content => (.framefoot content, here)
  | .setPalette pal => (.setPalette pal, DimHere.of pal)
  | .setTokens tk => (.setTokens tk, here)
  | .pagebreak => (.pagebreak, here)
  | .logo content => (.logo content, here)
  | .rule c nm th => (.rule c nm th, here)
  | .picture p =>
    (.picture (match pend with
      | some cv => p.recolor cv.cover.of
      | none => p), here)
  | .table cols pl pr rows rules spans =>
    (.table cols pl pr (dimTableRows k pend here #[] rows.toList) rules spans, here)
  | .float fk num ca body caption =>
    let r := dimBlockList k pend here #[] body.toList
    (.float fk num ca r.1 (dimFilled k pend here caption), r.2)
  | .bibliography src style items => (.bibliography src style items, here)
  | .contents spec entries =>
    (.contents spec (entries.map fun e => { e with title := dimFilled k pend here e.title }), here)
termination_by structural b => b

private def dimItems (k : Nat) (pend : Option DimHere) (here : DimHere) (out : Array (Array Block)) :
    List (Array Block) → Array (Array Block) × DimHere
  | [] => (out, here)
  | item :: rest =>
    let r := dimBlockList k pend here #[] item.toList
    dimItems k pend r.2 (out.push r.1) rest
termination_by structural items => items

private def dimColumns (k : Nat) (pend : Option DimHere) (here : DimHere)
    (out : Array (BoxWidth × Array Block)) :
    List (BoxWidth × Array Block) → Array (BoxWidth × Array Block) × DimHere
  | [] => (out, here)
  | (w, body) :: rest =>
    let r := dimBlockList k pend here #[] body.toList
    dimColumns k pend r.2 (out.push ({ w with box := w.box.map (·.dimmed pend) }, r.1)) rest
termination_by structural cols => cols

private def dimTableRows (k : Nat) (pend : Option DimHere) (here : DimHere)
    (out : Array (Array (Array Block))) :
    List (Array (Array Block)) → Array (Array (Array Block))
  | [] => out
  | row :: rest =>
    dimTableRows k pend here (out.push (dimItems k pend here #[] row.toList).1) rest
termination_by structural rows => rows

end

/-- The frame's body as step `k` of its overlay shows it, from the reading of the palette in force
where it opens. -/
public def dimBlocks (here : DimHere) (k : Nat) (xs : Array Block) : Array Block :=
  (dimBlockList k none here #[] xs.toList).1

/-- Inline content a pending step covers under `cv`, as `dimBlocks` covers a pending paragraph set
in `ink`. -/
public def coverInlines (cv : Cover) (ink : Color) (xs : Array Inline) : Array Inline :=
  coverRun 1 (DimHere.under cv ink) (DimHere.under cv ink) xs

/-- The conservation shape: `f` leaves the census fixed. -/
@[expose] public def Conserves (census : α → β) (f : α → α) : Prop :=
  ∀ x, census (f x) = census x

public theorem wrap_text (w : Array Inline → Inline)
    (hw : ∀ xs, plainTextOne (w xs) = plainText xs) :
    Conserves plainText (fun xs => #[w xs]) := fun xs => by
  simp [plainText, plainTextList, hw]

public theorem located_text (span : Span) :
    Conserves plainText (fun xs => #[.located span xs]) :=
  wrap_text (.located span) fun _ => rfl

/-- Wrap inline content in a language switch, as `\foreignlanguage`,
`\selectlanguage` and `otherlanguage` do. -/
public def langWrap (tag : String) (xs : Array Inline) : Array Inline :=
  #[.styled (.lang tag) xs]

public theorem langWrap_exact (tag : String) (xs : Array Inline) :
    langWrap tag xs = #[.styled (.lang tag) xs] := by
  rfl

public theorem langWrap_text (tag : String) :
    Conserves plainText (langWrap tag) :=
  wrap_text (.styled (.lang tag)) fun _ => rfl

/-- The style a disclosure's summary sets in: bold, as a titled block's title is. -/
public def disclosureSummaryStyle : Style := .bold

/-- A disclosure's summary as paper sets it, the line above its body; an empty
summary sets nothing. -/
public def disclosureSummary (summary : Array Inline) : Array Inline :=
  if summary.isEmpty then #[] else #[.styled disclosureSummaryStyle summary]

public theorem disclosureSummary_text : Conserves plainText disclosureSummary := fun xs => by
  unfold disclosureSummary
  split
  · rename_i h
    rw [Array.isEmpty_iff.mp h]
  · exact wrap_text (.styled disclosureSummaryStyle) (fun _ => rfl) xs

/-- Wrap inline content as a footnote's body: what `\footnote` becomes. -/
public def footnoteWrap (num : Option Nat) (xs : Array Inline) : Array Inline :=
  #[.footnote num xs]

public theorem footnoteWrap_text (num : Option Nat) :
    Conserves plainText (footnoteWrap num) :=
  wrap_text (.footnote num) fun _ => rfl

public theorem Styles_text (s : Styles) (kind : String) :
    Conserves plainText (s.linkInk kind) := by
  intro body
  unfold Styles.linkInk
  match (s.find? kind).bind (·.color) with
  | none => rfl
  | some (c, n) => exact wrap_text (Inline.colored c n) (fun _ => rfl) body

/-- A listing caption's census text, `""` when none is declared. -/
@[expose] public def ListingSpec.capText (spec : ListingSpec) : String :=
  match spec.caption with
  | some (_, cap) => plainText cap
  | none => ""

/-- The algorithm lines' census: each line's declared content, then its
comment; generated keywords never count. -/
@[expose] public def algLineText (acc : String) : List AlgLine → String
  | [] => acc
  | l :: rest =>
    algLineText (match l.comment with
      | some c =>
        let pc := plainText c
        (acc ++ plainText l.content) ++ pc
      | none => acc ++ plainText l.content) rest

/-- A laid-out paragraph's census: each line's content, in reading order. -/
@[expose] public def laidText (acc : String) : List LaidLine → String
  | [] => acc
  | l :: rest => laidText (acc ++ plainText l.content) rest

mutual

/-- The characters of block content with every mark stripped, the block companion of `plainText`. -/
@[expose] public def blocksText (xs : Array Block) : String := blockTextList "" xs.toList

@[expose] public def blockTextList (acc : String) : List Block → String
  | [] => acc
  | b :: rest => blockTextList (blockTextOne acc b) rest

@[expose] public def blockTextOne (acc : String) : Block → String
  | .para content =>
    let t := plainText content
    acc ++ t
  | .equation number content =>
    let t := plainText content
    let n := plainText number
    acc ++ t ++ n
  | .section _ _ _ title =>
    let t := plainText title
    acc ++ t
  | .list _ _ items => blockTextItems acc items.toList
  | .center body => blockTextList acc body.toList
  | .ragged _ body => blockTextList acc body.toList
  | .quote _ body => blockTextList acc body.toList
  | .lines ls => laidText acc ls.toList
  | .abstract body => blockTextList acc body.toList
  | .titled _ title body => blockTextList (acc ++ plainText title) body.toList
  | .disclosure title _ body => blockTextList (acc ++ plainText title) body.toList
  | .role _ body => blockTextList acc body.toList
  | .link _ body => blockTextList acc body.toList
  | .spaced _ body => blockTextList acc body.toList
  | .columns cols => blockTextColumns acc cols.toList
  | .onSteps _ body => blockTextList acc body.toList
  | .altSteps _ firstPage otherPage =>
    blockTextList (blockTextList acc firstPage.toList) otherPage.toList
  -- A conditional's content counts: the census reads declared content; `keepFor` drops it.
  | .only _ body => blockTextList acc body.toList
  | .nav _ body => blockTextList acc body.toList
  | .note body => blockTextList acc body.toList
  | .verbatim _ s spec => acc ++ spec.capText ++ s
  | .algorithm _ _ lines => algLineText acc lines.toList
  | .logo content => acc ++ plainText content
  | .frame title _ _ _ body => blockTextList (acc ++ plainText title) body.toList
  | .framefoot content => acc ++ plainText content
  | .setPalette _ => acc
  | .setTokens _ => acc
  | .pagebreak => acc
  | .rule _ _ _ => acc
  | .picture _ => acc
  | .table _ _ _ rows _ _ => blockTextTableRows acc rows.toList
  | .float _ _ _ body caption => blockTextList (acc ++ plainText caption) body.toList
  | .bibliography _ _ items => blockTextBibItems acc items.toList
  | .contents _ entries => blockTextContentsEntries acc entries.toList

@[expose] public def blockTextBibItems (acc : String) : List BibItem → String
  | [] => acc
  | item :: rest => blockTextBibItems (acc ++ plainText item.content) rest

@[expose] public def blockTextContentsEntries (acc : String) : List ContentsEntry → String
  | [] => acc
  | e :: rest => blockTextContentsEntries (acc ++ plainText e.title) rest


@[expose] public def blockTextItems (acc : String) : List (Array Block) → String
  | [] => acc
  | item :: rest => blockTextItems (blockTextList acc item.toList) rest

@[expose] public def blockTextColumns (acc : String) : List (BoxWidth × Array Block) → String
  | [] => acc
  | (_, body) :: rest => blockTextColumns (blockTextList acc body.toList) rest

@[expose] public def blockTextTableRows (acc : String) : List (Array (Array Block)) → String
  | [] => acc
  | row :: rest => blockTextTableRows (blockTextItems acc row.toList) rest

end

public theorem blockTextList_append (a b : List Block) (acc : String) :
    blockTextList acc (a ++ b) = blockTextList (blockTextList acc a) b := by
  induction a generalizing acc with
  | nil => simp [blockTextList]
  | cons x xs ih => simp [blockTextList, ih]

public theorem titled_text (acc : String) (kind : TitledKind) (title : Array Inline)
    (body : Array Block) :
    blockTextOne acc (.titled kind title body)
      = blockTextList (acc ++ plainText title) body.toList := by rfl

/-- A declared vertical skip standing on its own, as `\vskip` does. -/
private def gapBlock (g : Dim.SymGlue) : Block := .spaced (Sourced.bare g) #[]

/-- A declared bar with the skips beside it; no declared weight, no ink. -/
private def barSide (ink : Color × Option ColorRef)
    (before after : Dim.SymGlue) : Option Dim.SymGlue → Array Block
  | some w => #[gapBlock before, .rule ink.1 ink.2 (Sourced.bare w), gapBlock after]
  | none => #[]

/-- One title bracketed by its declared bars, appended to the walk's accumulator. -/
private def titleStep (st : ElementStyle) (ink : Color × Option ColorRef)
    (out : Array Block) (starred : Bool) (num : Option String)
    (title : Array Inline) : Array Block :=
  let above := barSide ink (st.ruleAboveSkip.getD titleBarSkip)
    (st.ruleAboveGap.getD titleBarGap) st.ruleAbove
  let below := barSide ink (st.ruleBelowGap.getD titleBarGap)
    (st.ruleBelowSkip.getD titleBarSkip) st.ruleBelow
  ((out ++ above).push (.section 0 starred num title)) ++ below

/-- Bracket a title block's level-0 heading with its declared bars, each
standing its gap from the type. -/
public def titleBarsList (st : ElementStyle) (ink : Color × Option ColorRef)
    (out : Array Block) (done : Bool) : List Block → Array Block
  | [] => out
  | b :: rest =>
    match b, done with
    | .section 0 starred num title, false =>
      titleBarsList st ink (titleStep st ink out starred num title) true rest
    | b, _ => titleBarsList st ink (out.push b) done rest

public def titleBars (st : ElementStyle) (ink : Color × Option ColorRef)
    (blocks : Array Block) : Array Block :=
  if st.ruleAbove.isNone && st.ruleBelow.isNone then blocks
  else titleBarsList st ink #[] false blocks.toList

private theorem blocksText_push (out : Array Block) (b : Block) :
    blocksText (out.push b) = blockTextOne (blocksText out) b := by
  simp [blocksText, Array.toList_push, blockTextList_append, blockTextList]

public theorem inParagraph_text (acc : String) (b : Block) :
    blockTextOne acc (inParagraph b) = blockTextOne acc b := by
  unfold inParagraph
  cases b.partopsepEnv <;> simp [blockTextOne, blockTextList]

public theorem boxedBlocks_text (b : InlineBox) : Conserves blocksText (boxedBlocks b) := by
  intro body
  unfold boxedBlocks
  dsimp only
  generalize hk : body.size - closingEpochs body = k
  have hsplit : body.extract 0 k ++ body.extract (body.extract 0 k).size body.size = body := by
    have hk' : k ≤ body.size := by omega
    apply Array.toList_inj.mp
    simp [Nat.min_eq_left hk', Nat.max_eq_right hk']
  split
  · next cols h =>
    split
    · next w inner h2 =>
      split
      · have hcore : body.extract 0 k = #[.columns #[(w, inner)]] := by
          apply Array.toList_inj.mp
          rw [h]
          obtain ⟨cl⟩ := cols
          simp_all
        conv => rhs; rw [← hsplit]
        simp only [blocksText, Array.toList_append, blockTextList_append]
        rw [hcore]
        simp [blockTextList, blockTextOne, blockTextColumns]
      · simp [blocksText, blockTextList, blockTextOne, blockTextColumns]
    · simp [blocksText, blockTextList, blockTextOne, blockTextColumns]
  · simp [blocksText, blockTextList, blockTextOne, blockTextColumns]

public theorem markInParagraph_text (inPar : Bool) (k : Nat) :
    Conserves blocksText (markInParagraph inPar k) := fun xs => by
  unfold markInParagraph
  split
  · next b _ hb =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    rw [Array.pop_push, blocksText_push, blocksText_push, inParagraph_text]
  · rfl
  · rfl

public theorem markInParagraph_false_id (k : Nat) (blocks : Array Block) :
    markInParagraph false k blocks = blocks := by
  unfold markInParagraph
  split <;> simp_all

public theorem flushedText_empty_exact (k : Nat) : flushedText k #[] = false := by
  simp [flushedText, lastContentFrom?, lastContentFrom?.go]

public theorem opensInParagraph_empty_exact (k : Nat) : opensInParagraph k #[] = false := by
  simp [opensInParagraph, flushedText_empty_exact, lastContent?, lastContentFrom?,
    lastContentFrom?.go]

public theorem lastLeavesEndPe_empty_exact : lastLeavesEndPe #[] = false := by
  simp [lastLeavesEndPe, lastContent?, lastContentFrom?, lastContentFrom?.go]

private theorem displayCtxOf_text (acc : String) (b : Block) :
    blockTextOne acc (displayCtxOf b).2 = blockTextOne acc b := by
  unfold displayCtxOf
  split
  · split
    · next hd => simp [blockTextOne, hd, blockTextList]
    · rfl
  · rfl

private theorem withDisplayCtx_text (acc : String) (c : DisplayCtx) (d : Block) :
    blockTextOne acc (withDisplayCtx c d) = blockTextOne acc d := by
  unfold withDisplayCtx
  split
  · rfl
  · simp [blockTextOne, blockTextList]

private theorem openDisplayAt_text (inPar endPe broken : Bool) (acc : String) (b : Block) :
    blockTextOne acc (openDisplayAt inPar endPe broken b) = blockTextOne acc b := by
  unfold openDisplayAt
  dsimp only
  split
  · rw [withDisplayCtx_text, displayCtxOf_text]
  · rfl

private theorem closeDisplayAt_text (parEnd : Bool) (acc : String) (b : Block) :
    blockTextOne acc (closeDisplayAt parEnd b) = blockTextOne acc b := by
  unfold closeDisplayAt
  dsimp only
  split
  · rw [withDisplayCtx_text, displayCtxOf_text]
  · rfl

mutual

private theorem carrierOpenBlock_text (inPar endPe broken : Bool) (acc : String) :
    Conserves (blockTextOne acc) (carrierOpenBlock inPar endPe broken) := fun b => by
  match b with
  | .altSteps s fa oa =>
    simp only [carrierOpenBlock, blockTextOne]
    rw [carrierOpenList_text inPar endPe broken acc fa.toList, carrierOpenList_text]
  | .onSteps s body =>
    simp only [carrierOpenBlock, blockTextOne]
    rw [carrierOpenList_text]
  | .para .. | .section .. | .list .. | .center .. | .ragged .. | .spaced .. | .role .. |
    .link .. | .quote .. | .lines .. | .abstract .. | .titled .. | .disclosure .. | .equation .. |
    .verbatim .. | .algorithm .. | .columns .. | .note .. | .only .. | .nav .. | .logo .. |
    .pagebreak | .frame .. | .framefoot .. | .setPalette .. | .setTokens .. | .rule .. |
    .picture .. | .table .. | .float .. | .bibliography .. | .contents .. =>
    simp only [carrierOpenBlock]
    exact openDisplayAt_text inPar endPe broken acc _

private theorem carrierOpenList_text (inPar endPe broken : Bool) (acc : String) :
    Conserves (blockTextList acc) (carrierOpenList inPar endPe broken) := fun xs => by
  match xs with
  | b :: rest =>
    simp only [carrierOpenList, blockTextList]
    rw [carrierOpenBlock_text]
  | [] => rfl

end

mutual

private theorem carrierCloseBlock_text (parEnd : Bool) (acc : String) :
    Conserves (blockTextOne acc) (carrierCloseBlock parEnd) := fun b => by
  match b with
  | .altSteps s fa oa =>
    simp only [carrierCloseBlock, blockTextOne]
    rw [carrierCloseList_text parEnd acc fa.toList, carrierCloseList_text]
  | .onSteps s body =>
    simp only [carrierCloseBlock, blockTextOne]
    rw [carrierCloseList_text]
  | .para .. | .section .. | .list .. | .center .. | .ragged .. | .spaced .. | .role .. |
    .link .. | .quote .. | .lines .. | .abstract .. | .titled .. | .disclosure .. | .equation .. |
    .verbatim .. | .algorithm .. | .columns .. | .note .. | .only .. | .nav .. | .logo .. |
    .pagebreak | .frame .. | .framefoot .. | .setPalette .. | .setTokens .. | .rule .. |
    .picture .. | .table .. | .float .. | .bibliography .. | .contents .. =>
    simp only [carrierCloseBlock]
    exact closeDisplayAt_text parEnd acc _

private theorem carrierCloseList_text (parEnd : Bool) (acc : String) :
    Conserves (blockTextList acc) (carrierCloseList parEnd) := fun xs => by
  match xs with
  | [] => rfl
  | [b] =>
    simp only [carrierCloseList, blockTextList]
    rw [carrierCloseBlock_text]
  | b :: c :: rest =>
    simp only [carrierCloseList, blockTextList]
    rw [carrierCloseList_text]
    rfl

end

public theorem carrierDisplays_text (inPar endPe parEnd broken : Bool) :
    Conserves blocksText (carrierDisplays inPar endPe parEnd broken) := fun xs => by
  simp only [carrierDisplays, blocksText, List.toList_toArray]
  rw [carrierCloseList_text, carrierOpenList_text]

public theorem markDisplay_text (inPar parEnd afterEnv : Bool) (k : Nat) :
    Conserves blocksText (markDisplay inPar parEnd afterEnv k) := fun xs => by
  unfold markDisplay
  split
  · next b _ hb =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    dsimp only
    split
    · rfl
    · rw [Array.pop_push, blocksText_push, blocksText_push]
      split <;> simp [blockTextOne, blockTextList, displayCtxOf_text]
  · rfl

private theorem blocksText_append_barSide (out : Array Block)
    (ink : Color × Option ColorRef) (before after : Dim.SymGlue)
    (w : Option Dim.SymGlue) :
    blocksText (out ++ barSide ink before after w) = blocksText out := by
  cases w <;>
    simp [barSide, gapBlock, blocksText, blockTextList_append, blockTextList,
      blockTextOne]

private theorem blocksText_titleStep (st : ElementStyle)
    (ink : Color × Option ColorRef) (out : Array Block) (starred : Bool)
    (num : Option String) (title : Array Inline) :
    blocksText (titleStep st ink out starred num title) =
      blocksText out ++ plainText title := by
  simp only [titleStep]
  rw [blocksText_append_barSide, blocksText_push, blocksText_append_barSide]
  simp [blockTextOne]

private theorem titleBarsList_text (st : ElementStyle) (ink : Color × Option ColorRef)
    (out : Array Block) (done : Bool) (l : List Block) :
    blocksText (titleBarsList st ink out done l) =
      blockTextList (blocksText out) l := by
  fun_induction titleBarsList st ink out done l <;>
    simp_all only [blockTextList, blocksText_push, blocksText_titleStep,
      blockTextOne]

public theorem titleBars_text (st : ElementStyle) (ink : Color × Option ColorRef) :
    Conserves blocksText (titleBars st ink) := by
  intro xs
  unfold titleBars
  split
  · rfl
  · rw [titleBarsList_text]
    simp [blocksText, blockTextList]

mutual

/-- Every `.section` level in document order, the document's heading outline;
frame bodies are walked, notes are not. -/
@[expose] public def headingLevels (xs : Array Block) : Array HeadingLevel := headingLevelList #[] xs.toList

@[expose] public def headingLevelList (out : Array HeadingLevel) : List Block → Array HeadingLevel
  | [] => out
  | b :: rest => headingLevelList (headingLevelOne out b) rest

@[expose] public def headingLevelOne (out : Array HeadingLevel) : Block → Array HeadingLevel
  | .section level _ _ _ => out.push level
  | .para _ => out
  | .equation _ _ => out
  | .list _ _ items => headingLevelItems out items.toList
  | .center body => headingLevelList out body.toList
  | .ragged _ body => headingLevelList out body.toList
  | .quote _ body => headingLevelList out body.toList
  | .lines _ => out
  | .abstract body => headingLevelList out body.toList
  | .titled _ _ body => headingLevelList out body.toList
  | .disclosure _ _ body => headingLevelList out body.toList
  | .role _ body => headingLevelList out body.toList
  | .link _ body => headingLevelList out body.toList
  | .spaced _ body => headingLevelList out body.toList
  | .columns cols => headingLevelColumns out cols.toList
  | .onSteps _ body => headingLevelList out body.toList
  | .altSteps _ firstPage otherPage =>
    headingLevelList (headingLevelList out firstPage.toList) otherPage.toList
  | .only _ body => headingLevelList out body.toList
  | .nav _ body => headingLevelList out body.toList
  | .frame _ _ _ _ body => headingLevelList out body.toList
  | .note _ => out
  | .verbatim _ _ _ => out
  | .algorithm _ _ _ => out
  | .framefoot _ => out
  | .setPalette _ => out
  | .setTokens _ => out
  | .pagebreak => out
  | .logo _ => out
  | .rule _ _ _ => out
  | .picture _ => out
  | .table _ _ _ rows _ _ => headingLevelRows out rows.toList
  | .float _ _ _ body _ => headingLevelList out body.toList
  | .bibliography _ _ _ | .contents _ _ => out

@[expose] public def headingLevelItems (out : Array HeadingLevel) : List (Array Block) → Array HeadingLevel
  | [] => out
  | item :: rest => headingLevelItems (headingLevelList out item.toList) rest

@[expose] public def headingLevelColumns (out : Array HeadingLevel) : List (BoxWidth × Array Block) → Array HeadingLevel
  | [] => out
  | (_, body) :: rest => headingLevelColumns (headingLevelList out body.toList) rest

@[expose] public def headingLevelRows (out : Array HeadingLevel) :
    List (Array (Array Block)) → Array HeadingLevel
  | [] => out
  | row :: rest => headingLevelRows (headingLevelItems out row.toList) rest

end

/-- The first reading's elements followed by the other reading's extra
occurrences, as a multiset union. -/
public def exclusiveOccurrences {α : Type u} [BEq α] (first other : Array α) : Array α :=
  first ++ (first.toList.foldl List.erase other.toList).toArray

private theorem eraseOccurrences_exact {α : Type u} [BEq α] [LawfulBEq α]
    (x : α) (first other : List α) :
    (first.foldl List.erase other).count x = other.count x - first.count x := by
  induction first generalizing other with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih, List.count_erase, List.count_cons]
    omega

public theorem exclusiveOccurrences_exact {α : Type u} [BEq α] [LawfulBEq α]
    (x : α) (first other : Array α) :
    (exclusiveOccurrences first other).toList.count x =
      max (first.toList.count x) (other.toList.count x) := by
  simp only [exclusiveOccurrences, Array.toList_append, List.count_append,
    eraseOccurrences_exact]
  omega

mutual

/-- Every footnote outside a speaker note, in document order with its resolved
mark number; equal occurrences in exclusive alternatives share one endnote. -/
-- conserves: none — projects the footnotes alone.
public def footnotesOf (xs : Array Block) : Array (Option Nat × Array Inline) :=
  footnoteBlockList #[] xs.toList

private def footnoteBlockList (out : Array (Option Nat × Array Inline)) :
    List Block → Array (Option Nat × Array Inline)
  | [] => out
  | b :: rest => footnoteBlockList (footnoteBlockOne out b) rest

private def footnoteBlockOne (out : Array (Option Nat × Array Inline)) :
    Block → Array (Option Nat × Array Inline)
  | .para content => footnoteInlineList out content.toList
  | .equation number content =>
    footnoteInlineList (footnoteInlineList out content.toList) number.toList
  | .section _ _ _ title => footnoteInlineList out title.toList
  | .list _ _ items => footnoteItems out items.toList
  | .center body => footnoteBlockList out body.toList
  | .ragged _ body => footnoteBlockList out body.toList
  | .quote _ body => footnoteBlockList out body.toList
  | .lines ls => footnoteLaid out ls.toList
  | .abstract body => footnoteBlockList out body.toList
  | .titled _ title body =>
    footnoteBlockList (footnoteInlineList out title.toList) body.toList
  | .disclosure title _ body =>
    footnoteBlockList (footnoteInlineList out title.toList) body.toList
  | .role _ body => footnoteBlockList out body.toList
  | .link _ body => footnoteBlockList out body.toList
  | .spaced _ body => footnoteBlockList out body.toList
  | .columns cols => footnoteColumns out cols.toList
  | .onSteps _ body => footnoteBlockList out body.toList
  | .altSteps _ firstPage otherPage =>
    out ++ exclusiveOccurrences (footnoteBlockList #[] firstPage.toList)
      (footnoteBlockList #[] otherPage.toList)
  | .only _ body => footnoteBlockList out body.toList
  | .nav _ body => footnoteBlockList out body.toList
  | .frame title _ _ _ body =>
    footnoteBlockList (footnoteInlineList out title.toList) body.toList
  | .note _ => out
  | .verbatim _ _ _ => out
  | .framefoot _ => out
  | .setPalette _ => out
  | .setTokens _ => out
  | .pagebreak => out
  | .logo _ => out
  | .rule _ _ _ => out
  | .picture _ => out
  | .table _ _ _ rows _ _ => footnoteTableRows out rows.toList
  | .algorithm _ _ lines => footnoteAlgLines out lines.toList
  | .float _ _ _ body caption =>
    footnoteBlockList (footnoteInlineList out caption.toList) body.toList
  | .bibliography _ _ items => footnoteBibItems out items.toList
  | .contents _ entries => footnoteContentsEntries out entries.toList

private def footnoteBibItems (out : Array (Option Nat × Array Inline)) :
    List BibItem → Array (Option Nat × Array Inline)
  | [] => out
  | it :: rest => footnoteBibItems (footnoteInlineList out it.content.toList) rest

private def footnoteContentsEntries (out : Array (Option Nat × Array Inline)) :
    List ContentsEntry → Array (Option Nat × Array Inline)
  | [] => out
  | e :: rest => footnoteContentsEntries (footnoteInlineList out e.title.toList) rest

private def footnoteTableRows (out : Array (Option Nat × Array Inline)) :
    List (Array (Array Block)) → Array (Option Nat × Array Inline)
  | [] => out
  | row :: rest => footnoteTableRows (footnoteItems out row.toList) rest

private def footnoteItems (out : Array (Option Nat × Array Inline)) :
    List (Array Block) → Array (Option Nat × Array Inline)
  | [] => out
  | item :: rest => footnoteItems (footnoteBlockList out item.toList) rest

private def footnoteColumns (out : Array (Option Nat × Array Inline)) :
    List (BoxWidth × Array Block) → Array (Option Nat × Array Inline)
  | [] => out
  | (_, body) :: rest => footnoteColumns (footnoteBlockList out body.toList) rest

private def footnoteAlgLines (out : Array (Option Nat × Array Inline)) :
    List AlgLine → Array (Option Nat × Array Inline)
  | [] => out
  | l :: rest =>
    footnoteAlgLines (match l.comment with
      | some c => footnoteInlineList (footnoteInlineList out l.content.toList) c.toList
      | none => footnoteInlineList out l.content.toList) rest

private def footnoteLaid (out : Array (Option Nat × Array Inline)) :
    List LaidLine → Array (Option Nat × Array Inline)
  | [] => out
  | l :: rest => footnoteLaid (footnoteInlineList out l.content.toList) rest

private def footnoteInlineList (out : Array (Option Nat × Array Inline)) :
    List Inline → Array (Option Nat × Array Inline)
  | [] => out
  | x :: rest => footnoteInlineList (footnoteInlineOne out x) rest

private def footnoteInlineOne (out : Array (Option Nat × Array Inline)) :
    Inline → Array (Option Nat × Array Inline)
  | .footnote num body =>
    footnoteInlineList (out.push (num, body)) body.toList
  | .styled _ body => footnoteInlineList out body.toList
  | .colored _ _ body => footnoteInlineList out body.toList
  | .located _ body => footnoteInlineList out body.toList
  | .role _ body => footnoteInlineList out body.toList
  | .link _ body => footnoteInlineList out body.toList
  | .cited _ _ ink => footnoteInlineList out ink.toList
  | .decorated _ body | .boxed _ body => footnoteInlineList out body.toList
  | .onSteps _ body => footnoteInlineList out body.toList
  | .altSteps _ firstPage otherPage =>
    out ++ exclusiveOccurrences (footnoteInlineList #[] firstPage.toList)
      (footnoteInlineList #[] otherPage.toList)
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ => out

end

/-- The places of a document's notes, one past each one's index, grouped by equal notes: the
names a backend gives them whatever numbers they show. -/
public structure NotePlaces where
  notes : Array (Option Nat × Array Inline)
  table : Std.HashMap (Option Nat × String) (Array (Array Inline × Array Nat))
  deriving Inhabited

public def NotePlaces.of (notes : Array (Option Nat × Array Inline)) : NotePlaces :=
  ⟨notes, notes.zipIdx.foldl (init := {}) fun m ((n, c), i) =>
    let key := (n, plainText c)
    let xs := m.getD key #[]
    match xs.findIdx? (·.1 == c) with
    | some j => m.insert key (xs.modify j fun (c, ps) => (c, ps.push (i + 1)))
    | none => m.insert key (xs.push (c, #[i + 1]))⟩

/-- The places of the notes equal to one, in reading order; empty for a note outside the list. -/
public def NotePlaces.places (t : NotePlaces) (n : Option Nat) (c : Array Inline) : Array Nat :=
  (((t.table.getD (n, plainText c) #[]).find? (·.1 == c)).map (·.2)).getD #[]

/-- The place of the first note equal to one. -/
public def NotePlaces.place (t : NotePlaces) (n : Option Nat) (c : Array Inline) : Option Nat :=
  (t.places n c)[0]?

/-- Each group of equal notes' places, by its first. -/
public def NotePlaces.groups (t : NotePlaces) : Std.HashMap Nat (Array Nat) :=
  t.table.fold (init := {}) fun m _ xs =>
    xs.foldl (init := m) fun m (_, ps) => match ps[0]? with
      | some p => m.insert p ps
      | none => m

mutual

/-- A field's notes numbered in reading order from `k + 1`; returns the counter past them. -/
-- conserves: none — sets marks only.
public def numberNotesInline (k : Nat) (x : Inline) : Nat × Inline :=
  match x with
  | .footnote none body =>
    let r := numberNotesList (k + 1) #[] body.toList
    (r.1, .footnote (some (k + 1)) r.2)
  | .footnote (some n) body =>
    let r := numberNotesList k #[] body.toList
    (r.1, .footnote (some n) r.2)
  | .styled s body =>
    let r := numberNotesList k #[] body.toList
    (r.1, .styled s r.2)
  | .colored c n body =>
    let r := numberNotesList k #[] body.toList
    (r.1, .colored c n r.2)
  | .located sp body =>
    let r := numberNotesList k #[] body.toList
    (r.1, .located sp r.2)
  | .role nm body =>
    let r := numberNotesList k #[] body.toList
    (r.1, .role nm r.2)
  | .link t body =>
    let r := numberNotesList k #[] body.toList
    (r.1, .link t r.2)
  | .cited f ks ink =>
    let r := numberNotesList k #[] ink.toList
    (r.1, .cited f ks r.2)
  | .decorated d body =>
    let r := numberNotesList k #[] body.toList
    (r.1, .decorated d r.2)
  | .boxed b body =>
    let r := numberNotesList k #[] body.toList
    (r.1, .boxed b r.2)
  | .onSteps spec body =>
    let r := numberNotesList k #[] body.toList
    (r.1, .onSteps spec r.2)
  | .altSteps spec firstPage otherPage =>
    let a := numberNotesList k #[] firstPage.toList
    let o := numberNotesList a.1 #[] otherPage.toList
    (o.1, .altSteps spec a.2 o.2)
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .label _
  | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _
  | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ => (k, x)

public def numberNotesList (k : Nat) (out : Array Inline) : List Inline → Nat × Array Inline
  | [] => (k, out)
  | x :: rest =>
    let r := numberNotesInline k x
    numberNotesList r.1 (out.push r.2) rest

end

/-- A reference list's notes numbered from `k + 1`, entry by entry, and the counter past them. -/
public def numberNotesItems (k : Nat) (items : Array BibItem) : Nat × Array BibItem :=
  items.foldl (init := (k, #[])) fun (k, out) it =>
    let r := numberNotesList k #[] it.content.toList
    (r.1, out.push { it with content := r.2 })

/-- Whether inline content holds a note its reading left to the list. -/
public def hasListNote (xs : Array Inline) : Bool :=
  anyInline (fun x => x matches .footnote none _) xs

/-- The document with each `\bibliography` list's note count set to `m`. -/
@[expose] public def Doc.withListNotes (doc : Doc) (m : Nat) : Doc :=
  { doc with listNotes := doc.listNotes.map fun (k, _) => (k, m) }

/-- A heading level in the author's own vocabulary. -/
private def levelName : HeadingLevel → String
  | .title => "the title"
  | .h1 => "a rank-one heading"
  | .h2 => "a rank-two heading"
  | .h3 => "a rank-three heading"
  | .h4 => "a rank-four heading"
  | .h5 => "a rank-five heading"
  | .h6 => "a rank-six heading"

/-- The broken-outline diagnostic, W0320. -/
private def outlineGapDiag (p l : HeadingLevel) : Diag :=
  Diag.of .W0320 (Diag.say .W0320 .heading)
    (detail := some s!"{levelName p} is followed by {levelName l}")
    (help := some "descend one rank at a time: 1, 2, 3, 4, 5, 6; \
add the missing heading or promote the deeper one (HTML §4.3.11, WCAG G141)")

private def outlineTitleDiag : Diag :=
  Diag.of .W0321 (Diag.say .W0321 .title)
    (help := some "put \\maketitle before the first \\section, so the \
outline starts at its top")

/-- The outline walk over the heading levels, `prev` the level just read: each
code fires once per document, in encounter order. -/
private def outlineWalk (prev : HeadingLevel) (gapNamed titleNamed : Bool)
    (out : Array Diag) : List HeadingLevel → Array Diag
  | [] => out
  | l :: rest =>
    if headingRank l > headingRank prev + 1 && !gapNamed then
      if l == 0 && !titleNamed then
        outlineWalk l true true
          ((out.push (outlineGapDiag prev l)).push outlineTitleDiag) rest
      else
        outlineWalk l true titleNamed (out.push (outlineGapDiag prev l)) rest
    else
      if l == 0 && !titleNamed then
        outlineWalk l gapNamed true (out.push outlineTitleDiag) rest
      else
        outlineWalk l gapNamed titleNamed out rest

/-- Whether, after a heading at `prev`, a heading exceeds its lead by more than one level. -/
private def outlineSkips (prev : HeadingLevel) : List HeadingLevel → Bool
  | [] => false
  | l :: rest => headingRank l > headingRank prev + 1 || outlineSkips l rest

/-- Whether the document's outline skips a level (HTML §4.3.11, WCAG technique G141). -/
public def outlineHasSkip (doc : Doc) : Bool :=
  match (headingLevels doc.body).toList with
  | [] => false
  | l :: rest => outlineSkips l rest

/-- Outline warnings, once each per document: a heading more than one level
deeper than its lead, and a level-0 title that does not come first. -/
public def outlineDiags (doc : Doc) : Array Diag :=
  match (headingLevels doc.body).toList with
  | [] => #[]
  | l :: rest => outlineWalk l false false #[] rest

private theorem outlineWalk_mem (d : Diag) :
    ∀ (ls : List HeadingLevel) (prev : HeadingLevel) (gN tN : Bool) (out : Array Diag),
      d ∈ out → d ∈ outlineWalk prev gN tN out ls
  | [], _, _, _, _, h => h
  | _ :: rest, _, _, _, _, h => by
    unfold outlineWalk
    split <;> split <;>
      exact outlineWalk_mem d rest _ _ _ _ (by
        first
        | exact h
        | exact Array.mem_push.mpr (Or.inl h)
        | exact Array.mem_push.mpr (Or.inl (Array.mem_push.mpr (Or.inl h))))

private theorem outlineWalk_finds :
    ∀ (ls : List HeadingLevel) (prev : HeadingLevel) (tN : Bool) (out : Array Diag),
      outlineSkips prev ls = true →
      ∃ d ∈ outlineWalk prev false tN out ls, d.code = "W0320"
  | l :: rest, prev, tN, out, hskip => by
    unfold outlineWalk
    by_cases hgap : headingRank l > headingRank prev + 1
    · refine ⟨outlineGapDiag prev l, ?_, by
        unfold outlineGapDiag
        rw [Diag.of_code_exact (detail := _)]
        exact DiagCode.w0320_code_exact⟩
      simp only [hgap, decide_true, Bool.not_false, Bool.and_true, ite_true]
      split <;>
        exact outlineWalk_mem _ rest _ _ _ _ (by simp [Array.mem_push])
    · have hrest : outlineSkips l rest = true := by
        unfold outlineSkips at hskip
        simpa [hgap] using hskip
      simp only [hgap, decide_false, Bool.false_and, Bool.false_eq_true,
        ite_false]
      split
      · exact outlineWalk_finds rest l true _ hrest
      · exact outlineWalk_finds rest l tN out hrest

public theorem headings_no_skip_judged (doc : Doc)
    (h : outlineHasSkip doc = true) :
    ∃ d ∈ outlineDiags doc, d.code = "W0320" := by
  unfold outlineHasSkip at h
  unfold outlineDiags
  split at h
  · exact absurd h (by simp)
  · exact outlineWalk_finds _ _ false #[] h

/-- Whether this node is a physical-page placeholder (`\pagenumber` / `\pagecount`). -/
@[expose] public def isPhysicalPage : Inline → Bool
  | .pageNumber => true
  | .pageCount => true
  | _ => false

/-- Whether inline content carries a physical-page placeholder anywhere. -/
@[expose] public def hasPhysicalPage (xs : Array Inline) : Bool :=
  anyInline isPhysicalPage xs

/-- Whether this slot shows the frame sequence rather than the physical pages. -/
public def ChromeSlot.isFrameSequence : ChromeSlot → Bool
  | .frameNumber => true
  | .frameFraction => true
  | .sectionTitle | .blank => false

/-- W0332 when a `\framefoot` note carries `\pagenumber`/`\pagecount` beside a
frame-sequence chrome slot the document did not declare itself. -/
public def footerSequenceDiags (doc : Doc) : Array Diag := Id.run do
  unless doc.docClass.record.chrome && doc.foot.isNone && !doc.chromeDeclared do
    return #[]
  let frameSlot := (doc.chrome.footerLeft.map ChromeSlot.isFrameSequence).getD false
    || (doc.chrome.footerRight.map ChromeSlot.isFrameSequence).getD false
  unless frameSlot do return #[]
  let mut out : Array Diag := #[]
  for b in doc.body do
    if let .framefoot xs := b then
      if hasPhysicalPage xs && out.isEmpty then
        out := out.push (Diag.of .W0332 (Diag.say .W0332 .footer "\\framefoot")
          (help := some "declare the footer's slots yourself \
(\\chrome{ footer = { left = ..., right = \\framenumber } }) to say the \
mixing is meant, or drop \\pagenumber from \\framefoot"))
  return out

public theorem frame_sequence_carries_no_physical (s : ChromeSlot)
    (sec : Array Inline) (n total : Nat) (hs : s.isFrameSequence = true) :
    hasPhysicalPage (s.render sec n total) = false := by
  cases s with
  | sectionTitle | blank => simp [ChromeSlot.isFrameSequence] at hs
  | frameNumber =>
    simp [ChromeSlot.render, hasPhysicalPage, anyInline, foldInlines,
      foldInlineList, foldInline, isPhysicalPage]
  | frameFraction =>
    simp [ChromeSlot.render, hasPhysicalPage, anyInline, foldInlines,
      foldInlineList, foldInline, isPhysicalPage]

private theorem plainTextList_append (l1 l2 : List Inline) :
    plainTextList (l1 ++ l2) = plainTextList l1 ++ plainTextList l2 := by
  induction l1 with
  | nil => simp [plainTextList]
  | cons x rest ih => simp [plainTextList, ih, String.append_assoc]

private theorem plainText_push (xs : Array Inline) (x : Inline) :
    plainText (xs.push x) = plainText xs ++ plainTextOne x := by
  simp [plainText, Array.toList_push, plainTextList_append, plainTextList]

private theorem mergeStep_text (out : Array Inline) (x : Inline) :
    plainText (mergeStep out x) = plainText out ++ plainTextOne x := by
  unfold mergeStep
  split
  · rename_i s t hb
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp hb
    simp [Array.pop_push, plainText_push, plainTextOne, String.append_assoc]
  · simp [plainText_push]

public theorem mergeTexts_text : Conserves plainText mergeTexts := fun xs => by
  have fold : ∀ (l : List Inline) (acc : Array Inline),
      plainText (l.foldl mergeStep acc) = plainText acc ++ plainTextList l := by
    intro l
    induction l with
    | nil => intro acc; simp [plainTextList]
    | cons x rest ih =>
      intro acc
      simp [List.foldl, ih, mergeStep_text, plainTextList, String.append_assoc]
  rw [mergeTexts, ← Array.foldl_toList, fold]
  simp [plainText, plainTextList]

private theorem blockTextList_chain (l1 l2 : List Block) (acc : String) :
    blockTextList acc (l1 ++ l2) = blockTextList (blockTextList acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextList]
  | cons b rest ih => simp [blockTextList, ih]

private theorem algLineText_chain (l1 l2 : List AlgLine) (acc : String) :
    algLineText acc (l1 ++ l2) = algLineText (algLineText acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [algLineText]
  | cons l rest ih => cases hc : l.comment <;> simp [algLineText, hc, ih]

private theorem laidText_chain (l1 l2 : List LaidLine) (acc : String) :
    laidText acc (l1 ++ l2) = laidText (laidText acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [laidText]
  | cons l rest ih => simp [laidText, ih]

private theorem blockTextItems_chain (l1 l2 : List (Array Block)) (acc : String) :
    blockTextItems acc (l1 ++ l2) = blockTextItems (blockTextItems acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextItems]
  | cons item rest ih => simp [blockTextItems, ih]

private theorem blockTextColumns_chain (l1 l2 : List (BoxWidth × Array Block))
    (acc : String) :
    blockTextColumns acc (l1 ++ l2)
      = blockTextColumns (blockTextColumns acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextColumns]
  | cons col rest ih => simp [blockTextColumns, ih]

private theorem blockTextTableRows_chain (l1 l2 : List (Array (Array Block)))
    (acc : String) :
    blockTextTableRows acc (l1 ++ l2)
      = blockTextTableRows (blockTextTableRows acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextTableRows]
  | cons row rest ih => simp [blockTextTableRows, ih]

mutual

private theorem dimInlineList_text (k : Nat) (pend : Option DimHere) (here : DimHere)
    (own : Option Color) (xs : List Inline) (out : Array Inline) :
    plainTextList (dimInlineList k pend here own out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simp [dimInlineList, plainTextList]
  | x :: rest =>
    rw [dimInlineList, dimInlineList_text k pend here own rest]
    simp [plainTextList, plainTextList_append, dimInline_text k pend here own x,
      String.append_assoc]

private theorem dimInline_text (k : Nat) (pend : Option DimHere) (here : DimHere)
    (own : Option Color) (x : Inline) :
    plainTextOne (dimInline k pend here own x) = plainTextOne x := by
  match x with
  | .styled st body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text k pend here own body.toList #[], plainTextList]
  | .footnote n body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text k pend here own body.toList #[], plainTextList]
  | .colored c nm body =>
    cases pend with
    | some cv =>
      rw [dimInline]
      simp [plainTextOne, dimInlineList_text k (some cv) here (some c) body.toList #[],
        plainTextList]
    | none =>
      rw [dimInline]
      simp [plainTextOne, dimInlineList_text k none here (some c) body.toList #[], plainTextList]
  | .located n body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text k pend here own body.toList #[], plainTextList]
  | .role n body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text k pend here own body.toList #[], plainTextList]
  | .link u body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text k pend here own body.toList #[], plainTextList]
  | .cited f ks ink =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text k pend here own ink.toList #[], plainTextList]
  | .decorated kind body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text k pend here own body.toList #[], plainTextList]
  | .boxed b body =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text k pend here own body.toList #[], plainTextList]
  | .onSteps spec body =>
    rw [dimInline]
    by_cases hc : here.cover.hidden = true
    · simp [hc, plainTextOne, dimInlineList_text k pend here own body.toList #[], plainTextList]
    by_cases h : (!spec.invisible && pend.isNone && spec.pending k) = true
    · simp [hc, h, plainTextOne, plainTextList,
        dimInlineList_text k (some here) here own body.toList #[]]
    · simp [hc, h, plainTextOne, dimInlineList_text k pend here own body.toList #[],
        plainTextList]
  | .altSteps spec firstPage otherPage =>
    rw [dimInline]
    simp [plainTextOne, dimInlineList_text k pend here own firstPage.toList #[],
      dimInlineList_text k pend here own otherPage.toList #[], plainTextList]
  | .image _ _ _ =>
    rfl
  | .formula _ _ _ =>
    rfl
  | .text _ | .math _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _
  | .label _ | .ref _ _ _ _
  | .icon _ _ | .cite _ _ =>
    rfl

end

private theorem coverRun_text (k : Nat) (cv : DimHere) (here : DimHere) (xs : Array Inline) :
    plainText (coverRun k cv here xs) = plainText xs := by
  simp [coverRun, plainText, plainTextList, plainTextOne,
    dimInlineList_text k (some cv) here none xs.toList #[]]

private theorem descLabel_text {xs label rest : Array Inline}
    (h : descLabel? xs = some (label, rest)) :
    plainText xs = plainText label ++ plainText rest := by
  unfold descLabel? at h
  split at h
  · rename_i n l hx
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h0 : xs.toList[0]? = some (Inline.role n l) := by simpa using hx
      cases wl : xs.toList with
      | nil => simp [wl] at h0
      | cons y tl =>
        rw [wl] at h0
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
        subst h0
        have hlen : xs.size = tl.length + 1 := by
          have h1 := congrArg List.length wl
          simpa using h1
        simp [plainText, wl, hlen, plainTextList, plainTextOne, Array.toList_extract,
          List.extract]
    · simp at h
  · simp at h

private theorem dimContent_text (k : Nat) (pend : Option DimHere) (here : DimHere)
    (xs : Array Inline) : plainText (dimContent k pend here xs) = plainText xs := by
  cases pend with
  | some cv =>
    cases hd : descLabel? xs with
    | none =>
      simp only [dimContent, hd]
      exact coverRun_text k cv here xs
    | some lr =>
      obtain ⟨label, rest⟩ := lr
      simp only [dimContent, hd]
      rw [descLabel_text hd]
      simp [plainText, plainTextList, plainTextOne, coverRun,
        dimInlineList_text k (some cv) here none label.toList #[],
        dimInlineList_text k (some cv) here none rest.toList #[]]
  | none => simp [dimContent, plainText, dimInlineList_text k none here none xs.toList #[],
      plainTextList]

private theorem dimFilled_text (k : Nat) (pend : Option DimHere) (here : DimHere)
    (xs : Array Inline) : plainText (dimFilled k pend here xs) = plainText xs := by
  unfold dimFilled
  split
  · rfl
  · exact dimContent_text k pend here xs

private theorem blockTextContentsEntries_map (f : Array Inline → Array Inline)
    (hf : ∀ x, plainText (f x) = plainText x) (es : List ContentsEntry) (acc : String) :
    blockTextContentsEntries acc (es.map fun e => { e with title := f e.title }) =
      blockTextContentsEntries acc es := by
  induction es generalizing acc with
  | nil => rfl
  | cons e rest ih => simp [blockTextContentsEntries, hf, ih]

private theorem dimAlgLines_text (k : Nat) (pend : Option DimHere) (here : DimHere)
    (ls : List AlgLine) (out : Array AlgLine) (acc : String) :
    algLineText acc (dimAlgLines k pend here out ls).toList
      = algLineText (algLineText acc out.toList) ls := by
  match ls with
  | [] => simp [dimAlgLines, algLineText]
  | l :: rest =>
    rw [dimAlgLines, dimAlgLines_text k pend here rest]
    rw [Array.toList_push, algLineText_chain]
    cases hc : l.comment <;> simp [hc, algLineText, dimFilled_text]

private theorem dimLaid_text (k : Nat) (pend : Option DimHere) (here : DimHere)
    (ls : List LaidLine) (out : Array LaidLine) (acc : String) :
    laidText acc (dimLaid k pend here out ls).toList = laidText (laidText acc out.toList) ls := by
  match ls with
  | [] => simp [dimLaid, laidText]
  | l :: rest =>
    rw [dimLaid, dimLaid_text k pend here rest]
    rw [Array.toList_push, laidText_chain]
    simp [laidText, dimFilled_text]

mutual

private theorem dimBlockList_text (k : Nat) (pend : Option DimHere) (here : DimHere)
    (xs : List Block) (out : Array Block) (acc : String) :
    blockTextList acc (dimBlockList k pend here out xs).1.toList
      = blockTextList (blockTextList acc out.toList) xs := by
  match xs with
  | [] => simp [dimBlockList, blockTextList]
  | b :: rest =>
    rw [dimBlockList, dimBlockList_text k pend (dimBlock k pend here b).2 rest]
    simp [blockTextList, blockTextList_chain, dimBlock_text k pend here b]
termination_by structural xs

private theorem dimBlock_text (k : Nat) (pend : Option DimHere) (here : DimHere) (b : Block)
    (acc : String) :
    blockTextOne acc (dimBlock k pend here b).1 = blockTextOne acc b := by
  match b with
  | .para content =>
    simp [dimBlock, blockTextOne, dimContent_text]
  | .equation num content =>
    simp [dimBlock, blockTextOne, dimContent_text]
  | .list o _ items =>
    simp [dimBlock, blockTextOne, dimItems_text k pend here items.toList #[] acc, blockTextItems]
  | .center body =>
    simp [dimBlock, blockTextOne, dimBlockList_text k pend here body.toList #[] acc, blockTextList]
  | .ragged _ body =>
    simp [dimBlock, blockTextOne, dimBlockList_text k pend here body.toList #[] acc, blockTextList]
  | .quote _ body =>
    simp [dimBlock, blockTextOne, dimBlockList_text k pend here body.toList #[] acc, blockTextList]
  | .lines ls =>
    simp [dimBlock, blockTextOne, dimLaid_text k pend here ls.toList #[] acc, laidText]
  | .abstract body =>
    simp [dimBlock, blockTextOne, dimBlockList_text k pend here body.toList #[] acc, blockTextList]
  | .titled kind title body =>
    simp [dimBlock, blockTextOne, plainText,
      dimInlineList_text k pend here none title.toList #[], plainTextList,
      dimBlockList_text k pend here body.toList #[] _, blockTextList]
  | .disclosure summary expanded body =>
    simp [dimBlock, blockTextOne, plainText,
      dimInlineList_text k pend here none summary.toList #[], plainTextList,
      dimBlockList_text k pend here body.toList #[] _, blockTextList]
  | .role n body =>
    simp [dimBlock, blockTextOne, dimBlockList_text k pend here body.toList #[] acc, blockTextList]
  | .link target body =>
    simp [dimBlock, blockTextOne, dimBlockList_text k pend here body.toList #[] acc, blockTextList]
  | .spaced g body =>
    simp [dimBlock, blockTextOne, dimBlockList_text k pend here body.toList #[] acc, blockTextList]
  | .columns cols =>
    simp [dimBlock, blockTextOne, dimColumns_text k pend here cols.toList #[] acc, blockTextColumns]
  | .onSteps spec body =>
    simp only [dimBlock, blockTextOne]
    rw [dimBlockList_text k _ here body.toList #[] acc]
    simp [blockTextList]
  | .altSteps spec firstPage otherPage =>
    simp [dimBlock, blockTextOne, dimBlockList_text k pend here firstPage.toList #[],
      dimBlockList_text k pend here otherPage.toList #[], blockTextList]
  | .only targets body =>
    simp [dimBlock, blockTextOne, dimBlockList_text k pend here body.toList #[] acc, blockTextList]
  | .nav spec body =>
    simp [dimBlock, blockTextOne, dimBlockList_text k pend here body.toList #[] acc, blockTextList]
  | .logo _ => rfl
  | .verbatim c s spec =>
    cases hc : spec.caption with
    | none => simp [dimBlock, blockTextOne, ListingSpec.capText, hc]
    | some p =>
      simp [dimBlock, blockTextOne, ListingSpec.capText, hc, plainText, plainTextList,
        dimInlineList_text k pend here none p.2.toList #[]]
  | .section l st num title =>
    simp [dimBlock, blockTextOne, plainText, dimInlineList_text k pend here none title.toList #[],
      plainTextList]
  | .note _ | .frame _ _ _ _ _ | .framefoot _
  | .setPalette _ | .setTokens _
  | .rule _ _ _ | .picture _ | .pagebreak | .bibliography _ _ _ => rfl
  | .contents _ entries =>
    simpa [dimBlock, blockTextOne] using
      blockTextContentsEntries_map _ (dimFilled_text k pend here) entries.toList acc
  | .algorithm n sm lines =>
    show algLineText acc (dimAlgLines k pend here #[] lines.toList).toList = _
    rw [dimAlgLines_text k pend here lines.toList #[] acc]
    rfl
  | .table cols pl pr rows rules spans =>
    simp [dimBlock, blockTextOne, dimTableRows_text k pend here rows.toList #[] acc,
      blockTextTableRows]
  | .float fk num ca body caption =>
    simp [dimBlock, blockTextOne, dimFilled_text,
      dimBlockList_text k pend here body.toList #[] _, blockTextList]
termination_by structural b

private theorem dimItems_text (k : Nat) (pend : Option DimHere) (here : DimHere)
    (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (dimItems k pend here out items).1.toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [dimItems, blockTextItems]
  | item :: rest =>
    rw [dimItems, dimItems_text k pend (dimBlockList k pend here #[] item.toList).2 rest]
    simp [blockTextItems, blockTextItems_chain,
      dimBlockList_text k pend here item.toList #[], blockTextList]
termination_by structural items

private theorem dimColumns_text (k : Nat) (pend : Option DimHere) (here : DimHere)
    (cols : List (BoxWidth × Array Block))
    (out : Array (BoxWidth × Array Block)) (acc : String) :
    blockTextColumns acc (dimColumns k pend here out cols).1.toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [dimColumns, blockTextColumns]
  | (w, body) :: rest =>
    rw [dimColumns, dimColumns_text k pend (dimBlockList k pend here #[] body.toList).2 rest]
    simp [blockTextColumns, blockTextColumns_chain,
      dimBlockList_text k pend here body.toList #[], blockTextList]
termination_by structural cols

private theorem dimTableRows_text (k : Nat) (pend : Option DimHere) (here : DimHere)
    (rows : List (Array (Array Block)))
    (out : Array (Array (Array Block))) (acc : String) :
    blockTextTableRows acc (dimTableRows k pend here out rows).toList
      = blockTextTableRows (blockTextTableRows acc out.toList) rows := by
  match rows with
  | [] => simp [dimTableRows, blockTextTableRows]
  | row :: rest =>
    rw [dimTableRows, dimTableRows_text k pend here rest _ acc]
    simp [blockTextTableRows, blockTextTableRows_chain,
      dimItems_text k pend here row.toList #[], blockTextItems]
termination_by structural rows

end

public theorem dimBlocks_text (here : DimHere) (k : Nat) :
    Conserves blocksText (dimBlocks here k) := fun xs => by
  simp [blocksText, dimBlocks, dimBlockList_text k none here xs.toList #[] "", blockTextList]

public theorem coverInlines_text (cv : Cover) (ink : Color) :
    Conserves plainText (coverInlines cv ink) := fun xs =>
  coverRun_text 1 (DimHere.under cv ink) (DimHere.under cv ink) xs

public theorem algorithm_text (numbered semis : Bool) (lines : Array AlgLine) :
    blocksText #[Block.algorithm numbered semis lines]
      = algLineText "" lines.toList := by rfl

public theorem decorated_text (kind : Decoration) :
    Conserves plainText (fun xs => #[Inline.decorated kind xs]) :=
  wrap_text (.decorated kind) fun _ => rfl

public theorem boxed_text (b : InlineBox) :
    Conserves plainText (fun xs => #[Inline.boxed b xs]) :=
  wrap_text (.boxed b) fun _ => rfl

mutual

private theorem numberFloatList_text {wf : Bool} (c : FloatCtr) (acc : Array Block)
    (bs : List Block) (s : String) :
    blockTextList s ((numberFloatList wf c acc bs).2).toList
      = blockTextList (blockTextList s acc.toList) bs := by
  match bs with
  | [] => simp [numberFloatList, blockTextList]
  | b :: rest =>
    show blockTextList s ((numberFloatList wf (numberFloatOne wf c b).1
      (acc.push (numberFloatOne wf c b).2) rest).2).toList = _
    rw [numberFloatList_text (numberFloatOne wf c b).1
      (acc.push (numberFloatOne wf c b).2) rest s]
    rw [Array.toList_push, blockTextList_chain]
    simp [blockTextList, numberFloatOne_text c b]

private theorem numberFloatOne_text {wf : Bool} (c : FloatCtr) (b : Block) (s : String) :
    blockTextOne s (numberFloatOne wf c b).2 = blockTextOne s b := by
  match b with
  | .para _ | .lines _ | .equation _ _ | .section _ _ _ _ | .note _ | .verbatim _ _ _ | .logo _
  | .bibliography _ _ _ | .contents _ _ | .algorithm _ _ _
  | .framefoot _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ => rfl
  | .list o _ items =>
    simp [numberFloatOne, blockTextOne,
      numberFloatItems_text c #[] items.toList, blockTextItems]
  | .center body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .ragged _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .quote _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .abstract body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .titled kind title body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .disclosure summary expanded body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .role _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .link _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .spaced _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .columns cols =>
    simp [numberFloatOne, blockTextOne,
      numberFloatCols_text c #[] cols.toList, blockTextColumns]
  | .onSteps _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .altSteps _ firstPage otherPage =>
    simp [numberFloatOne, blockTextOne, numberFloatList_text, blockTextList]
  | .only _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .nav _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .frame _ _ _ _ body =>
    simp [numberFloatOne, blockTextOne,
      numberFloatList_text c #[] body.toList, blockTextList]
  | .float kind _ capAbove body caption =>
    simp [numberFloatOne, blockTextOne, numberFloatList_text, blockTextList]

private theorem numberFloatItems_text {wf : Bool} (c : FloatCtr) (acc : Array (Array Block))
    (items : List (Array Block)) (s : String) :
    blockTextItems s ((numberFloatItems wf c acc items).2).toList
      = blockTextItems (blockTextItems s acc.toList) items := by
  match items with
  | [] => simp [numberFloatItems, blockTextItems]
  | item :: rest =>
    show blockTextItems s ((numberFloatItems wf (numberFloatList wf c #[] item.toList).1
      (acc.push (numberFloatList wf c #[] item.toList).2) rest).2).toList = _
    rw [numberFloatItems_text (numberFloatList wf c #[] item.toList).1
      (acc.push (numberFloatList wf c #[] item.toList).2) rest s]
    rw [Array.toList_push, blockTextItems_chain]
    simp [blockTextItems, numberFloatList_text c #[] item.toList, blockTextList]

private theorem numberFloatCols_text {wf : Bool} (c : FloatCtr)
    (acc : Array (BoxWidth × Array Block))
    (cols : List (BoxWidth × Array Block)) (s : String) :
    blockTextColumns s ((numberFloatCols wf c acc cols).2).toList
      = blockTextColumns (blockTextColumns s acc.toList) cols := by
  match cols with
  | [] => simp [numberFloatCols, blockTextColumns]
  | (w, body) :: rest =>
    show blockTextColumns s ((numberFloatCols wf (numberFloatList wf c #[] body.toList).1
      (acc.push (w, (numberFloatList wf c #[] body.toList).2)) rest).2).toList = _
    rw [numberFloatCols_text (numberFloatList wf c #[] body.toList).1
      (acc.push (w, (numberFloatList wf c #[] body.toList).2)) rest s]
    rw [Array.toList_push, blockTextColumns_chain]
    simp [blockTextColumns, numberFloatList_text c #[] body.toList, blockTextList]

end

public theorem numberFloats_text (within : Bool) :
    Conserves blocksText (numberFloats · within) := fun xs => by
  simp [blocksText, numberFloats, numberFloatList_text (wf := within) {} #[] xs.toList "",
    blockTextList]

private theorem blockTextBibItems_chain (l1 l2 : List BibItem) (acc : String) :
    blockTextBibItems acc (l1 ++ l2)
      = blockTextBibItems (blockTextBibItems acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextBibItems]
  | cons item rest ih => simp [blockTextBibItems, ih]

private theorem blockTextContentsEntries_chain (l1 l2 : List ContentsEntry) (acc : String) :
    blockTextContentsEntries acc (l1 ++ l2)
      = blockTextContentsEntries (blockTextContentsEntries acc l1) l2 := by
  induction l1 generalizing acc with
  | nil => simp [blockTextContentsEntries]
  | cons e rest ih => simp [blockTextContentsEntries, ih]

/-- The backend names an `{ifbackend}` target may spell, one per emitter. -/
public def backendNames : List String := ["pdf", "html", "md"]

/-- Whether backend `t` keeps this block; only a conditional can exclude one. -/
@[expose] public def keptBy (t : String) : Block → Bool
  | .only targets _ => targets.contains t
  | .para _ | .equation _ _ | .section _ _ _ _ | .list _ _ _ | .center _ | .ragged _ _
  | .quote _ _ | .lines _ | .abstract _
  | .role _ _ | .link _ _
  | .titled _ _ _ | .disclosure _ _ _
  | .spaced _ _
  | .verbatim _ _ _ | .columns _ | .onSteps _ _ | .note _ | .logo _
  | .altSteps _ _ _
  | .frame _ _ _ _ _ | .framefoot _ | .setPalette _ | .setTokens _
  | .rule _ _ _ | .nav _ _ | .picture _ | .pagebreak | .algorithm _ _ _
  | .table _ _ _ _ _ _ | .float _ _ _ _ _ | .bibliography _ _ _ | .contents _ _ => true

mutual

/-- The document as backend `t` sees it: an `.only` block whose targets
exclude `t` is dropped whole, everything else kept. -/
@[expose] public def keepForOne (t : String) : Block → Block
  | .only targets body => .only targets (keepForList t body.toList).toArray
  | .nav spec body => .nav spec (keepForList t body.toList).toArray
  | .list o s items => .list o s (keepForItems t items.toList).toArray
  | .center body => .center (keepForList t body.toList).toArray
  | .ragged s body => .ragged s (keepForList t body.toList).toArray
  | .quote q body => .quote q (keepForList t body.toList).toArray
  | .abstract body => .abstract (keepForList t body.toList).toArray
  | .titled kind title body => .titled kind title (keepForList t body.toList).toArray
  | .disclosure summary expanded body =>
    .disclosure summary expanded (keepForList t body.toList).toArray
  | .role n body => .role n (keepForList t body.toList).toArray
  | .link target body => .link target (keepForList t body.toList).toArray
  | .spaced g body => .spaced g (keepForList t body.toList).toArray
  | .columns cols => .columns (keepForColumns t cols.toList).toArray
  | .onSteps spec body => .onSteps spec (keepForList t body.toList).toArray
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (keepForList t firstPage.toList).toArray (keepForList t otherPage.toList).toArray
  | .note body => .note (keepForList t body.toList).toArray
  | .frame ti st v br body => .frame ti st v br (keepForList t body.toList).toArray
  | .para c => .para c
  | .lines ls => .lines ls
  | .equation n c => .equation n c
  | .section l st num title => .section l st num title
  | .verbatim c s sp => .verbatim c s sp
  | .logo c => .logo c
  | .framefoot c => .framefoot c
  | .setPalette pal => .setPalette pal
  | .setTokens tk => .setTokens tk
  | .pagebreak => .pagebreak
  | .rule c n th => .rule c n th
  | .picture p => .picture p
  | .table c pl pr rows rules spans => .table c pl pr rows rules spans
  | .algorithm n sm lines => .algorithm n sm lines
  | .float k n ca body caption => .float k n ca (keepForList t body.toList).toArray caption
  | .bibliography src style items => .bibliography src style items
  | .contents spec entries => .contents spec entries

@[expose] public def keepForList (t : String) : List Block → List Block
  | [] => []
  | b :: rest =>
    match keptBy t b with
    | true => keepForOne t b :: keepForList t rest
    | false => keepForList t rest

public def keepForItems (t : String) : List (Array Block) → List (Array Block)
  | [] => []
  | item :: rest => (keepForList t item.toList).toArray :: keepForItems t rest

public def keepForColumns (t : String) :
    List (BoxWidth × Array Block) → List (BoxWidth × Array Block)
  | [] => []
  | (w, body) :: rest => (w, (keepForList t body.toList).toArray) :: keepForColumns t rest

end

@[expose] public def keepFor (t : String) (xs : Array Block) : Array Block :=
  (keepForList t xs.toList).toArray

/-- Algorithm text leaves: each line's declared content one leaf, its comment another. -/
private def algTextLeaves (acc : List String) : List AlgLine → List String
  | [] => acc
  | l :: rest =>
    algTextLeaves (match l.comment with
      | some c => plainText c :: plainText l.content :: acc
      | none => plainText l.content :: acc) rest

private def textLeavesLaid (acc : List String) : List LaidLine → List String
  | [] => acc
  | l :: rest => textLeavesLaid (plainText l.content :: acc) rest

mutual

/-- Every text leaf of the blocks, most recent first: each paragraph's,
title's and verbatim block's plain text. -/
private def textLeavesList (acc : List String) : List Block → List String
  | [] => acc
  | b :: rest => textLeavesList (textLeavesOne acc b) rest

private def textLeavesOne (acc : List String) : Block → List String
  | .para content => plainText content :: acc
  | .equation _ content => plainText content :: acc
  | .section _ _ _ title => plainText title :: acc
  | .verbatim _ s spec =>
    match spec.caption with
    | some (_, cap) => s :: plainText cap :: acc
    | none => s :: acc
  | .logo content => plainText content :: acc
  | .framefoot content => plainText content :: acc
  | .setPalette _ => acc
  | .setTokens _ => acc
  | .pagebreak => acc
  | .list _ _ items => textLeavesItems acc items.toList
  | .center body => textLeavesList acc body.toList
  | .ragged _ body => textLeavesList acc body.toList
  | .quote _ body => textLeavesList acc body.toList
  | .lines ls => textLeavesLaid acc ls.toList
  | .abstract body => textLeavesList acc body.toList
  | .titled _ title body => textLeavesList (plainText title :: acc) body.toList
  | .disclosure title _ body => textLeavesList (plainText title :: acc) body.toList
  | .role _ body => textLeavesList acc body.toList
  | .link _ body => textLeavesList acc body.toList
  | .spaced _ body => textLeavesList acc body.toList
  | .columns cols => textLeavesColumns acc cols.toList
  | .onSteps _ body => textLeavesList acc body.toList
  | .altSteps _ firstPage otherPage =>
    textLeavesList (textLeavesList acc firstPage.toList) otherPage.toList
  | .note body => textLeavesList acc body.toList
  | .only _ body => textLeavesList acc body.toList
  | .nav _ body => textLeavesList acc body.toList
  | .frame title _ _ _ body => textLeavesList (plainText title :: acc) body.toList
  | .rule _ _ _ => acc
  | .picture _ => acc
  | .table _ _ _ rows _ _ => textLeavesTableRows acc rows.toList
  | .algorithm _ _ lines => algTextLeaves acc lines.toList
  | .float _ _ _ body caption => textLeavesList (plainText caption :: acc) body.toList
  | .bibliography _ _ items => textLeavesBibItems acc items.toList
  | .contents _ entries => textLeavesContentsEntries acc entries.toList

private def textLeavesBibItems (acc : List String) : List BibItem → List String
  | [] => acc
  | item :: rest => textLeavesBibItems (plainText item.content :: acc) rest

private def textLeavesContentsEntries (acc : List String) : List ContentsEntry → List String
  | [] => acc
  | e :: rest => textLeavesContentsEntries (plainText e.title :: acc) rest

private def textLeavesTableRows (acc : List String) :
    List (Array (Array Block)) → List String
  | [] => acc
  | row :: rest => textLeavesTableRows (textLeavesItems acc row.toList) rest

private def textLeavesItems (acc : List String) : List (Array Block) → List String
  | [] => acc
  | item :: rest => textLeavesItems (textLeavesList acc item.toList) rest

private def textLeavesColumns (acc : List String) :
    List (BoxWidth × Array Block) → List String
  | [] => acc
  | (_, body) :: rest => textLeavesColumns (textLeavesList acc body.toList) rest

end

public def textLeaves (xs : Array Block) : List String := textLeavesList [] xs.toList

mutual

/-- Whether along every nesting path each `.only` node's targets keep a member of `avail`. -/
private def orphanFreeList (avail : List String) : List Block → Bool
  | [] => true
  | b :: rest => orphanFreeOne avail b && orphanFreeList avail rest

private def orphanFreeOne (avail : List String) : Block → Bool
  | .only targets body =>
    let eff := avail.filter (fun a => targets.contains a)
    !eff.isEmpty && orphanFreeList eff body.toList
  | .list _ _ items => orphanFreeItems avail items.toList
  | .center body => orphanFreeList avail body.toList
  | .ragged _ body => orphanFreeList avail body.toList
  | .quote _ body => orphanFreeList avail body.toList
  | .abstract body => orphanFreeList avail body.toList
  | .titled _ _ body => orphanFreeList avail body.toList
  | .disclosure _ _ body => orphanFreeList avail body.toList
  | .role _ body => orphanFreeList avail body.toList
  | .link _ body => orphanFreeList avail body.toList
  | .spaced _ body => orphanFreeList avail body.toList
  | .columns cols => orphanFreeColumns avail cols.toList
  | .onSteps _ body => orphanFreeList avail body.toList
  | .altSteps _ firstPage otherPage =>
    orphanFreeList avail firstPage.toList && orphanFreeList avail otherPage.toList
  | .note body => orphanFreeList avail body.toList
  | .nav _ body => orphanFreeList avail body.toList
  | .frame _ _ _ _ body => orphanFreeList avail body.toList
  | .para _ | .lines _ | .equation _ _ | .section _ _ _ _ | .verbatim _ _ _ | .logo _
  | .framefoot _ | .setPalette _ | .setTokens _ | .algorithm _ _ _
  | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ | .pagebreak
  | .bibliography _ _ _ | .contents _ _ => true
  | .float _ _ _ body _ => orphanFreeList avail body.toList

private def orphanFreeItems (avail : List String) : List (Array Block) → Bool
  | [] => true
  | item :: rest => orphanFreeList avail item.toList && orphanFreeItems avail rest

private def orphanFreeColumns (avail : List String) :
    List (BoxWidth × Array Block) → Bool
  | [] => true
  | (_, body) :: rest =>
    orphanFreeList avail body.toList && orphanFreeColumns avail rest

end

public def orphanFree (avail : List String) (xs : Array Block) : Bool :=
  orphanFreeList avail xs.toList

private theorem algTextLeaves_acc (acc : List String) (ls : List AlgLine) :
    algTextLeaves acc ls = algTextLeaves [] ls ++ acc := by
  induction ls generalizing acc with
  | nil => simp [algTextLeaves]
  | cons l rest ih =>
    cases hc : l.comment with
    | none =>
      rw [algTextLeaves, algTextLeaves]
      simp only [hc]
      rw [ih (plainText l.content :: acc), ih [plainText l.content]]
      simp
    | some c =>
      rw [algTextLeaves, algTextLeaves]
      simp only [hc]
      rw [ih (plainText c :: plainText l.content :: acc),
        ih [plainText c, plainText l.content]]
      simp

private theorem textLeavesLaid_acc (acc : List String)
    (ls : List LaidLine) :
    textLeavesLaid acc ls = textLeavesLaid [] ls ++ acc := by
  induction ls generalizing acc with
  | nil => simp [textLeavesLaid]
  | cons l rest ih =>
    rw [textLeavesLaid, textLeavesLaid, ih (plainText l.content :: acc),
      ih [plainText l.content]]
    simp

mutual

private theorem textLeavesList_acc (acc : List String) (xs : List Block) :
    textLeavesList acc xs = textLeavesList [] xs ++ acc := by
  match xs with
  | [] => simp [textLeavesList]
  | b :: rest =>
    rw [textLeavesList, textLeavesList,
      textLeavesList_acc (textLeavesOne acc b) rest,
      textLeavesList_acc (textLeavesOne [] b) rest,
      textLeavesOne_acc acc b]
    simp [List.append_assoc]

private theorem textLeavesOne_acc (acc : List String) (b : Block) :
    textLeavesOne acc b = textLeavesOne [] b ++ acc := by
  match b with
  | .para c => simp [textLeavesOne]
  | .equation _ c => simp [textLeavesOne]
  | .section _ _ _ title => simp [textLeavesOne]
  | .verbatim c s sp => cases hc : sp.caption <;> simp [textLeavesOne, hc]
  | .logo c => simp [textLeavesOne]
  | .framefoot c => simp [textLeavesOne]
  | .setPalette _ => simp [textLeavesOne]
  | .setTokens _ => simp [textLeavesOne]
  | .pagebreak => simp [textLeavesOne]
  | .rule _ _ _ => simp [textLeavesOne]
  | .picture _ => simp [textLeavesOne]
  | .algorithm n sm lines =>
    rw [textLeavesOne, textLeavesOne]
    exact algTextLeaves_acc acc lines.toList
  | .list o _ items =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesItems_acc acc items.toList
  | .center body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .ragged _ body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .quote _ body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .lines ls =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesLaid_acc acc _
  | .abstract body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .titled k t body =>
    rw [textLeavesOne, textLeavesOne,
      textLeavesList_acc (plainText t :: acc) body.toList,
      textLeavesList_acc [plainText t] body.toList]
    simp
  | .disclosure t _ body =>
    rw [textLeavesOne, textLeavesOne,
      textLeavesList_acc (plainText t :: acc) body.toList,
      textLeavesList_acc [plainText t] body.toList]
    simp
  | .role n body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .link target body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .spaced g body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .columns cols =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesColumns_acc acc cols.toList
  | .onSteps spec body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .altSteps spec firstPage otherPage =>
    rw [textLeavesOne, textLeavesOne, textLeavesList_acc acc firstPage.toList,
      textLeavesList_acc (textLeavesList [] firstPage.toList ++ acc) otherPage.toList,
      textLeavesList_acc (textLeavesList [] firstPage.toList) otherPage.toList]
    simp [List.append_assoc]
  | .note body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .only targets body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .nav spec body =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesList_acc acc body.toList
  | .frame title st v _ body =>
    rw [textLeavesOne, textLeavesOne,
      textLeavesList_acc (plainText title :: acc) body.toList,
      textLeavesList_acc [plainText title] body.toList]
    simp
  | .table c pl pr rows rules spans =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesTableRows_acc acc rows.toList
  | .float k n ca body caption =>
    rw [textLeavesOne, textLeavesOne,
      textLeavesList_acc (plainText caption :: acc) body.toList,
      textLeavesList_acc [plainText caption] body.toList]
    simp
  | .bibliography src style items =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesBibItems_acc acc items.toList
  | .contents spec entries =>
    rw [textLeavesOne, textLeavesOne]
    exact textLeavesContentsEntries_acc acc entries.toList

private theorem textLeavesBibItems_acc (acc : List String) (items : List BibItem) :
    textLeavesBibItems acc items = textLeavesBibItems [] items ++ acc := by
  match items with
  | [] => simp [textLeavesBibItems]
  | item :: rest =>
    rw [textLeavesBibItems, textLeavesBibItems,
      textLeavesBibItems_acc (plainText item.content :: acc) rest,
      textLeavesBibItems_acc [plainText item.content] rest]
    simp

private theorem textLeavesContentsEntries_acc (acc : List String) (entries : List ContentsEntry) :
    textLeavesContentsEntries acc entries = textLeavesContentsEntries [] entries ++ acc := by
  match entries with
  | [] => simp [textLeavesContentsEntries]
  | e :: rest =>
    rw [textLeavesContentsEntries, textLeavesContentsEntries,
      textLeavesContentsEntries_acc (plainText e.title :: acc) rest,
      textLeavesContentsEntries_acc [plainText e.title] rest]
    simp

private theorem textLeavesItems_acc (acc : List String) (items : List (Array Block)) :
    textLeavesItems acc items = textLeavesItems [] items ++ acc := by
  match items with
  | [] => simp [textLeavesItems]
  | item :: rest =>
    rw [textLeavesItems, textLeavesItems,
      textLeavesItems_acc (textLeavesList acc item.toList) rest,
      textLeavesItems_acc (textLeavesList [] item.toList) rest,
      textLeavesList_acc acc item.toList]
    simp [List.append_assoc]

private theorem textLeavesColumns_acc (acc : List String)
    (cols : List (BoxWidth × Array Block)) :
    textLeavesColumns acc cols = textLeavesColumns [] cols ++ acc := by
  match cols with
  | [] => simp [textLeavesColumns]
  | (w, body) :: rest =>
    rw [textLeavesColumns, textLeavesColumns,
      textLeavesColumns_acc (textLeavesList acc body.toList) rest,
      textLeavesColumns_acc (textLeavesList [] body.toList) rest,
      textLeavesList_acc acc body.toList]
    simp [List.append_assoc]

private theorem textLeavesTableRows_acc (acc : List String)
    (rows : List (Array (Array Block))) :
    textLeavesTableRows acc rows = textLeavesTableRows [] rows ++ acc := by
  match rows with
  | [] => simp [textLeavesTableRows]
  | row :: rest =>
    rw [textLeavesTableRows, textLeavesTableRows,
      textLeavesTableRows_acc (textLeavesItems acc row.toList) rest,
      textLeavesTableRows_acc (textLeavesItems [] row.toList) rest,
      textLeavesItems_acc acc row.toList]
    simp [List.append_assoc]

end

private theorem keepForList_kept (t : String) (b : Block) (rest : List Block)
    (h : keptBy t b = true) :
    keepForList t (b :: rest) = keepForOne t b :: keepForList t rest := by
  rw [keepForList, h]

private theorem keepForList_dropped (t : String) (b : Block) (rest : List Block)
    (h : keptBy t b = false) :
    keepForList t (b :: rest) = keepForList t rest := by
  rw [keepForList, h]

mutual

private theorem keepForList_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (xs : List Block) (h : orphanFreeList avail xs = true) :
    ∀ s ∈ textLeavesList [] xs, ∃ t ∈ avail, s ∈ textLeavesList [] (keepForList t xs) := by
  match xs with
  | [] =>
    intro s hs
    simp [textLeavesList] at hs
  | b :: rest =>
    intro s hs
    rw [orphanFreeList, Bool.and_eq_true] at h
    rw [textLeavesList, textLeavesList_acc (textLeavesOne [] b) rest,
      List.mem_append] at hs
    cases hs with
    | inr hone =>
      obtain ⟨t, ht, hkept, hmem⟩ := keepForOne_covers avail t0 h0 b h.1 s hone
      refine ⟨t, ht, ?_⟩
      rw [keepForList_kept t b rest hkept, textLeavesList,
        textLeavesList_acc (textLeavesOne [] (keepForOne t b)) (keepForList t rest)]
      exact List.mem_append.mpr (.inr hmem)
    | inl hrest =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 rest h.2 s hrest
      refine ⟨t, ht, ?_⟩
      cases hk : keptBy t b with
      | true =>
        rw [keepForList_kept t b rest hk, textLeavesList,
          textLeavesList_acc (textLeavesOne [] (keepForOne t b)) (keepForList t rest)]
        exact List.mem_append.mpr (.inl hmem)
      | false =>
        rw [keepForList_dropped t b rest hk]
        exact hmem

private theorem keepForOne_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (b : Block) (h : orphanFreeOne avail b = true) :
    ∀ s ∈ textLeavesOne [] b,
      ∃ t ∈ avail, keptBy t b = true ∧ s ∈ textLeavesOne [] (keepForOne t b) := by
  match b with
  | .para c =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .lines ls =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .equation n c =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .section l st num title =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .verbatim c str sp =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .logo c =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .framefoot c =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .setPalette pal =>
    intro s hs
    simp [textLeavesOne] at hs
  | .setTokens tk =>
    intro s hs
    simp [textLeavesOne] at hs
  | .rule c n th =>
    intro s hs
    simp [textLeavesOne] at hs
  | .picture p =>
    intro s hs
    simp [textLeavesOne] at hs
  | .pagebreak =>
    intro s hs
    simp [textLeavesOne] at hs
  | .table c pl pr rows rules spans =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .algorithm n sm lines =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .bibliography src style items =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .contents spec entries =>
    intro s hs
    exact ⟨t0, h0, rfl, hs⟩
  | .float k n ca body caption =>
    intro s hs
    rw [textLeavesOne, textLeavesList_acc [plainText caption] body.toList,
      List.mem_append] at hs
    cases hs with
    | inr hcap =>
      refine ⟨t0, h0, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText caption]
          ((keepForList t0 body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inr hcap)
    | inl hbody =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hbody
      refine ⟨t, ht, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText caption]
          ((keepForList t body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inl (by simpa using hmem))
  | .center body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .ragged _ body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .quote _ body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .titled k ti body =>
    intro s hs
    rw [textLeavesOne, textLeavesList_acc [plainText ti] body.toList,
      List.mem_append] at hs
    cases hs with
    | inr hcap =>
      refine ⟨t0, h0, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText ti]
          ((keepForList t0 body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inr hcap)
    | inl hbody =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hbody
      refine ⟨t, ht, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText ti]
          ((keepForList t body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inl (by simpa using hmem))
  | .disclosure ti _ body =>
    intro s hs
    rw [textLeavesOne, textLeavesList_acc [plainText ti] body.toList,
      List.mem_append] at hs
    cases hs with
    | inr hcap =>
      refine ⟨t0, h0, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText ti]
          ((keepForList t0 body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inr hcap)
    | inl hbody =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hbody
      refine ⟨t, ht, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText ti]
          ((keepForList t body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inl (by simpa using hmem))
  | .abstract body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .role n body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .link target body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .spaced g body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .onSteps spec body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .altSteps spec firstPage otherPage =>
    intro s hs
    rw [orphanFreeOne, Bool.and_eq_true] at h
    rw [textLeavesOne, textLeavesList_acc, List.mem_append] at hs
    cases hs with
    | inl hso =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 otherPage.toList h.2 s hso
      refine ⟨t, ht, rfl, ?_⟩
      rw [keepForOne, textLeavesOne, textLeavesList_acc, List.mem_append]
      exact .inl (by simpa using hmem)
    | inr hsa =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 firstPage.toList h.1 s hsa
      refine ⟨t, ht, rfl, ?_⟩
      rw [keepForOne, textLeavesOne, textLeavesList_acc, List.mem_append]
      exact .inr (by simpa using hmem)
  | .note body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .nav spec body =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .list o _ items =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForItems_covers avail t0 h0 items.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .columns cols =>
    intro s hs
    rw [textLeavesOne] at hs
    obtain ⟨t, ht, hmem⟩ := keepForColumns_covers avail t0 h0 cols.toList h s hs
    exact ⟨t, ht, rfl, by simpa [keepForOne, textLeavesOne] using hmem⟩
  | .frame title st v _ body =>
    intro s hs
    rw [textLeavesOne, textLeavesList_acc [plainText title] body.toList,
      List.mem_append] at hs
    cases hs with
    | inr hti =>
      refine ⟨t0, h0, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText title] ((keepForList t0 body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inr hti)
    | inl hbody =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h s hbody
      refine ⟨t, ht, rfl, ?_⟩
      rw [keepForOne, textLeavesOne,
        textLeavesList_acc [plainText title] ((keepForList t body.toList).toArray.toList)]
      exact List.mem_append.mpr (.inl (by simpa using hmem))
  | .only targets body =>
    intro s hs
    rw [orphanFreeOne, Bool.and_eq_true] at h
    have hne : avail.filter (fun a => targets.contains a) ≠ [] := by
      intro he
      rw [he] at h
      simp [List.isEmpty] at h
    obtain ⟨t1, ht1⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨t, ht, hmem⟩ := keepForList_covers
      (avail.filter (fun a => targets.contains a)) t1 ht1 body.toList h.2 s
      (by simpa [textLeavesOne] using hs)
    have ht' := List.mem_filter.mp ht
    refine ⟨t, ht'.1, ht'.2, ?_⟩
    rw [keepForOne, textLeavesOne]
    simpa using hmem

private theorem keepForItems_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (items : List (Array Block)) (h : orphanFreeItems avail items = true) :
    ∀ s ∈ textLeavesItems [] items,
      ∃ t ∈ avail, s ∈ textLeavesItems [] (keepForItems t items) := by
  match items with
  | [] =>
    intro s hs
    simp [textLeavesItems] at hs
  | item :: rest =>
    intro s hs
    rw [orphanFreeItems, Bool.and_eq_true] at h
    rw [textLeavesItems, textLeavesItems_acc (textLeavesList [] item.toList) rest,
      List.mem_append] at hs
    cases hs with
    | inr hitem =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 item.toList h.1 s hitem
      refine ⟨t, ht, ?_⟩
      rw [keepForItems, textLeavesItems,
        textLeavesItems_acc (textLeavesList [] (keepForList t item.toList).toArray.toList)
          (keepForItems t rest)]
      exact List.mem_append.mpr (.inr (by simpa using hmem))
    | inl hrest =>
      obtain ⟨t, ht, hmem⟩ := keepForItems_covers avail t0 h0 rest h.2 s hrest
      refine ⟨t, ht, ?_⟩
      rw [keepForItems, textLeavesItems,
        textLeavesItems_acc (textLeavesList [] (keepForList t item.toList).toArray.toList)
          (keepForItems t rest)]
      exact List.mem_append.mpr (.inl hmem)

private theorem keepForColumns_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (cols : List (BoxWidth × Array Block))
    (h : orphanFreeColumns avail cols = true) :
    ∀ s ∈ textLeavesColumns [] cols,
      ∃ t ∈ avail, s ∈ textLeavesColumns [] (keepForColumns t cols) := by
  match cols with
  | [] =>
    intro s hs
    simp [textLeavesColumns] at hs
  | (w, body) :: rest =>
    intro s hs
    rw [orphanFreeColumns, Bool.and_eq_true] at h
    rw [textLeavesColumns, textLeavesColumns_acc (textLeavesList [] body.toList) rest,
      List.mem_append] at hs
    cases hs with
    | inr hbody =>
      obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 body.toList h.1 s hbody
      refine ⟨t, ht, ?_⟩
      rw [keepForColumns, textLeavesColumns,
        textLeavesColumns_acc (textLeavesList [] (keepForList t body.toList).toArray.toList)
          (keepForColumns t rest)]
      exact List.mem_append.mpr (.inr (by simpa using hmem))
    | inl hrest =>
      obtain ⟨t, ht, hmem⟩ := keepForColumns_covers avail t0 h0 rest h.2 s hrest
      refine ⟨t, ht, ?_⟩
      rw [keepForColumns, textLeavesColumns,
        textLeavesColumns_acc (textLeavesList [] (keepForList t body.toList).toArray.toList)
          (keepForColumns t rest)]
      exact List.mem_append.mpr (.inl hmem)

end

public theorem keepFor_covers (avail : List String) (t0 : String) (h0 : t0 ∈ avail)
    (xs : Array Block) (h : orphanFree avail xs = true) :
    ∀ s ∈ textLeaves xs, ∃ t ∈ avail, s ∈ textLeaves (keepFor t xs) := by
  intro s hs
  obtain ⟨t, ht, hmem⟩ := keepForList_covers avail t0 h0 xs.toList h s hs
  exact ⟨t, ht, by simpa [textLeaves, keepFor] using hmem⟩

mutual

/-- Whether no backend conditional stands anywhere in the blocks; hand-rolled
on `keepForList`'s skeleton for its proofs. -/
@[expose] public def onlyFreeList : List Block → Bool
  | [] => true
  | b :: rest => onlyFreeOne b && onlyFreeList rest

@[expose] public def onlyFreeOne : Block → Bool
  | .only _ _ => false
  | .list _ _ items => onlyFreeItems items.toList
  | .center body => onlyFreeList body.toList
  | .ragged _ body => onlyFreeList body.toList
  | .quote _ body => onlyFreeList body.toList
  | .abstract body => onlyFreeList body.toList
  | .titled _ _ body => onlyFreeList body.toList
  | .disclosure _ _ body => onlyFreeList body.toList
  | .role _ body => onlyFreeList body.toList
  | .link _ body => onlyFreeList body.toList
  | .spaced _ body => onlyFreeList body.toList
  | .columns cols => onlyFreeColumns cols.toList
  | .onSteps _ body => onlyFreeList body.toList
  | .altSteps _ firstPage otherPage =>
    onlyFreeList firstPage.toList && onlyFreeList otherPage.toList
  | .note body => onlyFreeList body.toList
  | .nav _ body => onlyFreeList body.toList
  | .frame _ _ _ _ body => onlyFreeList body.toList
  | .float _ _ _ body _ => onlyFreeList body.toList
  | .para _ | .lines _ | .equation _ _ | .section _ _ _ _ | .verbatim _ _ _ | .logo _
  | .framefoot _ | .setPalette _ | .setTokens _ | .rule _ _ _ | .picture _ | .algorithm _ _ _
  | .table _ _ _ _ _ _ | .pagebreak | .bibliography _ _ _ | .contents _ _ => true

public def onlyFreeItems : List (Array Block) → Bool
  | [] => true
  | item :: rest => onlyFreeList item.toList && onlyFreeItems rest

public def onlyFreeColumns : List (BoxWidth × Array Block) → Bool
  | [] => true
  | (_, body) :: rest => onlyFreeList body.toList && onlyFreeColumns rest

end

@[expose] public def onlyFree (xs : Array Block) : Bool := onlyFreeList xs.toList

mutual

public theorem keepForList_id (t : String) (xs : List Block)
    (h : onlyFreeList xs = true) : keepForList t xs = xs := by
  match xs with
  | [] => rfl
  | b :: rest =>
    rw [onlyFreeList, Bool.and_eq_true] at h
    have hk : keptBy t b = true := by
      cases b
      case only => exact absurd h.1 (by simp [onlyFreeOne])
      all_goals rfl
    rw [keepForList_kept t b rest hk, keepForOne_id t b h.1,
      keepForList_id t rest h.2]

public theorem keepForOne_id (t : String) (b : Block)
    (h : onlyFreeOne b = true) : keepForOne t b = b := by
  match b with
  | .only targets body => exact absurd h (by simp [onlyFreeOne])
  | .para c => rfl
  | .lines ls => rfl
  | .equation n c => rfl
  | .section l st num title => rfl
  | .verbatim c s sp => rfl
  | .logo c => rfl
  | .framefoot c => rfl
  | .setPalette pal => rfl
  | .setTokens tk => rfl
  | .pagebreak => rfl
  | .rule c n th => rfl
  | .picture p => rfl
  | .table c pl pr rows rules spans => rfl
  | .algorithm n sm lines => rfl
  | .bibliography src style items => rfl
  | .contents spec entries => rfl
  | .list o _ items =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForItems_id t items.toList h]
  | .center body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .ragged _ body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .quote _ body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .abstract body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .titled kind title body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .disclosure summary expanded body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .role n body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .link target body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .spaced g body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .columns cols =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForColumns_id t cols.toList h]
  | .onSteps spec body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .altSteps spec firstPage otherPage =>
    rw [onlyFreeOne, Bool.and_eq_true] at h
    simp [keepForOne, keepForList_id t firstPage.toList h.1,
      keepForList_id t otherPage.toList h.2]
  | .note body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .nav spec body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .frame ti st v _ body =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]
  | .float k n ca body caption =>
    rw [onlyFreeOne] at h
    simp [keepForOne, keepForList_id t body.toList h]

public theorem keepForItems_id (t : String) (items : List (Array Block))
    (h : onlyFreeItems items = true) : keepForItems t items = items := by
  match items with
  | [] => rfl
  | item :: rest =>
    rw [onlyFreeItems, Bool.and_eq_true] at h
    rw [keepForItems, keepForList_id t item.toList h.1,
      keepForItems_id t rest h.2]

public theorem keepForColumns_id (t : String) (cols : List (BoxWidth × Array Block))
    (h : onlyFreeColumns cols = true) : keepForColumns t cols = cols := by
  match cols with
  | [] => rfl
  | (w, body) :: rest =>
    rw [onlyFreeColumns, Bool.and_eq_true] at h
    rw [keepForColumns, keepForList_id t body.toList h.1,
      keepForColumns_id t rest h.2]

end

public theorem keepFor_id (t : String) (xs : Array Block) (h : onlyFree xs = true) :
    keepFor t xs = xs := by
  rw [keepFor, keepForList_id t xs.toList h]


/-- The `.bib` files one `\bibliography` marker names: its argument split at
commas, each name trimmed. -/
public def bibSourceNames (src : String) : Array String :=
  ((src.splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)).toArray

/-- The block face of `bibRefs`, over a body not yet assembled onto a `Doc`. -/
public def bibRefsBlocks (blocks : Array Block) : Array String :=
  foldBlocks (fun out b => match b with
    | .bibliography src _ _ => (bibSourceNames src).foldl (init := out) fun out s =>
        if out.contains s then out else out.push s
    | _ => out) (fun out _ => out) #[] blocks

/-- The items of every `thebibliography` (a `.bibliography` naming no `.bib`
source), in document order. -/
public def ownBibItemsBlocks (blocks : Array Block) : Array BibItem :=
  foldBlocks (fun out b => match b with
    | .bibliography "" _ items => items.foldl (·.push ·) out
    | _ => out) (fun out _ => out) #[] blocks

/-- Every `.bib` source the document's `\bibliography` markers name, in
document order, deduplicated. -/
public def bibRefs (doc : Doc) : Array String := bibRefsBlocks doc.body

/-- The document's first `\bibliographystyle`, `none` when nothing declared. -/
public def bibStyleName (doc : Doc) : Option String :=
  (foldBlocks (fun out b => match b with
    | .bibliography _ (some s) _ => out.push s
    | _ => out) (fun out _ => out) #[] doc.body)[0]?

/-- One image-source leaf into the collect, deduplicated, in document order. -/
private def imageSrcPush (out : Array String)
    (x : Inline) : Array String :=
  match x with
  | .image src _ _ => if out.contains src then out else out.push src
  | _ => out

/-- Every image source the inlines reference, in document order. -/
public def imageSrcsInlines (out : Array String) (xs : Array Inline) : Array String :=
  foldInlines imageSrcPush out xs

/-- Every inline region a backend sets beside the body, as one list. -/
public def furnitureInlines (doc : Doc) : Array (Array Inline) :=
  optRegion doc.head ++ optRegion doc.foot ++ optRegion doc.logo ++
    (match doc.headline with
      | some hl => #[hl.title, hl.author, hl.institute]
      | none => #[]) ++
    optRegion doc.logoLeft ++ optRegion doc.logoRight ++
    doc.styles.entries.flatMap (fun (_, st) =>
      optRegion st.font ++ optRegion st.authorFont ++ optRegion st.marker ++
        st.slots.flatMap fun slot =>
          slot.parts.flatMap fun part => #[part.content] ++ optRegion part.font) ++
    doc.itemLabels.map Prod.snd
where
  /-- An optional region as zero or one entries. -/
  optRegion : Option (Array Inline) → Array (Array Inline)
    | some r => #[r]
    | none => #[]

/-- `foldInlines` over the whole document: the body through `foldBlocks`, then
every furniture region, in `furnitureInlines`' order. -/
@[expose] public def foldDoc (fi : α → Inline → α) (acc : α) (doc : Doc)
    (fb : α → Block → α := fun acc _ => acc) : α :=
  (furnitureInlines doc).foldl (fun acc r => foldInlines fi acc r)
    (foldBlocks fb fi acc doc.body)

/-- The rewrite face of `foldDoc`: `fb` rewrites the body, `fi` each furniture region. -/
@[expose] public def mapDoc (fi : Array Inline → Array Inline) (fb : Array Block → Array Block)
    (doc : Doc) : Doc :=
  { doc with
    body := fb doc.body
    head := doc.head.map fi
    foot := doc.foot.map fi
    logo := doc.logo.map fi
    headline := doc.headline.map fun hl =>
      { title := fi hl.title, author := fi hl.author, institute := fi hl.institute }
    logoLeft := doc.logoLeft.map fi
    logoRight := doc.logoRight.map fi
    styles := { doc.styles with entries := doc.styles.entries.map fun (nm, st) =>
      (nm, { st with
        font := st.font.map fi
        authorFont := st.authorFont.map fi
        marker := st.marker.map fi
        slots := st.slots.map fun slot =>
          { slot with parts := slot.parts.map fun part =>
            { part with content := fi part.content, font := part.font.map fi } } }) }
    itemLabels := doc.itemLabels.map fun (lvl, l) => (lvl, fi l) }

private theorem optRegion_map (fi : Array Inline → Array Inline) (o : Option (Array Inline)) :
    furnitureInlines.optRegion (o.map fi) = (furnitureInlines.optRegion o).map fi := by
  cases o <;> simp [furnitureInlines.optRegion]

public theorem furnitureInlines_mapDoc (fi : Array Inline → Array Inline)
    (fb : Array Block → Array Block) (doc : Doc) :
    furnitureInlines (mapDoc fi fb doc) = (furnitureInlines doc).map fi := by
  unfold furnitureInlines mapDoc
  rw [← Array.toList_inj]
  cases doc.headline <;>
    simp [optRegion_map, Array.toList_append, Array.toList_map, Array.toList_flatMap,
      List.flatMap_map, List.map_flatMap, List.map_append]

public theorem foldInlineList_append (fi : α → Inline → α) (acc : α) (l₁ l₂ : List Inline) :
    foldInlineList fi acc (l₁ ++ l₂) = foldInlineList fi (foldInlineList fi acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons x rest ih => rw [List.cons_append, foldInlineList, foldInlineList, ih]

public theorem foldBlockList_append (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (l₁ l₂ : List Block) :
    foldBlockList fb fi acc (l₁ ++ l₂) = foldBlockList fb fi (foldBlockList fb fi acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons b rest ih => rw [List.cons_append, foldBlockList, foldBlockList, ih]

public theorem foldBlockItems_append (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (l₁ l₂ : List (Array Block)) :
    foldBlockItems fb fi acc (l₁ ++ l₂) = foldBlockItems fb fi (foldBlockItems fb fi acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons b rest ih => rw [List.cons_append, foldBlockItems, foldBlockItems, ih]

public theorem foldTableRows_append (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (l₁ l₂ : List (Array (Array Block))) :
    foldTableRows fb fi acc (l₁ ++ l₂) = foldTableRows fb fi (foldTableRows fb fi acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons b rest ih => rw [List.cons_append, foldTableRows, foldTableRows, ih]

public theorem foldBlockCols_append (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (l₁ l₂ : List (BoxWidth × Array Block)) :
    foldBlockCols fb fi acc (l₁ ++ l₂) = foldBlockCols fb fi (foldBlockCols fb fi acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons b rest ih =>
    obtain ⟨w, body⟩ := b
    rw [List.cons_append, foldBlockCols, foldBlockCols, ih]

private theorem foldBibItems_foldl (fi : α → Inline → α) (acc : α) (items : List BibItem) :
    foldBibItems fi acc items = items.foldl (fun acc it => foldInlines fi acc it.content) acc := by
  induction items generalizing acc with
  | nil => rfl
  | cons it rest ih => rw [foldBibItems, ih, List.foldl_cons]; rfl

public theorem foldBlock_bibliography_exact (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (src : String) (style : Option String) (items : Array BibItem) :
    foldBlock fb fi acc (.bibliography src style items) =
      items.foldl (fun acc it => foldInlines fi acc it.content)
        (fb acc (.bibliography src style items)) := by
  simp only [foldBlock, foldBibItems_foldl, Array.foldl_toList]

public theorem foldBlockList_push (fb : α → Block → α) (fi : α → Inline → α) (acc : α)
    (out : Array Block) (b : Block) :
    foldBlockList fb fi acc (out.push b).toList = foldBlock fb fi (foldBlockList fb fi acc out.toList) b := by
  rw [Array.toList_push, foldBlockList_append]
  rfl

/-- Every image the document references, deduplicated, in document order: the
request the CLI driver fulfils. -/
public def imageRefs (doc : Doc) : Array String := foldDoc imageSrcPush #[] doc

/-- An image request keeps its asset selector: two includes of different pages
in one PDF share no store entry. -/
private def imageRequestPush (out : Array Image.Request) : Inline → Array Image.Request
  | .image src spec _ =>
    let req := spec.request src
    if out.contains req then out else out.push req
  | .text _ | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _
  | .located _ _ | .role _ _ | .link _ _ | .label _ | .ref _ _ _ _ | .decorated _ _ | .boxed _ _ | .fill
  | .hspace _ _ | .rule _ _ _ | .pageNumber | .pageCount | .linebreak _
  | .strut _ | .italicCorr _ | .onSteps _ _ | .altSteps _ _ _ | .icon _ _
  | .cite _ _ | .cited _ _ _ | .footnote _ _ => out

public def imageRequests (doc : Doc) : Array Image.Request :=
  foldDoc imageRequestPush #[] doc

/-- The image-source prefix of a boundary picture, followed by the request's content hash. -/
public def picSrcPrefix : String := "leantex-pic:"

/-- The key a refusal for a withdrawn picture is named under: the picture's
id, then the refusal's own words. -/
public def picFragmentKey (id msg : String) : String := "picture:" ++ id ++ ":" ++ msg

/-- The key a picture in a line of text is named under where it is not drawn. -/
public def picInlineKey (id : String) : String := "picture:inline:" ++ id

/-- A picture body's or wrapped request's content key, in lower-case hex. -/
public def picHash (s : String) : String := (Flate.contentKey s.toUTF8).toLower

/-- A character a palette name holds: an ASCII letter or digit, `_` or `.`. -/
public def colorNameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.'

/-- The palette's name grammar: every maximal run of name characters in a colour expression or a
picture body, deduplicated in first-seen order. -/
private def colorNamesFlush (cur : String) (acc : Array String) : Array String :=
  if cur.isEmpty || acc.contains cur then acc else acc.push cur

private def colorNamesGo : List Char → String → Array String → Array String
  | [], cur, acc => colorNamesFlush cur acc
  | c :: rest, cur, acc =>
    if colorNameChar c then colorNamesGo rest (cur.push c) acc
    else colorNamesGo rest "" (colorNamesFlush cur acc)

public def colorNames (body : String) : Array String := colorNamesGo body.toList "" #[]

/-- A character that ends a colour expression in TeX source: a group, option or argument
delimiter, a key's `=`, or an extended expression's `:` and `;`. -/
private def mentionCut (c : Char) : Bool :=
  c == '{' || c == '}' || c == '[' || c == ']' || c == '(' || c == ')' || c == ',' || c == '=' ||
    c == ';' || c == ':'

/-- One unit of a source: its names where it stands as one colour expression, holding no space. -/
private def mentionUnit (unit : String) (acc : Array String) : Array String :=
  let u := unit.trimAscii.toString
  if u.isEmpty || u.any Char.isWhitespace then acc
  else (colorNamesGo u.toList "" #[]).foldl (·.push ·) acc

/-- Where the mention walk stands: in text, past a backslash, in a control word, or in a marker's
kind word or value, spelled `\ <kind> <value>`. -/
private inductive MentionAt where
  | text | escape | word | kind (k : String) | value (ink : Bool)

/-- The colour names a source spells where a colour expression stands: each argument, option or
key's value that is one expression, and a colour marker's value, so a word of prose and a control
sequence name no colour. -/
public def mentionedColorNames (src : String) : Array String := Id.run do
  let mut acc : Array String := #[]
  let mut cur := ""
  let mut mode := MentionAt.text
  for c in src.toList do
    match mode with
    | .escape =>
      mode := if c == ' ' then .kind "" else if c.isAlpha || c == '@' then .word else .text
    | .word =>
      unless c.isAlpha || c == '@' do
        mode := .text
        if mentionCut c || c == '\\' then
          if c == '\\' then mode := .escape
        else if !c.isWhitespace then cur := cur.push c
    | .kind k =>
      mode := if c == ' ' then .value ((Marker.Kind.words.lookup k).any Marker.Kind.carriesColor)
        else .kind (k.push c)
    | .value ink =>
      if mentionCut c || c.isWhitespace || c == '\\' then
        if ink then acc := mentionUnit cur acc
        cur := ""
        mode := if c == '\\' then .escape else .text
      else cur := cur.push c
    | .text =>
      if c == '\\' then
        acc := mentionUnit cur acc
        cur := ""
        mode := .escape
      else if mentionCut c then
        acc := mentionUnit cur acc
        cur := ""
      else cur := cur.push c
  return match mode with
    | .value false | .kind _ | .escape | .word => acc
    | .value true | .text => mentionUnit cur acc

/-- The palette roles a picture body mentions, each with the palette's value. -/
public def paletteDecls (pal : Palette) (body : String) : Array (String × Color) :=
  (colorNames body).filterMap fun n => (pal.find? n).map (n, ·)

/-- A CMYK component in thousandths as xcolor's `0`–`1` real, in its shortest spelling. -/
public def cmykPart (v : Nat) : String :=
  if v = 0 then "0"
  else if v ≥ 1000 then "1"
  else
    let s := toString v
    let padded := "".pushn '0' (3 - s.length) ++ s
    "0." ++ String.ofList (padded.toList.reverse.dropWhile (· == '0')).reverse

/-- One palette role as the `\definecolor` the boundary tool reads, in its
exact source model where declared. -/
public def colorDeclLine : String × Color → String
  | (n, c) => match c.pdfModel with
    | some (.rgb r g b) => s!"\\definecolor\{{n}}\{rgb}\{{r},{g},{b}}\n"
    | some (.gray v) => s!"\\definecolor\{{n}}\{gray}\{{v}}\n"
    | some (.cmyk cy m y k) => s!"\\definecolor\{{n}}\{cmyk}\{{cy},{m},{y},{k}}\n"
    | some (.separation i t) =>
      let tint := if t == 1 then "" else s!"!{Color.pdfRat (t * 100)}"
      s!"\\colorlet\{{n}}\{{i.xcolorName}{tint}}\n"
    | none => match c.cmyk with
      | some (cy, m, y, k) =>
        s!"\\definecolor\{{n}}\{cmyk}\{{cmykPart cy},{cmykPart m},{cmykPart y},{cmykPart k}}\n"
      | none => s!"\\definecolor\{{n}}\{RGB}\{{c.r},{c.g},{c.b}}\n"

/-- The document's declared font roles as the standalone's fontspec and
`unicode-math` preamble lines. -/
public def fontLines (fonts : FontSpec) : String :=
  let named (f : Option String) : Option String := f.filter fun fam =>
    !(fam.endsWith ".ttf" || fam.endsWith ".otf" || fam.endsWith ".ttc")
  let role (cmd : String) (f : Option String) : String :=
    match named f with
    | some fam => s!"\\{cmd}\{{fam}}\n"
    | none => ""
  let faces := role "setmainfont" fonts.body ++ role "setsansfont" fonts.sans ++
    role "setmonofont" fonts.mono ++
    String.join (fonts.families.toList.map fun (cmd, fam) => role s!"newfontfamily\\{cmd}" (some fam))
  let math := match named fonts.math with
    | some fam =>
      let opts := fonts.mathSources.options
      let load := if opts.isEmpty then "\\usepackage{unicode-math}\n"
        else s!"\\usepackage[{String.intercalate "," opts.toList}]\{unicode-math}\n"
      load ++ s!"\\setmathfont\{{fam}}\n"
    | none => ""
  if faces.isEmpty && math.isEmpty then "" else "\\usepackage{fontspec}\n" ++ faces ++ math

/-- TeX's control-word grammar: every backslash-led run of letters a source
spells, deduplicated in first-seen order. -/
private def ctrlNamesFlush (cur : Option String) (acc : Array String) : Array String :=
  match cur with
  | none => acc
  | some n => if n.isEmpty || acc.contains n then acc else acc.push n

private def ctrlNamesGo : List Char → Option String → Array String → Array String
  | [], cur, acc => ctrlNamesFlush cur acc
  | c :: rest, some n, acc =>
    if c.isAlpha then ctrlNamesGo rest (some (n.push c)) acc
    else ctrlNamesGo rest (if c == '\\' then some "" else none) (ctrlNamesFlush (some n) acc)
  | c :: rest, none, acc =>
    ctrlNamesGo rest (if c == '\\' then some "" else none) acc

public def ctrlNames (src : String) : Array String := ctrlNamesGo src.toList none #[]

/-- Consume each reachable declaration once, adding the names its body spells. -/
public def macroReachNames (pending : List (String × String)) (ns : Array String) : Array String :=
  match _h : pending.find? (fun p => ns.contains p.1) with
  | none => ns
  | some p => macroReachNames (pending.erase p) (ns ++ ctrlNames p.2)
termination_by pending.length
decreasing_by
  have hp := List.mem_of_find?_eq_some _h
  rw [List.length_erase_of_mem hp]
  have hn := List.length_pos_of_mem hp
  omega

/-- The document's own macro definitions a picture body reaches, transitively, in document order. -/
public def macroDecls (macros : Array (String × String)) (body : String) : Array (String × String) :=
  let ns := macroReachNames macros.toList (ctrlNames body)
  macros.filter fun p => ns.contains p.1

/-- The carried definitions as the standalone's preamble reads them, one
per line. -/
public def macroDeclLines (macros : Array (String × String)) : String :=
  macros.foldl (fun s p => s ++ p.2 ++ "\n") ""

/-- Each distinct ink the colours paint with, declared once as colorspace declares it. -/
public def inkDeclLines (colors : Array (String × Color)) : String :=
  let inks := colors.foldl (init := (#[] : Array Ink)) fun acc (_, c) => match c.ink? with
    | some (i, _) => if acc.any (·.name == i.name) then acc else acc.push i
    | none => acc
  if inks.isEmpty then "" else
    inks.foldl (init := "\\usepackage{colorspace}\n") fun s i =>
      s ++ s!"\\definespotcolor\{{i.xcolorName}}\{{i.name}}\
\{{Color.pdfRat i.c},{Color.pdfRat i.m},{Color.pdfRat i.y},{Color.pdfRat i.k}}\n"

/-- Wrap one picture body for the boundary as a `standalone` document carrying
the preamble, font roles, palette roles and macros it needs. -/
public def wrapStandalone (head preamble fonts : String) (colors : Array (String × Color))
    (shims : String) (macros : Array (String × String)) (switch : Option String)
    (src : PicSrc) : String :=
  head ++ preamble ++ fonts ++ inkDeclLines colors ++
    colors.foldl (fun s c => s ++ colorDeclLine c) "" ++ shims ++ macroDeclLines macros ++
    src.kind.docOpen switch ++ src.body ++ src.kind.docClose

/-- The class line and the TikZ load a standalone opens with, at the
document's body size where the class has an option for it. -/
@[expose] public def standaloneHead (body : Length) : String :=
  if body == Dim.pt 11 then "\\documentclass[11pt]{standalone}\n\\usepackage{tikz}\n"
  else if body == Dim.pt 12 then "\\documentclass[12pt]{standalone}\n\\usepackage{tikz}\n"
  else "\\documentclass{standalone}\n\\usepackage{tikz}\n"

/-- The size switch a request's standalone sets before its picture: the size
in force, by its ladder name. -/
public def pictureSwitch (page : PageSpec) (size : Option String) : Option String :=
  if page.fontSize == Dim.pt 10 || page.fontSize == Dim.pt 11 || page.fontSize == Dim.pt 12 then
    size.map ("\\" ++ ·)
  else
    let sz := scaleStepIn page.scale page.fontSize (size.getD "normalsize")
    some s!"\\fontsize\{{sz.toPtString}pt}\{{(leadingFor sz).toPtString}pt}\\selectfont"

public theorem wrapStandalone_picture_exact (preamble fonts : String)
    (colors : Array (String × Color)) (macros : Array (String × String)) (body : String) :
    wrapStandalone "\\documentclass{standalone}\n\\usepackage{tikz}\n" preamble fonts colors ""
        macros none { kind := .picture, body } =
      "\\documentclass{standalone}\n\\usepackage{tikz}\n" ++ preamble ++ fonts ++
        inkDeclLines colors ++
        colors.foldl (fun s c => s ++ colorDeclLine c) "" ++ "" ++ macroDeclLines macros ++
        "\\begin{document}\n\\begin{tikzpicture}" ++ body ++
        "\\end{tikzpicture}\n\\end{document}\n" := by
  simp only [wrapStandalone, PicKind.docOpen, PicKind.docClose]

/-- Beamer's `\alert` as a picture body spells it, read as a command name. -/
private def alertCtrl : String := "alert"

/-- What beamer defines that a beamer document's standalone does not:
`\alert`, where the picture spells it. -/
public def slideShims (doc : Doc) (roots : String) : String :=
  if doc.docClass != .slides && doc.docClass != .poster then "" else
  let alert :=
    if !(ctrlNames roots).contains alertCtrl then ""
    else if (Design.declared? doc.palette .alert).isSome then
      "\\providecommand{\\alert}{}\\RenewDocumentCommand{\\alert}{d<>m}\
{\\textcolor{alert}{\\ifmmode#2\\else\\bfseries#2\\fi}}\n"
    else
      "\\providecommand{\\alert}{}\\RenewDocumentCommand{\\alert}{d<>m}\
{\\ifmmode#2\\else{\\bfseries#2}\\fi}\n"
  let d := Design.ofPalette doc.palette
  let named := colorNames roots
  alert ++ ([("fg", d.fg), ("bg", d.bg)].filter fun (n, _) =>
    named.contains n && (doc.palette.find? n).isNone).foldl (fun s c => s ++ colorDeclLine c) ""

/-- The request one picture body states, formed from the finished document. -/
public def pictureRequest (doc : Doc) (src : PicSrc) (faces : FontSpec := doc.fonts) : String :=
  let roots := doc.picturePreamble ++ src.body
  let macros := macroDecls doc.pictureMacros roots
  wrapStandalone (standaloneHead doc.page.fontSize) doc.picturePreamble (fontLines faces)
    (paletteDecls doc.palette (macroDeclLines macros ++ roots)) (slideShims doc roots) macros
    (pictureSwitch doc.page src.size) src

/-- The document with boundary pictures `more` added to its request, each id once, its own first. -/
@[expose] public def Doc.addPictures (doc : Doc) (more : Array (String × PicSrc)) : Doc :=
  { doc with pictureSrcs := more.foldl (init := doc.pictureSrcs) fun acc (h, b) =>
      if acc.any (·.1 == h) then acc else acc.push (h, b) }

/-- The boundary requests the shipped tree states: `pictureSrcs` filtered to
the ids an `.image` node still references, each wrapped. -/
public def pictureRefs (doc : Doc) (faces : FontSpec := doc.fonts) : Array (String × String) :=
  let srcs := imageRefs doc
  (doc.pictureSrcs.filter fun (h, _) => srcs.contains (picSrcPrefix ++ h)).map
    fun (h, src) => (h, pictureRequest doc src faces)

/-- Blanks a standalone's spelling sets between a command and its operand. -/
private def skipBlanksL : List Char → List Char
  | [] => []
  | c :: rest => if c == ' ' || c == '\n' then skipBlanksL rest else c :: rest

/-- What follows an option bracket `[…]`, braces nesting inside it. -/
private def afterBracketL : Nat → List Char → List Char
  | _, [] => []
  | 0, ']' :: rest => rest
  | d, '{' :: rest => afterBracketL (d + 1) rest
  | d, '}' :: rest => afterBracketL (d - 1) rest
  | d, _ :: rest => afterBracketL d rest

/-- A braced operand's text, braces nesting inside it; `none` where it never
closes. -/
private def groupTextL : Nat → List Char → List Char → Option String
  | _, _, [] => none
  | 0, acc, '}' :: _ => some (String.ofList acc.reverse)
  | d + 1, acc, '}' :: rest => groupTextL d ('}' :: acc) rest
  | d, acc, '{' :: rest => groupTextL (d + 1) ('{' :: acc) rest
  | d, acc, c :: rest => groupTextL d (c :: acc) rest

/-- The file one `\includegraphics` call names, read from just after its
control word: the starred form, an option bracket, then the braced file. -/
private def includedFileL (cs : List Char) : Option String :=
  let cs := if cs.head? == some '*' then cs.drop 1 else cs
  let cs := skipBlanksL cs
  let cs := if cs.head? == some '[' then skipBlanksL (afterBracketL 0 (cs.drop 1)) else cs
  match cs with
  | '{' :: rest => (groupTextL 0 [] rest).map (·.trimAscii.toString)
  | _ => none

/-- The files a boundary request reads: every `\includegraphics` operand the
standalone spells, deduplicated in first-seen order. -/
public def pictureInputs (request : String) : Array String := Id.run do
  let pieces := request.splitOn "\\includegraphics"
  let mut out : Array String := #[]
  for piece in pieces.drop 1 do
    let cs := piece.toList
    if cs.head?.any Char.isAlpha then continue
    match includedFileL cs with
    | some f =>
      if !f.isEmpty && !f.contains '\\' && !f.contains '#' && !out.contains f then
        out := out.push f
    | none => pure ()
  return out

public theorem paletteDecls_covers (pal : Palette) (body n : String) (c : Color)
    (hn : n ∈ colorNames body) (hc : pal.find? n = some c) :
    (n, c) ∈ paletteDecls pal body := by
  unfold paletteDecls
  rw [Array.mem_filterMap]
  exact ⟨n, hn, by simp [hc]⟩

public theorem paletteDecls_agree (pal : Palette) (body n : String) (c : Color)
    (h : (n, c) ∈ paletteDecls pal body) : pal.find? n = some c := by
  unfold paletteDecls at h
  rw [Array.mem_filterMap] at h
  obtain ⟨m, _, hm⟩ := h
  cases hf : pal.find? m with
  | none => simp [hf] at hm
  | some c' =>
    simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hf

public theorem paletteDecls_mem (pal : Palette) (body n : String) (c : Color)
    (h : (n, c) ∈ paletteDecls pal body) : n ∈ colorNames body := by
  unfold paletteDecls at h
  rw [Array.mem_filterMap] at h
  obtain ⟨m, hm, he⟩ := h
  cases hf : pal.find? m with
  | none => simp [hf] at he
  | some c' =>
    simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact hm

private theorem filterMap_congr_mem {α β : Type} (f g : α → Option β) : ∀ (l : List α),
    (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons]
    rw [h a (List.mem_cons_self ..),
      filterMap_congr_mem f g l fun x hx => h x (List.mem_cons.mpr (Or.inr hx))]

public theorem paletteDecls_local_exact (pal pal' : Palette) (body : String)
    (h : ∀ n ∈ colorNames body, pal.find? n = pal'.find? n) :
    paletteDecls pal body = paletteDecls pal' body := by
  unfold paletteDecls
  apply Array.ext'
  simp only [Array.toList_filterMap]
  apply filterMap_congr_mem
  intro n hn
  rw [h n (Array.mem_def.mpr hn)]

public theorem macroReachNames_contract (pending : List (String × String)) (ns : Array String) :
    (∀ n ∈ ns, n ∈ macroReachNames pending ns) ∧
    (∀ p ∈ pending, p.1 ∈ macroReachNames pending ns →
      ∀ n ∈ ctrlNames p.2, n ∈ macroReachNames pending ns) := by
  induction pending, ns using macroReachNames.induct with
  | case1 pending ns h =>
    rw [macroReachNames, h]
    refine ⟨fun _ h => h, ?_⟩
    intro p hp hn
    exact False.elim ((List.find?_eq_none.mp h p hp) (Array.contains_iff_mem.mpr hn))
  | case2 pending ns p h ih =>
    rw [macroReachNames, h]
    refine ⟨fun n hn => ih.1 n (Array.mem_append_left _ hn), ?_⟩
    intro q hq hn n hdep
    by_cases he : q = p
    · subst q
      exact ih.1 n (Array.mem_append_right _ hdep)
    · exact ih.2 q ((List.mem_erase_of_ne he).mpr hq) hn n hdep

public theorem macroDecls_covers (macros : Array (String × String)) (body n d : String)
    (hn : n ∈ ctrlNames body) (hm : (n, d) ∈ macros) :
    (n, d) ∈ macroDecls macros body := by
  simp only [macroDecls]
  refine Array.mem_filter.mpr ⟨hm, ?_⟩
  exact Array.contains_iff_mem.mpr
    ((macroReachNames_contract macros.toList (ctrlNames body)).1 n hn)

public theorem macroDecls_fixed_point (macros : Array (String × String)) (body n d : String)
    (hm : (n, d) ∈ macros)
    (hr : ∃ p ∈ macroDecls macros body, n ∈ ctrlNames p.2) :
    (n, d) ∈ macroDecls macros body := by
  obtain ⟨p, hp, hn⟩ := hr
  simp only [macroDecls] at hp ⊢
  obtain ⟨hm', hp⟩ := Array.mem_filter.mp hp
  refine Array.mem_filter.mpr ⟨hm, Array.contains_iff_mem.mpr ?_⟩
  exact (macroReachNames_contract macros.toList (ctrlNames body)).2 p
    (Array.mem_def.mp hm') (Array.contains_iff_mem.mp hp) n hn

public theorem macroDecls_mem (macros : Array (String × String)) (body : String)
    (p : String × String) (h : p ∈ macroDecls macros body) : p ∈ macros :=
  (Array.mem_filter.mp h).1

public theorem pictureRefs_design_projects (doc : Doc) (faces : FontSpec)
    (id w : String)
    (h : (id, w) ∈ pictureRefs doc faces) :
    ∃ src, (id, src) ∈ doc.pictureSrcs ∧
      w = wrapStandalone (standaloneHead doc.page.fontSize) doc.picturePreamble
        (fontLines faces)
        (paletteDecls doc.palette
          (macroDeclLines (macroDecls doc.pictureMacros (doc.picturePreamble ++ src.body)) ++
            (doc.picturePreamble ++ src.body)))
        (slideShims doc (doc.picturePreamble ++ src.body))
        (macroDecls doc.pictureMacros (doc.picturePreamble ++ src.body))
        (pictureSwitch doc.page src.size) src := by
  unfold pictureRefs at h
  rw [Array.mem_map] at h
  obtain ⟨⟨id', src⟩, hmem, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨src, (Array.mem_filter.mp hmem).1, rfl⟩

public theorem boundary_request_env_free (doc : Doc) (t : Option String) :
    pictureRefs { doc with pictureTool := t } = pictureRefs doc := by rfl

/-- The logo in force at position `k`: the last span whose key is at or before
`k`, else the preamble's `init`. -/
public def logoInForce (init : Option (Array Inline))
    (spans : Array (Nat × Array Inline)) (k : Nat) : Option (Array Inline) :=
  spans.foldl (fun acc s => if s.1 ≤ k then some s.2 else acc) init

private theorem logoInForceList_rekey (f : Nat → Nat) (k : Nat) :
    ∀ (l : List (Nat × Array Inline)),
      (∀ s ∈ l, (f s.1 ≤ f k) ↔ (s.1 ≤ k)) →
      ∀ (init : Option (Array Inline)),
        l.foldl (fun acc s => if f s.1 ≤ f k then some s.2 else acc) init =
          l.foldl (fun acc s => if s.1 ≤ k then some s.2 else acc) init := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons s rest ih =>
    intro h init
    simp only [List.foldl_cons]
    have hs := h s (List.mem_cons_self ..)
    have hrest := fun t ht => h t (List.mem_cons_of_mem _ ht)
    simp only [hs]
    exact ih hrest _

public theorem logo_frames_agree (init : Option (Array Inline))
    (spans : Array (Nat × Array Inline)) (f : Nat → Nat) (k : Nat)
    (h : ∀ s ∈ spans, (f s.1 ≤ f k) ↔ (s.1 ≤ k)) :
    logoInForce init (spans.map fun s => (f s.1, s.2)) (f k) =
      logoInForce init spans k := by
  unfold logoInForce
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map,
    List.foldl_map]
  exact logoInForceList_rekey f k spans.toList
    (fun s hs => h s (by simpa using hs)) init

/-- The logo's declared alignment in the furniture band:
`\style{logo}{ align = ... }`, else `right`. -/
public def logoAlign (styles : Styles) : HAlign :=
  ((styles.find? "logo").bind (·.align)).getD .right

/-- Every image source the logo state ships: the preamble `\logo` and each
body declaration's content. -/
public def logoImageSrcs (doc : Doc) : Array String :=
  let out := foldBlocks (fun out b => match b with
    | .logo c => imageSrcsInlines out c
    | _ => out) (fun out _ => out) #[] doc.body
  let out := match doc.logo with | some l => imageSrcsInlines out l | none => out
  let out := match doc.logoLeft with | some l => imageSrcsInlines out l | none => out
  match doc.logoRight with | some r => imageSrcsInlines out r | none => out

private structure SansAltCensus where
  missing : Array String := #[]
  pictures : Nat := 0

/-- One image node's contribution to the no-alternative census: an `.image`
whose `alt` is `.undeclared`, its `src` once. -/
private def sansAltStep (out : SansAltCensus) (x : Inline) : SansAltCensus :=
  match x with
  | .image src _ alt =>
    if alt == .undeclared && !out.missing.contains src then
      { out with missing := out.missing.push src }
    else out
  | _ => out

/-- The census key prefix of a native picture: `picture#k`, its index among
native pictures in document order. -/
public def picKeyPrefix : String := "picture#"

/-- One native picture's contribution to the no-alternative census, judged on its `alternative`. -/
private def sansAltPicStep (out : SansAltCensus) (b : Block) : SansAltCensus :=
  match b with
  | .picture pic =>
    let key := picKeyPrefix ++ toString out.pictures
    { missing := if pic.alternative == .undeclared then out.missing.push key else out.missing
      pictures := out.pictures + 1 }
  | _ => out

/-- Every non-text object the artifacts ship with no text alternative, in document order. -/
public def imagesSansAlt (doc : Doc) : Array String :=
  let out := foldBlocks sansAltPicStep sansAltStep {} doc.body
  let out := match doc.head with | some h => foldInlines sansAltStep out h | none => out
  let out := match doc.foot with | some f => foldInlines sansAltStep out f | none => out
  out.missing.filter (fun src => !(logoImageSrcs doc).contains src)

/-- The picture faces' one message and help, native and boundary alike. -/
public def pictureSansAltMessage : String := Diag.say .N0376 .altText

public def pictureSansAltHelp : String :=
  "describe the picture — \\begin{tikzpicture}[alt={...}] — mark it " ++
    "decorative with [artifact], or caption a figure around it; an empty " ++
    "alt= says nothing"

/-- The text-alternative judge for file images and native pictures (WCAG 2.2
SC 1.1.1): one diagnostic per distinct object. -/
public def altDiags (doc : Doc) (spanOf : String → Option Span := fun _ => none) :
    Array Diag :=
  ((imagesSansAlt doc).filter fun src => !src.startsWith picSrcPrefix).map fun src =>
    let span := spanOf src
    if src.startsWith picKeyPrefix then
      Diag.of .N0376 pictureSansAltMessage span
        (help := some pictureSansAltHelp) (subject := some src)
    else
      Diag.of .N0376 (Diag.say .N0376 .altText (obj := some (some .image, src)))
        span
        (help := some ("describe the image — \\includegraphics[alt={...}] — " ++
          "mark it decorative with [artifact], or caption its figure: the " ++
          "caption becomes the alternative"))
        (subject := some src)

/-- The text-alternative judge for boundary pictures, read after fulfilment;
`shipped` says whether the drawn box embeds. -/
public def picAltDiags (doc : Doc) (spanOf : String → Option Span)
    (shipped : String → Bool) : Array Diag :=
  ((imagesSansAlt doc).filter fun src =>
      src.startsWith picSrcPrefix && shipped src).map fun src =>
    let span := spanOf src
    Diag.of .N0376 pictureSansAltMessage span
      (help := some pictureSansAltHelp) (subject := some src)

private theorem length_filter_partition (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter (fun a => !p a)).length = l.length
  | [] => rfl
  | a :: l => by
    have ih := length_filter_partition p l
    cases h : p a <;> simp [h] <;> omega

private theorem size_filter_partition (p : α → Bool) (as : Array α) :
    (as.filter (fun a => !p a)).size + (as.filter p).size = as.size := by
  have h1 := congrArg List.length (Array.toList_filter (p := fun a => !p a) (xs := as))
  have h2 := congrArg List.length (Array.toList_filter (p := p) (xs := as))
  have h3 := length_filter_partition p as.toList
  simp only [Array.length_toList] at h1 h2 h3
  omega

public theorem alt_judged_complete (doc : Doc) (spanOf : String → Option Span) :
    (altDiags doc spanOf).size + (picAltDiags doc spanOf (fun _ => true)).size =
      (imagesSansAlt doc).size := by
  rw [altDiags, picAltDiags, Array.size_map, Array.size_map]
  simp only [Bool.and_true]
  exact size_filter_partition (fun src => src.startsWith picSrcPrefix)
    (imagesSansAlt doc)

/-- The text a link's body offers the accessibility tree: its plain text and
each contained image's declared alternative. -/
public def linkReading (body : Array Inline) : String :=
  foldInlines
    (fun s x => match x with | .image _ _ alt => s ++ alt.text | _ => s)
    (plainText body) body

/-- One link node's contribution to the no-text census: a `.link` whose body
reads as nothing, its target once. -/
private def sansTextLinkStep (out : Array String)
    (x : Inline) : Array String :=
  match x with
  | .link url body =>
    if (linkReading body).isEmpty && !out.contains url then out.push url
    else out
  | _ => out

private def sansTextBlockLinkStep (out : Array String)
    (b : Block) : Array String :=
  match b with
  | .link target body =>
    if (blockLinkReading body).isEmpty && !out.contains target then out.push target else out
  | .para _ | .equation _ _ | .section _ _ _ _ | .list _ _ _ | .center _ | .ragged _ _
  | .spaced _ _ | .role _ _ | .quote _ _ | .lines _ | .abstract _ | .titled _ _ _ | .disclosure _ _ _ | .verbatim _ _ _
  | .algorithm _ _ _ | .columns _ | .onSteps _ _ | .altSteps _ _ _ | .note _ | .only _ _
  | .nav _ _ | .logo _ | .pagebreak | .frame _ _ _ _ _ | .framefoot _ | .setPalette _
  | .setTokens _ | .rule _ _ _ | .picture _ | .table _ _ _ _ _ _ | .float _ _ _ _ _
  | .bibliography _ _ _ => out
  | .contents _ entries => entries.foldl (fun out e => e.inline.foldl sansTextLinkStep out) out

/-- Every link the artifacts ship with no reading, deduplicated by target, in document order. -/
public def linksSansText (doc : Doc) : Array String :=
  let out := foldBlocks sansTextBlockLinkStep sansTextLinkStep #[] doc.body
  let out := match doc.head with | some h => foldInlines sansTextLinkStep out h | none => out
  let out := match doc.foot with | some f => foldInlines sansTextLinkStep out f | none => out
  match doc.logo with | some l => foldInlines sansTextLinkStep out l | none => out

/-- The link-purpose judge (WCAG 2.2 SC 2.4.4): one diagnostic per distinct target. -/
public def linkDiags (doc : Doc) : Array Diag :=
  (linksSansText doc).map fun (url : String) =>
    Diag.of .W0377 (Diag.say .W0377 .text (obj := some (some .link, url)))
      (help := some ("give the link visible text — \\href{...}{words} — " ++
        "or an image with alt inside it"))

public theorem links_judged_complete (doc : Doc) :
    linkDiags doc = #[] ↔ linksSansText doc = #[] := by
  rw [← Array.size_eq_zero_iff, ← Array.size_eq_zero_iff, linkDiags,
    Array.size_map]

mutual

/-- One leaf-parameterised map for every leaf rewrite: `f` rewrites childless
nodes, `finish` combines each completed sibling array. -/
@[expose] public def mapInlines (f : Inline → Inline) (xs : Array Inline)
    (finish : Array Inline → Array Inline := id) : Array Inline :=
  mapInlineList f #[] xs.toList finish

@[expose] public def mapInlineList (f : Inline → Inline) (out : Array Inline) (xs : List Inline)
    (finish : Array Inline → Array Inline := id) : Array Inline :=
  match xs with
  | [] => finish out
  | x :: rest => mapInlineList f (out.push (mapInline f x finish)) rest finish

@[expose] public def mapInline (f : Inline → Inline) (x : Inline)
    (finish : Array Inline → Array Inline := id) : Inline :=
  match x with
  | .styled st body => .styled st (mapInlineList f #[] body.toList finish)
  | .colored c n body => .colored c n (mapInlineList f #[] body.toList finish)
  | .located span body => .located span (mapInlineList f #[] body.toList finish)
  | .role n body => .role n (mapInlineList f #[] body.toList finish)
  | .link u body => .link u (mapInlineList f #[] body.toList finish)
  | .decorated kind body => .decorated kind (mapInlineList f #[] body.toList finish)
  | .boxed b body => .boxed b (mapInlineList f #[] body.toList finish)
  | .onSteps spec body => .onSteps spec (mapInlineList f #[] body.toList finish)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (mapInlineList f #[] firstPage.toList finish)
      (mapInlineList f #[] otherPage.toList finish)
  | .footnote n body => .footnote n (mapInlineList f #[] body.toList finish)
  | .cited tx keys ink => .cited tx keys (mapInlineList f #[] ink.toList finish)
  | .text s => f (.text s)
  | .math d src => f (.math d src)
  | .formula d src body => f (.formula d src body)
  | .image src size alt => f (.image src size alt)
  | .icon s l => f (.icon s l)
  | .label k => f (.label k)
  | .ref k p t tg => f (.ref k p t tg)
  | .cite tx keys => f (.cite tx keys)
  | .fill => f .fill
  | .hspace g keep => f (.hspace g keep)
  | .rule w h r => f (.rule w h r)
  | .strut h => f (.strut h)
  | .italicCorr m => f (.italicCorr m)
  | .pageNumber => f .pageNumber
  | .pageCount => f .pageCount
  | .linebreak e => f (.linebreak e)

end

@[expose] public def mapBibItems (f : Inline → Inline) (out : Array BibItem) (items : List BibItem)
    (finish : Array Inline → Array Inline := id) : Array BibItem :=
  match items with
  | [] => out
  | i :: rest =>
    mapBibItems f (out.push { i with content := mapInlines f i.content finish }) rest finish

@[expose] public def mapContentsEntries (f : Inline → Inline) (out : Array ContentsEntry)
    (entries : List ContentsEntry) (finish : Array Inline → Array Inline := id) :
    Array ContentsEntry :=
  match entries with
  | [] => out
  | e :: rest =>
    mapContentsEntries f (out.push { e with title := mapInlines f e.title finish }) rest finish

@[expose] public def mapAlgLines (f : Inline → Inline) (out : Array AlgLine) (ls : List AlgLine)
    (finish : Array Inline → Array Inline := id) : Array AlgLine :=
  match ls with
  | [] => out
  | l :: rest =>
    mapAlgLines f (out.push
      { depth := l.depth
        kind := l.kind
        content := mapInlines f l.content finish
        comment := l.comment.map (mapInlines f · finish) }) rest finish

@[expose] public def mapLaidLines (f : Inline → Inline) (out : Array LaidLine) (ls : List LaidLine)
    (finish : Array Inline → Array Inline := id) : Array LaidLine :=
  match ls with
  | [] => out
  | l :: rest =>
    mapLaidLines f (out.push { depth := l.depth, content := mapInlines f l.content finish }) rest finish

mutual

/-- The block face of the generic map: `gp` rewrites native pictures, `f`
childless inlines, `finish` completed regions, `listing` listing
specifications. -/
@[expose] public def mapBlocksPic (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (xs : Array Block) (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Array Block :=
  mapBlockList gp f #[] xs.toList finish listing

/-- The generic map with every picture passed through untouched; a rewrite
that must reach label text uses `mapBlocksPic`. -/
@[expose] public def mapBlocks (f : Inline → Inline) (xs : Array Block)
    (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Array Block :=
  mapBlocksPic id f xs finish listing

@[expose] public def mapBlockList (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (out : Array Block) (bs : List Block) (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Array Block :=
  match bs with
  | [] => out
  | b :: rest =>
    mapBlockList gp f (out.push (mapBlock gp f b finish listing)) rest finish listing
termination_by structural bs

@[expose] public def mapBlock (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline) (b : Block)
    (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Block :=
  match b with
  | .para content => .para (mapInlines f content finish)
  | .equation n content => .equation (mapInlines f n finish) (mapInlines f content finish)
  | .section l st n title => .section l st n (mapInlines f title finish)
  | .list o s items => .list o s (mapBlockItems gp f #[] items.toList finish listing)
  | .center body => .center (mapBlockList gp f #[] body.toList finish listing)
  | .ragged s body => .ragged s (mapBlockList gp f #[] body.toList finish listing)
  | .quote q body => .quote q (mapBlockList gp f #[] body.toList finish listing)
  | .lines ls => .lines (mapLaidLines f #[] ls.toList finish)
  | .abstract body => .abstract (mapBlockList gp f #[] body.toList finish listing)
  | .titled kind title body =>
    .titled kind (mapInlines f title finish) (mapBlockList gp f #[] body.toList finish listing)
  | .disclosure summary expanded body =>
    .disclosure (mapInlines f summary finish) expanded
      (mapBlockList gp f #[] body.toList finish listing)
  | .role n body => .role n (mapBlockList gp f #[] body.toList finish listing)
  | .link target body => .link target (mapBlockList gp f #[] body.toList finish listing)
  | .spaced g body => .spaced g (mapBlockList gp f #[] body.toList finish listing)
  | .columns cols => .columns (mapBlockCols gp f #[] cols.toList finish listing)
  | .onSteps spec body => .onSteps spec (mapBlockList gp f #[] body.toList finish listing)
  | .altSteps spec firstPage otherPage =>
    .altSteps spec (mapBlockList gp f #[] firstPage.toList finish listing)
      (mapBlockList gp f #[] otherPage.toList finish listing)
  | .only targets body => .only targets (mapBlockList gp f #[] body.toList finish listing)
  | .nav spec body => .nav spec (mapBlockList gp f #[] body.toList finish listing)
  | .note body => .note (mapBlockList gp f #[] body.toList finish listing)
  | .frame title st v br body =>
    .frame (mapInlines f title finish) st v br (mapBlockList gp f #[] body.toList finish listing)
  | .framefoot content => .framefoot (mapInlines f content finish)
  | .float k num ca body caption =>
    .float k num ca (mapBlockList gp f #[] body.toList finish listing)
      (mapInlines f caption finish)
  | .table c pl pr rows rules spans =>
    .table c pl pr (mapTableRows gp f #[] rows.toList finish listing) rules spans
  | .algorithm n sm ls => .algorithm n sm (mapAlgLines f #[] ls.toList finish)
  | .logo content => .logo (mapInlines f content finish)
  | .bibliography src style items =>
    .bibliography src style (mapBibItems f #[] items.toList finish)
  | .contents spec entries => .contents spec (mapContentsEntries f #[] entries.toList finish)
  | .verbatim c s spec =>
    .verbatim c s (listing { spec with caption := spec.caption.map fun (n, cap) =>
      (n, mapInlines f cap finish) })
  | .setPalette pal => .setPalette pal
  | .setTokens tk => .setTokens tk
  | .pagebreak => .pagebreak
  | .rule c n th => .rule c n th
  | .picture pic => .picture (gp pic)
termination_by structural b

public def mapBlockItems (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (out : Array (Array Block)) (items : List (Array Block))
    (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Array (Array Block) :=
  match items with
  | [] => out
  | item :: rest =>
    mapBlockItems gp f (out.push (mapBlockList gp f #[] item.toList finish listing))
      rest finish listing
termination_by structural items

public def mapBlockCols (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (out : Array (BoxWidth × Array Block)) (cols : List (BoxWidth × Array Block))
    (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Array (BoxWidth × Array Block) :=
  match cols with
  | [] => out
  | (w, body) :: rest =>
    mapBlockCols gp f (out.push (w, mapBlockList gp f #[] body.toList finish listing))
      rest finish listing
termination_by structural cols

public def mapTableRows (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (out : Array (Array (Array Block))) (rows : List (Array (Array Block)))
    (finish : Array Inline → Array Inline := id)
    (listing : ListingSpec → ListingSpec := id) : Array (Array (Array Block)) :=
  match rows with
  | [] => out
  | row :: rest =>
    mapTableRows gp f (out.push (mapBlockItems gp f #[] row.toList finish listing))
      rest finish listing
termination_by structural rows

end

@[expose] public def resolveMathAlphaInline (coverage : Math.MathAlphabetCoverage) : Inline → Inline
  | .formula display src body =>
    .formula display src (Math.resolveMathAlphas coverage body)
  | .styled st body => .styled st body
  | .colored c n body => .colored c n body
  | .located n body => .located n body
  | .role n body => .role n body
  | .link u body => .link u body
  | .decorated kind body => .decorated kind body
  | .boxed b body => .boxed b body
  | .onSteps spec body => .onSteps spec body
  | .altSteps spec active otherwise => .altSteps spec active otherwise
  | .footnote n body => .footnote n body
  | .text s => .text s
  | .math display src => .math display src
  | .image src size alt => .image src size alt
  | .icon c label => .icon c label
  | .label key => .label key
  | .ref key form text target => .ref key form text target
  | .cite text keys => .cite text keys
  | .cited text keys ink => .cited text keys ink
  | .fill => .fill
  | .hspace g keep => .hspace g keep
  | .rule w h raise => .rule w h raise
  | .strut g => .strut g
  | .italicCorr maybe => .italicCorr maybe
  | .pageNumber => .pageNumber
  | .pageCount => .pageCount
  | .linebreak extra => .linebreak extra

public theorem resolveMathAlphaInline_fixed_point (coverage : Math.MathAlphabetCoverage)
    (x : Inline) :
    resolveMathAlphaInline coverage (resolveMathAlphaInline coverage x) =
      resolveMathAlphaInline coverage x := by
  cases x <;> simp only [resolveMathAlphaInline, Math.resolveMathAlphas_fixed_point]

/-- The picture face of alphabet resolution: a label's formulas resolve as a caption's do. -/
@[expose] public def resolveMathAlphaPicture (coverage : Math.MathAlphabetCoverage)
    (pic : Pic.Picture) : Pic.Picture :=
  pic.mapLabels (mapInlines (resolveMathAlphaInline coverage))

/-- A formula and the authored location enclosing it. -/
public structure MathRequest where
  body : Math.MList
  source : Option Span

/-- The regions a formula census reads: alphabet resolution's, which include
notes and style templates, or the painted scalar census's. -/
public inductive MathRequestScope where
  | alphabets
  | face
  deriving BEq, DecidableEq

private def mathRequestInlines : CtxFold (Option Span × Bool) (Array MathRequest) where
  openBlock := fun ctx out _ => (out, ctx)
  closeBlock := fun _ out _ => out
  openInline := fun ctx out x => match x with
    | .located span _ => (out, (ctx.1.orElse (fun _ => some span), ctx.2))
    | .formula _ _ body =>
      (if ctx.2 then out.push ⟨body, ctx.1⟩ else out, ctx)
    | .text _ | .math _ _ | .styled _ _ | .colored _ _ _ | .role _ _
    | .link _ _ | .decorated _ _ | .boxed _ _ | .onSteps _ _ | .altSteps _ _ _
    | .footnote _ _ | .image _ _ _ | .icon _ _ | .label _ | .ref _ _ _ _
    | .cite _ _ | .cited _ _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _
    | .pageNumber | .pageCount | .linebreak _ => (out, ctx)
  closeInline := fun _ out _ => out

/-- Entering a block for the request census: a note closes the face scope, and
block-owned regions are read here. -/
private def mathRequestOpen (scope : MathRequestScope) (ctx : Option Span × Bool)
    (out : Array MathRequest) (b : Block) : Array MathRequest × (Option Span × Bool) :=
  let read := foldCtxInlines mathRequestInlines ctx
  match b with
  | .note _ => (out, (ctx.1, ctx.2 && scope == .alphabets))
  | .verbatim _ _ spec =>
    (match spec.caption with
      | some (_, caption) => read out caption
      | none => out, ctx)
  | .picture pic => (pic.labelContents.foldl read out, ctx)
  | .para _ | .equation _ _ | .section _ _ _ _ | .list _ _ _ | .center _
  | .ragged _ _ | .quote _ _ | .lines _ | .abstract _ | .titled _ _ _ | .disclosure _ _ _ | .role _ _
  | .link _ _ | .spaced _ _ | .columns _ | .onSteps _ _ | .altSteps _ _ _
  | .only _ _ | .nav _ _ | .frame _ _ _ _ _ | .framefoot _
  | .float _ _ _ _ _ | .table _ _ _ _ _ _ | .algorithm _ _ _ | .logo _
  | .bibliography _ _ _ | .contents _ _
  | .setPalette _ | .setTokens _ | .pagebreak | .rule _ _ _ => (out, ctx)

private def mathRequestFold (scope : MathRequestScope) :
    CtxFold (Option Span × Bool) (Array MathRequest) :=
  { mathRequestInlines with openBlock := mathRequestOpen scope }

/-- Formula requests in the shared context fold's document order; a location
binds only its own descendants. -/
public def mathRequests (scope : MathRequestScope) (doc : Doc) : Array MathRequest :=
  let body := foldCtxBlocks (mathRequestFold scope) (none, true) #[] doc.body
  let furniture := match scope with
    | .alphabets => furnitureInlines doc
    | .face =>
      furnitureInlines.optRegion doc.head ++ furnitureInlines.optRegion doc.foot ++
        (match doc.headline with
          | some hl => #[hl.title, hl.author, hl.institute]
          | none => #[]) ++
        furnitureInlines.optRegion doc.logoLeft ++ furnitureInlines.optRegion doc.logoRight ++
        doc.itemLabels.map Prod.snd
  furniture.foldl (fun out xs => foldCtxInlines mathRequestInlines (none, true) out xs) body

/-- One request's missing alphabets onto a census that keeps first use
and drops repeats. -/
private def noteRequestAlphas (coverage : Math.MathAlphabetCoverage)
    (out : Array Math.MathAlphabet) (r : MathRequest) : Array Math.MathAlphabet :=
  (Math.missingMathAlphas coverage r.body).foldl (fun out a =>
    if out.contains a then out else out.push a) out

/-- Every alphabet whose used range the selected symbol face lacks over a
request census, deduplicated in first-use order. -/
public def missingAlphasOf (coverage : Math.MathAlphabetCoverage)
    (requests : Array MathRequest) : Array Math.MathAlphabet :=
  requests.foldl (noteRequestAlphas coverage) #[]

/-- Every alphabet whose used range the selected symbol face lacks,
deduplicated in first-use order over the alphabet census. -/
public def missingMathAlphas (coverage : Math.MathAlphabetCoverage)
    (doc : Doc) : Array Math.MathAlphabet :=
  missingAlphasOf coverage (mathRequests .alphabets doc)

/-- The first formula needing glyphs, before a face is selected. -/
public def mathFaceRequest (doc : Doc) : Option MathRequest :=
  (mathRequests .face doc).find? fun r => !(Math.MList.scalarsList true #[] r.body).isEmpty

public theorem mathFaceRequest_covers (doc : Doc) (request : MathRequest)
    (h : mathFaceRequest doc = some request) :
    request ∈ mathRequests .face doc ∧
      (Math.MList.scalarsList true #[] request.body).isEmpty = false := by
  refine ⟨Array.mem_of_find?_eq_some h, ?_⟩
  simpa using Array.find?_some h

/-- Resolve typed math-alphabet scopes in the shared IR, with one diagnostic
per missing alphabet. -/
@[expose] public def resolveMathAlphas (coverage : Math.MathAlphabetCoverage) (family : String)
    (doc : Doc) : Doc × Array Diag :=
  let leaf := resolveMathAlphaInline coverage
  let resolved := mapDoc (mapInlines leaf)
    (mapBlocksPic (resolveMathAlphaPicture coverage) leaf) doc
  let requests := mathRequests .alphabets doc
  let diags := (missingAlphasOf coverage requests).map fun a =>
    let source := (requests.find? fun r =>
      (Math.missingMathAlphas coverage r.body).contains a).bind (·.source)
    Diag.of .N0018 (Diag.say .N0018 .alphabet a.styleLabel (some (some .font, family)))
      source
      (help := some "write \\fonts{ math = \"...\" } with a face that carries this alphabet")
      (subject := some ("math-alpha:" ++ a.name))
      (trigger := source.bind (·.pos.command))
  (resolved, diags)

public theorem resolveMathAlphas_origin_covers (coverage : Math.MathAlphabetCoverage)
    (family : String) (doc : Doc) (d : Diag) (span : Span)
    (hd : d ∈ (resolveMathAlphas coverage family doc).2) (hs : d.span = some span) :
    ∃ a, a ∈ missingMathAlphas coverage doc ∧
      d.subject = some ("math-alpha:" ++ a.name) ∧
      ∃ request, request ∈ mathRequests .alphabets doc ∧
        request.source = some span ∧
          (Math.missingMathAlphas coverage request.body).contains a = true := by
  obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hd
  refine ⟨a, ha, ?_, ?_⟩
  · rw [Diag.of_record_exact]
  · rw [Diag.of_record_exact] at hs
    obtain ⟨request, hr, hsource⟩ := Option.bind_eq_some_iff.mp hs
    exact ⟨request, Array.mem_of_find?_eq_some hr, hsource,
      Array.find?_some (p := fun r : MathRequest =>
        (Math.missingMathAlphas coverage r.body).contains a) hr⟩

public theorem resolveMathAlphas_named (coverage : Math.MathAlphabetCoverage)
    (family : String) (doc : Doc) :
    (resolveMathAlphas coverage family doc).2.map (·.subject) =
      (missingMathAlphas coverage doc).map
        (fun a => some ("math-alpha:" ++ a.name)) := by
  simp [resolveMathAlphas, missingMathAlphas, Diag.of_subject, Array.map_map, Function.comp]

public theorem mapInlineList_finish_exact (f : Inline → Inline) (out : Array Inline)
    (xs : List Inline) (finish : Array Inline → Array Inline) :
    mapInlineList f out xs finish =
      finish (out.toList ++ xs.map (mapInline f · finish)).toArray := by
  induction xs generalizing out with
  | nil => simp [mapInlineList]
  | cons x xs ih =>
    rw [mapInlineList, ih]
    simp [Array.toList_push, List.append_assoc]

public theorem mapInlineList_toList (f : Inline → Inline) (out : Array Inline) (xs : List Inline) :
    (mapInlineList f out xs).toList = out.toList ++ xs.map (mapInline f) := by
  simp only [mapInlineList_finish_exact, id_eq, List.toList_toArray]

mutual

private theorem mapMathInline_fixed_point (coverage : Math.MathAlphabetCoverage) (x : Inline) :
    mapInline (resolveMathAlphaInline coverage) (mapInline (resolveMathAlphaInline coverage) x)
      = mapInline (resolveMathAlphaInline coverage) x := by
  match x with
  | .styled st body
  | .colored c n body
  | .located n body | .role n body
  | .link u body
  | .decorated kind body
  | .boxed _ body
  | .onSteps spec body
  | .footnote n body
  | .cited f ks body =>
    simp only [mapInline]; congr 1; apply Array.toList_inj.mp
    simp [mapInlineList_toList, mapMathInlineElems_fixed_point coverage body.toList]
  | .altSteps spec firstPage otherPage =>
    simp only [mapInline]
    congr 1 <;>
      · apply Array.toList_inj.mp
        simp [mapInlineList_toList, mapMathInlineElems_fixed_point coverage firstPage.toList,
          mapMathInlineElems_fixed_point coverage otherPage.toList]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _
  | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
    simp only [mapInline, resolveMathAlphaInline, Math.resolveMathAlphas_fixed_point]

private theorem mapMathInlineElems_fixed_point (coverage : Math.MathAlphabetCoverage) :
    ∀ xs : List Inline,
      ((xs.map (mapInline (resolveMathAlphaInline coverage))).map
        (mapInline (resolveMathAlphaInline coverage)))
        = xs.map (mapInline (resolveMathAlphaInline coverage))
  | [] => rfl
  | y :: rest => by
    simp only [List.map_cons]
    rw [mapMathInline_fixed_point coverage y, mapMathInlineElems_fixed_point coverage rest]

end

public theorem mapMathInlines_fixed_point (coverage : Math.MathAlphabetCoverage)
    (xs : Array Inline) :
    mapInlines (resolveMathAlphaInline coverage)
        (mapInlines (resolveMathAlphaInline coverage) xs)
      = mapInlines (resolveMathAlphaInline coverage) xs := by
  apply Array.toList_inj.mp
  simp [mapInlines, mapInlineList_toList, mapMathInlineElems_fixed_point coverage xs.toList]

private theorem map_map_fixed_point {α : Type _} (f : α → α) (h : ∀ a, f (f a) = f a)
    (l : List α) : (l.map f).map f = l.map f := by
  rw [List.map_map]
  exact List.map_congr_left (fun a _ => h a)

public theorem mapBlockList_toList (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline) :
    ∀ (out : Array Block) (bs : List Block),
      (mapBlockList gp f out bs).toList = out.toList ++ bs.map (mapBlock gp f)
  | _, [] => by simp [mapBlockList]
  | out, b :: rest => by
    rw [mapBlockList, mapBlockList_toList gp f (out.push (mapBlock gp f b)) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapBlockItems_toList (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline) :
    ∀ (out : Array (Array Block)) (items : List (Array Block)),
      (mapBlockItems gp f out items).toList
        = out.toList ++ items.map (fun it => mapBlockList gp f #[] it.toList)
  | _, [] => by simp [mapBlockItems]
  | out, it :: rest => by
    rw [mapBlockItems,
      mapBlockItems_toList gp f (out.push (mapBlockList gp f #[] it.toList)) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapBlockCols_toList (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline) :
    ∀ (out : Array (BoxWidth × Array Block)) (cols : List (BoxWidth × Array Block)),
      (mapBlockCols gp f out cols).toList
        = out.toList ++ cols.map (fun c => (c.1, mapBlockList gp f #[] c.2.toList))
  | _, [] => by simp [mapBlockCols]
  | out, (w, body) :: rest => by
    rw [mapBlockCols,
      mapBlockCols_toList gp f (out.push (w, mapBlockList gp f #[] body.toList)) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapTableRows_toList (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline) :
    ∀ (out : Array (Array (Array Block))) (rows : List (Array (Array Block))),
      (mapTableRows gp f out rows).toList
        = out.toList ++ rows.map (fun row => mapBlockItems gp f #[] row.toList)
  | _, [] => by simp [mapTableRows]
  | out, row :: rest => by
    rw [mapTableRows, mapTableRows_toList gp f (out.push (mapBlockItems gp f #[] row.toList)) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapAlgLines_toList (f : Inline → Inline) :
    ∀ (out : Array AlgLine) (ls : List AlgLine),
      (mapAlgLines f out ls).toList
        = out.toList ++ ls.map (fun l => ({ depth := l.depth, kind := l.kind, content := mapInlines f l.content, comment := l.comment.map (mapInlines f) } : AlgLine))
  | _, [] => by simp [mapAlgLines]
  | out, l :: rest => by
    rw [mapAlgLines, mapAlgLines_toList f (out.push { depth := l.depth, kind := l.kind, content := mapInlines f l.content, comment := l.comment.map (mapInlines f) }) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapLaidLines_toList (f : Inline → Inline) :
    ∀ (out : Array LaidLine) (ls : List LaidLine),
      (mapLaidLines f out ls).toList
        = out.toList ++ ls.map (fun l => ({ depth := l.depth, content := mapInlines f l.content } : LaidLine))
  | _, [] => by simp [mapLaidLines]
  | out, l :: rest => by
    rw [mapLaidLines, mapLaidLines_toList f (out.push { depth := l.depth, content := mapInlines f l.content }) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapBibItems_toList (f : Inline → Inline) :
    ∀ (out : Array BibItem) (items : List BibItem),
      (mapBibItems f out items).toList
        = out.toList ++ items.map (fun i => { i with content := mapInlines f i.content })
  | _, [] => by simp [mapBibItems]
  | out, i :: rest => by
    rw [mapBibItems, mapBibItems_toList f (out.push { i with content := mapInlines f i.content }) rest]
    simp [Array.toList_push, List.append_assoc]

public theorem mapContentsEntries_toList (f : Inline → Inline) :
    ∀ (out : Array ContentsEntry) (entries : List ContentsEntry),
      (mapContentsEntries f out entries).toList
        = out.toList ++ entries.map (fun e => { e with title := mapInlines f e.title })
  | _, [] => by simp [mapContentsEntries]
  | out, e :: rest => by
    rw [mapContentsEntries,
      mapContentsEntries_toList f (out.push { e with title := mapInlines f e.title }) rest]
    simp [Array.toList_push, List.append_assoc]

private theorem resolveMathAlphaPicture_fixed_point (coverage : Math.MathAlphabetCoverage)
    (pic : Pic.Picture) :
    resolveMathAlphaPicture coverage (resolveMathAlphaPicture coverage pic)
      = resolveMathAlphaPicture coverage pic := by
  simp only [resolveMathAlphaPicture, Pic.Picture.mapLabels_comp]
  congr 1
  exact funext (mapMathInlines_fixed_point coverage)

private theorem mapMathAlgLines_fixed_point (coverage : Math.MathAlphabetCoverage) (ls : List AlgLine) :
    mapAlgLines (resolveMathAlphaInline coverage) #[]
        (mapAlgLines (resolveMathAlphaInline coverage) #[] ls).toList
      = mapAlgLines (resolveMathAlphaInline coverage) #[] ls := by
  apply Array.toList_inj.mp
  simp only [mapAlgLines_toList, List.nil_append]
  apply map_map_fixed_point
  intro l
  have hcomment : (l.comment.map (mapInlines (resolveMathAlphaInline coverage))).map
      (mapInlines (resolveMathAlphaInline coverage))
      = l.comment.map (mapInlines (resolveMathAlphaInline coverage)) := by
    cases l.comment with
    | none => rfl
    | some c => simp [mapMathInlines_fixed_point coverage]
  simp only [mapMathInlines_fixed_point coverage, hcomment]

private theorem mapMathLaidLines_fixed_point (coverage : Math.MathAlphabetCoverage) (ls : List LaidLine) :
    mapLaidLines (resolveMathAlphaInline coverage) #[]
        (mapLaidLines (resolveMathAlphaInline coverage) #[] ls).toList
      = mapLaidLines (resolveMathAlphaInline coverage) #[] ls := by
  apply Array.toList_inj.mp
  simp only [mapLaidLines_toList, List.nil_append]
  apply map_map_fixed_point
  intro l
  simp only [mapMathInlines_fixed_point coverage]

private theorem mapMathBibItems_fixed_point (coverage : Math.MathAlphabetCoverage) (items : List BibItem) :
    mapBibItems (resolveMathAlphaInline coverage) #[]
        (mapBibItems (resolveMathAlphaInline coverage) #[] items).toList
      = mapBibItems (resolveMathAlphaInline coverage) #[] items := by
  apply Array.toList_inj.mp
  simp only [mapBibItems_toList, List.nil_append]
  apply map_map_fixed_point
  intro i
  simp [mapMathInlines_fixed_point coverage]

private theorem mapMathContentsEntries_fixed_point (coverage : Math.MathAlphabetCoverage)
    (entries : List ContentsEntry) :
    mapContentsEntries (resolveMathAlphaInline coverage) #[]
        (mapContentsEntries (resolveMathAlphaInline coverage) #[] entries).toList
      = mapContentsEntries (resolveMathAlphaInline coverage) #[] entries := by
  apply Array.toList_inj.mp
  simp only [mapContentsEntries_toList, List.nil_append]
  apply map_map_fixed_point
  intro e
  simp [mapMathInlines_fixed_point coverage]

mutual

private theorem mapMathBlock_fixed_point (coverage : Math.MathAlphabetCoverage) (b : Block) :
    mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage)
        (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) b)
      = mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) b := by
  match b with
  | .para content => simp only [mapBlock, mapMathInlines_fixed_point coverage]
  | .equation n content => simp only [mapBlock, mapMathInlines_fixed_point coverage]
  | .section l st n title => simp only [mapBlock, mapMathInlines_fixed_point coverage]
  | .framefoot content => simp only [mapBlock, mapMathInlines_fixed_point coverage]
  | .logo content => simp only [mapBlock, mapMathInlines_fixed_point coverage]
  | .list o _ items =>
    simp only [mapBlock]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockItems_toList, List.nil_append]
    exact mapMathBlockItemsElems_fixed_point coverage items.toList
  | .columns cols =>
    simp only [mapBlock]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockCols_toList, List.nil_append]
    exact mapMathBlockColsElems_fixed_point coverage cols.toList
  | .center body
  | .ragged s body
  | .quote _ body
  | .abstract body
  | .role n body
  | .link target body
  | .spaced g body
  | .onSteps spec body
  | .only targets body
  | .nav spec body
  | .note body =>
    simp only [mapBlock]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockList_toList, List.nil_append]
    exact mapMathBlockElems_fixed_point coverage body.toList
  | .titled kind title body =>
    simp only [mapBlock, mapMathInlines_fixed_point coverage]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockList_toList, List.nil_append]
    exact mapMathBlockElems_fixed_point coverage body.toList
  | .disclosure summary expanded body =>
    simp only [mapBlock, mapMathInlines_fixed_point coverage]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockList_toList, List.nil_append]
    exact mapMathBlockElems_fixed_point coverage body.toList
  | .frame title st v br body =>
    simp only [mapBlock, mapMathInlines_fixed_point coverage]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockList_toList, List.nil_append]
    exact mapMathBlockElems_fixed_point coverage body.toList
  | .float k num ca body caption =>
    simp only [mapBlock, mapMathInlines_fixed_point coverage]; congr 1; apply Array.toList_inj.mp
    simp only [mapBlockList_toList, List.nil_append]
    exact mapMathBlockElems_fixed_point coverage body.toList
  | .altSteps spec firstPage otherPage =>
    simp only [mapBlock]
    congr 1 <;>
      · apply Array.toList_inj.mp
        simp only [mapBlockList_toList, List.nil_append]
        first
          | exact mapMathBlockElems_fixed_point coverage firstPage.toList
          | exact mapMathBlockElems_fixed_point coverage otherPage.toList
  | .table c pl pr rows rules spans =>
    simp only [mapBlock]; congr 1; apply Array.toList_inj.mp
    simp only [mapTableRows_toList, List.nil_append]
    exact mapMathTableRowsElems_fixed_point coverage rows.toList
  | .algorithm n sm lines =>
    simp only [mapBlock]
    rw [mapMathAlgLines_fixed_point coverage lines.toList]
  | .lines ls =>
    simp only [mapBlock]
    rw [mapMathLaidLines_fixed_point coverage ls.toList]
  | .bibliography src style items =>
    simp only [mapBlock]
    rw [mapMathBibItems_fixed_point coverage items.toList]
  | .contents spec entries =>
    simp only [mapBlock]
    rw [mapMathContentsEntries_fixed_point coverage entries.toList]
  | .verbatim c s spec =>
    cases hc : spec.caption with
    | none => simp [mapBlock, hc]
    | some pr => simp [mapBlock, hc, mapMathInlines_fixed_point coverage]
  | .picture pic => simp only [mapBlock, resolveMathAlphaPicture_fixed_point coverage pic]
  | .setPalette _ | .setTokens _ | .pagebreak | .rule _ _ _ =>
    simp only [mapBlock]

private theorem mapMathBlockElems_fixed_point (coverage : Math.MathAlphabetCoverage) :
    ∀ bs : List Block,
      ((bs.map (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))).map
        (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage)))
        = bs.map (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))
  | [] => rfl
  | b :: rest => by
    simp only [List.map_cons]
    rw [mapMathBlock_fixed_point coverage b, mapMathBlockElems_fixed_point coverage rest]

private theorem mapMathBlockItemsElems_fixed_point (coverage : Math.MathAlphabetCoverage) :
    ∀ its : List (Array Block),
      ((its.map (fun it => mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] it.toList)).map
        (fun it => mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] it.toList))
        = its.map (fun it => mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] it.toList)
  | [] => rfl
  | it :: rest => by
    have h : mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[]
        (mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] it.toList).toList
        = mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] it.toList := by
      apply Array.toList_inj.mp
      simp only [mapBlockList_toList, List.nil_append]
      exact mapMathBlockElems_fixed_point coverage it.toList
    simp only [List.map_cons]
    rw [h, mapMathBlockItemsElems_fixed_point coverage rest]

private theorem mapMathBlockColsElems_fixed_point (coverage : Math.MathAlphabetCoverage) :
    ∀ cols : List (BoxWidth × Array Block),
      ((cols.map (fun c => (c.1, mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] c.2.toList))).map
        (fun c => (c.1, mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] c.2.toList)))
        = cols.map (fun c => (c.1, mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] c.2.toList))
  | [] => rfl
  | c :: rest => by
    have h : mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[]
        (mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] c.2.toList).toList
        = mapBlockList (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] c.2.toList := by
      apply Array.toList_inj.mp
      simp only [mapBlockList_toList, List.nil_append]
      exact mapMathBlockElems_fixed_point coverage c.2.toList
    simp only [List.map_cons]
    rw [h, mapMathBlockColsElems_fixed_point coverage rest]

private theorem mapMathTableRowsElems_fixed_point (coverage : Math.MathAlphabetCoverage) :
    ∀ rows : List (Array (Array Block)),
      ((rows.map (fun row => mapBlockItems (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] row.toList)).map
        (fun row => mapBlockItems (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] row.toList))
        = rows.map (fun row => mapBlockItems (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] row.toList)
  | [] => rfl
  | row :: rest => by
    have h : mapBlockItems (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[]
        (mapBlockItems (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] row.toList).toList
        = mapBlockItems (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) #[] row.toList := by
      apply Array.toList_inj.mp
      simp only [mapBlockItems_toList, List.nil_append]
      exact mapMathBlockItemsElems_fixed_point coverage row.toList
    simp only [List.map_cons]
    rw [h, mapMathTableRowsElems_fixed_point coverage rest]

end

private theorem mapMathBlocks_fixed_point (coverage : Math.MathAlphabetCoverage) (xs : Array Block) :
    mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) xs)
      = mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) xs := by
  apply Array.toList_inj.mp
  simp only [mapBlocksPic, mapBlockList_toList, List.nil_append]
  exact mapMathBlockElems_fixed_point coverage xs.toList

private theorem mapDoc_comp (fi fi' : Array Inline → Array Inline)
    (fb fb' : Array Block → Array Block) (doc : Doc) :
    mapDoc fi fb (mapDoc fi' fb' doc) = mapDoc (fi ∘ fi') (fb ∘ fb') doc := by
  simp [mapDoc, Option.map_map, Function.comp]
  congr 1

private theorem mapMathDoc_fixed_point (coverage : Math.MathAlphabetCoverage) (doc : Doc) :
    mapDoc (mapInlines (resolveMathAlphaInline coverage))
        (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))
        (mapDoc (mapInlines (resolveMathAlphaInline coverage))
          (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage)) doc)
      = mapDoc (mapInlines (resolveMathAlphaInline coverage))
          (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage)) doc := by
  have hfi : (mapInlines (resolveMathAlphaInline coverage))
      ∘ (mapInlines (resolveMathAlphaInline coverage))
      = mapInlines (resolveMathAlphaInline coverage) := funext (mapMathInlines_fixed_point coverage)
  have hfb : (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))
      ∘ (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))
      = mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) := funext (mapMathBlocks_fixed_point coverage)
  rw [mapDoc_comp, hfi, hfb]

public theorem resolveMathAlphas_fixed_point (coverage : Math.MathAlphabetCoverage)
    (family : String) (doc : Doc) :
    (resolveMathAlphas coverage family (resolveMathAlphas coverage family doc).1).1
      = (resolveMathAlphas coverage family doc).1 := by
  simp only [resolveMathAlphas]
  exact mapMathDoc_fixed_point coverage doc

/-- Every request a census holds asks for an alphabet-free formula. -/
private def RequestsFree (out : Array MathRequest) : Prop :=
  ∀ r ∈ out, r.body.alphaFree = true

private theorem requestsFree_push {out : Array MathRequest} {r : MathRequest}
    (h : RequestsFree out) (hr : r.body.alphaFree = true) : RequestsFree (out.push r) := by
  intro q hq
  rcases Array.mem_push.mp hq with hq | hq
  · exact h q hq
  · exact hq ▸ hr

private theorem mathRequestFold_openBlock (scope : MathRequestScope)
    (ctx : Option Span × Bool) (out : Array MathRequest) (b : Block) :
    (mathRequestFold scope).openBlock ctx out b = mathRequestOpen scope ctx out b := rfl

private theorem mathRequestFold_closeBlock (scope : MathRequestScope)
    (ctx : Option Span × Bool) (out : Array MathRequest) (b : Block) :
    (mathRequestFold scope).closeBlock ctx out b = out := rfl

mutual

private theorem requestsInline_resolve_covers (coverage : Math.MathAlphabetCoverage)
    (w : CtxFold (Option Span × Bool) (Array MathRequest))
    (ho : ∀ ctx out x, w.openInline ctx out x = mathRequestInlines.openInline ctx out x)
    (hc : ∀ ctx out x, w.closeInline ctx out x = out)
    (ctx : Option Span × Bool) (out : Array MathRequest) (x : Inline) (h : RequestsFree out) :
    RequestsFree (foldCtxInline w ctx out (mapInline (resolveMathAlphaInline coverage) x)) := by
  match x with
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
  | .decorated _ body | .boxed _ body | .onSteps _ body | .footnote _ body | .cited _ _ body =>
    simp only [mapInline, foldCtxInline, ho, hc, mathRequestInlines, mapInlineList_toList,
      List.nil_append]
    exact requestsInlineList_resolve_covers coverage w ho hc _ out body.toList h
  | .altSteps _ firstPage otherPage =>
    simp only [mapInline, foldCtxInline, ho, hc, mathRequestInlines, mapInlineList_toList,
      List.nil_append]
    exact requestsInlineList_resolve_covers coverage w ho hc _ _ otherPage.toList
      (requestsInlineList_resolve_covers coverage w ho hc _ out firstPage.toList h)
  | .formula _ _ body =>
    simp only [mapInline, resolveMathAlphaInline, foldCtxInline, ho, hc, mathRequestInlines]
    split
    · exact requestsFree_push h (Math.resolveMathAlphas_covers coverage body)
    · exact h
  | .text _ | .math _ _ | .image _ _ _ | .icon _ _ | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount
  | .linebreak _ =>
    simpa only [mapInline, resolveMathAlphaInline, foldCtxInline, ho, hc, mathRequestInlines]
      using h

private theorem requestsInlineList_resolve_covers (coverage : Math.MathAlphabetCoverage)
    (w : CtxFold (Option Span × Bool) (Array MathRequest))
    (ho : ∀ ctx out x, w.openInline ctx out x = mathRequestInlines.openInline ctx out x)
    (hc : ∀ ctx out x, w.closeInline ctx out x = out)
    (ctx : Option Span × Bool) (out : Array MathRequest) :
    ∀ xs : List Inline, RequestsFree out →
      RequestsFree (foldCtxInlineList w ctx out
        (xs.map (mapInline (resolveMathAlphaInline coverage))))
  | [], h => h
  | x :: rest, h => by
    rw [List.map_cons, foldCtxInlineList]
    exact requestsInlineList_resolve_covers coverage w ho hc ctx _ rest
      (requestsInline_resolve_covers coverage w ho hc ctx out x h)

end

private theorem requestsFoldInlines_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool)
    (out : Array MathRequest) (xs : Array Inline) (h : RequestsFree out) :
    RequestsFree (foldCtxInlineList (mathRequestFold scope) ctx out
      (mapInlines (resolveMathAlphaInline coverage) xs).toList) := by
  simp only [mapInlines, mapInlineList_toList, List.nil_append]
  exact requestsInlineList_resolve_covers coverage (mathRequestFold scope) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) ctx out xs.toList h

private theorem requestsRegions_resolve_covers (coverage : Math.MathAlphabetCoverage)
    (ctx : Option Span × Bool) :
    ∀ (regions : List (Array Inline)) (out : Array MathRequest), RequestsFree out →
      RequestsFree ((regions.map (mapInlines (resolveMathAlphaInline coverage))).foldl
        (fun acc xs => foldCtxInlines mathRequestInlines ctx acc xs) out)
  | [], _, h => h
  | xs :: rest, out, h => by
    rw [List.map_cons, List.foldl_cons]
    apply requestsRegions_resolve_covers coverage ctx rest
    simp only [foldCtxInlines, mapInlines, mapInlineList_toList, List.nil_append]
    exact requestsInlineList_resolve_covers coverage _ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      ctx out xs.toList h

private theorem requestsAlgLines_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool) :
    ∀ (lines : List AlgLine) (out : Array MathRequest), RequestsFree out →
      RequestsFree (foldCtxAlgLines (mathRequestFold scope) ctx out
        (mapAlgLines (resolveMathAlphaInline coverage) #[] lines).toList)
  | [], _, h => h
  | line :: rest, out, h => by
    have step := requestsAlgLines_resolve_covers scope coverage ctx rest
    simp only [mapAlgLines_toList, List.nil_append] at step ⊢
    rw [List.map_cons, foldCtxAlgLines]
    apply step
    cases hc : line.comment with
    | none =>
      simpa only [Option.map_none] using
        requestsFoldInlines_resolve_covers scope coverage ctx out line.content h
    | some c =>
      simp only [Option.map_some]
      exact requestsFoldInlines_resolve_covers scope coverage ctx _ c
        (requestsFoldInlines_resolve_covers scope coverage ctx out line.content h)

private theorem requestsLaid_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool) :
    ∀ (lines : List LaidLine) (out : Array MathRequest), RequestsFree out →
      RequestsFree (foldCtxLaidLines (mathRequestFold scope) ctx out
        (mapLaidLines (resolveMathAlphaInline coverage) #[] lines).toList)
  | [], _, h => h
  | line :: rest, out, h => by
    have step := requestsLaid_resolve_covers scope coverage ctx rest
    simp only [mapLaidLines_toList, List.nil_append] at step ⊢
    rw [List.map_cons, foldCtxLaidLines]
    exact step _ (requestsFoldInlines_resolve_covers scope coverage ctx out line.content h)

private theorem requestsBibItems_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool) :
    ∀ (items : List BibItem) (out : Array MathRequest), RequestsFree out →
      RequestsFree (foldCtxBibItems (mathRequestFold scope) ctx out
        (items.map fun i => { i with content := mapInlines (resolveMathAlphaInline coverage) i.content }))
  | [], _, h => h
  | it :: rest, out, h => by
    rw [List.map_cons, foldCtxBibItems]
    exact requestsBibItems_resolve_covers scope coverage ctx rest _
      (requestsFoldInlines_resolve_covers scope coverage ctx out it.content h)

private theorem requestsContentsEntries_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool) :
    ∀ (entries : List ContentsEntry) (out : Array MathRequest), RequestsFree out →
      RequestsFree (foldCtxContentsEntries (mathRequestFold scope) ctx out
        (entries.map fun e => { e with title := mapInlines (resolveMathAlphaInline coverage) e.title }))
  | [], _, h => h
  | e :: rest, out, h => by
    rw [List.map_cons, foldCtxContentsEntries]
    exact requestsContentsEntries_resolve_covers scope coverage ctx rest _
      (requestsFoldInlines_resolve_covers scope coverage ctx out e.title h)

mutual

private theorem requestsBlock_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool)
    (out : Array MathRequest) (b : Block) (h : RequestsFree out) :
    RequestsFree (foldCtxBlock (mathRequestFold scope) ctx out
      (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage) b)) := by
  match b with
  | .para content | .section _ _ _ content | .framefoot content | .logo content =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock]
    exact requestsFoldInlines_resolve_covers scope coverage ctx out content h
  | .equation number content =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock]
    exact requestsFoldInlines_resolve_covers scope coverage ctx _ number
      (requestsFoldInlines_resolve_covers scope coverage ctx out content h)
  | .list _ _ items =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockItems_toList, List.nil_append]
    exact requestsItems_resolve_covers scope coverage ctx out items.toList h
  | .columns cols =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockCols_toList, List.nil_append]
    exact requestsCols_resolve_covers scope coverage ctx out cols.toList h
  | .center body | .ragged _ body | .quote _ body | .abstract body | .role _ body
  | .link _ body | .spaced _ body | .onSteps _ body | .only _ body | .nav _ body =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockList_toList, List.nil_append]
    exact requestsBlockList_resolve_covers scope coverage ctx out body.toList h
  | .note body =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockList_toList, List.nil_append]
    exact requestsBlockList_resolve_covers scope coverage _ out body.toList h
  | .titled _ title body | .disclosure title _ body | .frame title _ _ _ body | .float _ _ _ body title =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockList_toList, List.nil_append]
    exact requestsBlockList_resolve_covers scope coverage ctx _ body.toList
      (requestsFoldInlines_resolve_covers scope coverage ctx out title h)
  | .altSteps _ firstPage otherPage =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBlockList_toList, List.nil_append]
    exact requestsBlockList_resolve_covers scope coverage ctx _ otherPage.toList
      (requestsBlockList_resolve_covers scope coverage ctx out firstPage.toList h)
  | .table _ _ _ rows _ _ =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapTableRows_toList, List.nil_append]
    exact requestsRows_resolve_covers scope coverage ctx out rows.toList h
  | .algorithm _ _ lines =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock]
    exact requestsAlgLines_resolve_covers scope coverage ctx lines.toList out h
  | .lines ls =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock]
    exact requestsLaid_resolve_covers scope coverage ctx ls.toList out h
  | .verbatim _ _ spec =>
    cases hc : spec.caption with
    | none =>
      simpa only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
        mathRequestFold_closeBlock, hc, Option.map_none, id_eq] using h
    | some caption =>
      simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
        mathRequestFold_closeBlock, hc, Option.map_some, id_eq]
      exact requestsRegions_resolve_covers coverage ctx [caption.2] out h
  | .bibliography _ _ items =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapBibItems_toList, List.nil_append]
    exact requestsBibItems_resolve_covers scope coverage ctx items.toList out h
  | .contents _ entries =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, mapContentsEntries_toList, List.nil_append]
    exact requestsContentsEntries_resolve_covers scope coverage ctx entries.toList out h
  | .picture pic =>
    simp only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock, resolveMathAlphaPicture, Pic.Picture.labelContents_mapLabels]
    rw [← Array.foldl_toList, Array.toList_map]
    exact requestsRegions_resolve_covers coverage ctx pic.labelContents.toList out h
  | .setPalette _ | .setTokens _ | .pagebreak | .rule _ _ _ =>
    simpa only [mapBlock, foldCtxBlock, mathRequestFold_openBlock, mathRequestOpen,
      mathRequestFold_closeBlock] using h

private theorem requestsBlockList_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool)
    (out : Array MathRequest) :
    ∀ bs : List Block, RequestsFree out →
      RequestsFree (foldCtxBlockList (mathRequestFold scope) ctx out
        (bs.map (mapBlock (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage))))
  | [], h => h
  | b :: rest, h => by
    rw [List.map_cons, foldCtxBlockList]
    exact requestsBlockList_resolve_covers scope coverage ctx _ rest
      (requestsBlock_resolve_covers scope coverage ctx out b h)

private theorem requestsItems_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool)
    (out : Array MathRequest) :
    ∀ items : List (Array Block), RequestsFree out →
      RequestsFree (foldCtxBlockItems (mathRequestFold scope) ctx out
        (items.map fun item => mapBlockList (resolveMathAlphaPicture coverage)
          (resolveMathAlphaInline coverage) #[] item.toList))
  | [], h => h
  | item :: rest, h => by
    rw [List.map_cons, foldCtxBlockItems, mapBlockList_toList, List.nil_append]
    exact requestsItems_resolve_covers scope coverage ctx _ rest
      (requestsBlockList_resolve_covers scope coverage ctx out item.toList h)

private theorem requestsCols_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool)
    (out : Array MathRequest) :
    ∀ cols : List (BoxWidth × Array Block), RequestsFree out →
      RequestsFree (foldCtxBlockCols (mathRequestFold scope) ctx out
        (cols.map fun c => (c.1, mapBlockList (resolveMathAlphaPicture coverage)
          (resolveMathAlphaInline coverage) #[] c.2.toList)))
  | [], h => h
  | (_, body) :: rest, h => by
    rw [List.map_cons, foldCtxBlockCols, mapBlockList_toList, List.nil_append]
    exact requestsCols_resolve_covers scope coverage ctx _ rest
      (requestsBlockList_resolve_covers scope coverage ctx out body.toList h)

private theorem requestsRows_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (ctx : Option Span × Bool)
    (out : Array MathRequest) :
    ∀ rows : List (Array (Array Block)), RequestsFree out →
      RequestsFree (foldCtxTableRows (mathRequestFold scope) ctx out
        (rows.map fun row => mapBlockItems (resolveMathAlphaPicture coverage)
          (resolveMathAlphaInline coverage) #[] row.toList))
  | [], h => h
  | row :: rest, h => by
    rw [List.map_cons, foldCtxTableRows, mapBlockItems_toList, List.nil_append]
    exact requestsRows_resolve_covers scope coverage ctx _ rest
      (requestsItems_resolve_covers scope coverage ctx out row.toList h)

end

public theorem mathRequests_resolve_covers (scope : MathRequestScope)
    (coverage : Math.MathAlphabetCoverage) (family : String) (doc : Doc) :
    ∀ r ∈ mathRequests scope (resolveMathAlphas coverage family doc).1,
      r.body.alphaFree = true := by
  have body : RequestsFree (foldCtxBlocks (mathRequestFold scope) (none, true) #[]
      (mapBlocksPic (resolveMathAlphaPicture coverage) (resolveMathAlphaInline coverage)
        doc.body)) := by
    simp only [foldCtxBlocks, mapBlocksPic, mapBlockList_toList, List.nil_append]
    exact requestsBlockList_resolve_covers scope coverage (none, true) #[] doc.body.toList
      (fun _ h => by simp at h)
  have furniture : ∀ (regions : Array (Array Inline)) (out : Array MathRequest),
      RequestsFree out →
        RequestsFree ((regions.map (mapInlines (resolveMathAlphaInline coverage))).foldl
          (fun acc xs => foldCtxInlines mathRequestInlines (none, true) acc xs) out) := by
    intro regions out h
    rw [← Array.foldl_toList, Array.toList_map]
    exact requestsRegions_resolve_covers coverage (none, true) regions.toList out h
  cases scope with
  | alphabets =>
    simp only [mathRequests, resolveMathAlphas, furnitureInlines_mapDoc]
    exact furniture _ _ body
  | face =>
    simp only [mathRequests, resolveMathAlphas]
    cases hh : doc.headline with
    | none =>
      have := furniture (furnitureInlines.optRegion doc.head ++
        furnitureInlines.optRegion doc.foot ++ #[] ++
        furnitureInlines.optRegion doc.logoLeft ++ furnitureInlines.optRegion doc.logoRight ++
        doc.itemLabels.map Prod.snd)
        _ body
      simp only [RequestsFree] at this
      simpa [mapDoc, hh, optRegion_map, Array.map_append, Array.map_map, Function.comp_def]
        using this
    | some hl =>
      have := furniture (furnitureInlines.optRegion doc.head ++
        furnitureInlines.optRegion doc.foot ++ #[hl.title, hl.author, hl.institute] ++
        furnitureInlines.optRegion doc.logoLeft ++ furnitureInlines.optRegion doc.logoRight ++
        doc.itemLabels.map Prod.snd)
        _ body
      simp only [RequestsFree] at this
      simpa [mapDoc, hh, optRegion_map, Array.map_append, Array.map_map, Function.comp_def]
        using this

public theorem missingMathAlphas_resolve_exact (coverage : Math.MathAlphabetCoverage)
    (family : String) (doc : Doc) :
    missingMathAlphas coverage (resolveMathAlphas coverage family doc).1 = #[] := by
  have spent : ∀ rs : List MathRequest, (∀ r ∈ rs, r.body.alphaFree = true) →
      rs.foldl (noteRequestAlphas coverage) #[] = #[] := by
    intro rs hrs
    induction rs with
    | nil => rfl
    | cons r rest ih =>
      simp only [List.foldl_cons, noteRequestAlphas,
        Math.missingMathAlphas_alphaFree_exact coverage _ (hrs r (by simp)), Array.foldl_empty]
      exact ih fun q hq => hrs q (by simp [hq])
  rw [missingMathAlphas, missingAlphasOf, ← Array.foldl_toList]
  exact spent _ fun r hr =>
    mathRequests_resolve_covers .alphabets coverage family doc r (by simpa using hr)

public theorem resolveMathAlphas_diags_exact (coverage : Math.MathAlphabetCoverage)
    (family : String) (doc : Doc) :
    (resolveMathAlphas coverage family (resolveMathAlphas coverage family doc).1).2 = #[] := by
  change (missingMathAlphas coverage (resolveMathAlphas coverage family doc).1).map _ = #[]
  rw [missingMathAlphas_resolve_exact, Array.map_empty]

/-- The List companion of `linkBlocks`: one block link owns the whole body. -/
private def linkBlockList (url : String) (body : List Block) : List Block :=
  [Block.link url body.toArray]

/-- Wrap a block sequence in one link destination. -/
public def linkBlocks (url : String) (xs : Array Block) : Array Block :=
  (linkBlockList url xs.toList).toArray

/-- A block link's nested body given its kind's affordance: every text-bearing
run set in the kind's link ink and underlined. -/
public def Styles.linkBodyAfford (s : Styles) (kind : String) (xs : Array Block) : Array Block :=
  -- A picture's labels are the diagram's text: they keep their ink and are never underlined.
  mapBlocks (s.linkLeafAfford kind) xs

mutual

public theorem mapInlineFinish_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) (x : Inline) :
    plainTextOne (mapInline (finish := finish) f x) = plainTextOne x := by
  match x with
  | .styled st body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .colored c n body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .located n body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .role n body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .link u body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .decorated kind body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .boxed b body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .onSteps spec body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .altSteps spec firstPage otherPage =>
    show plainTextList (mapInlineList (finish := finish) f #[] firstPage.toList).toList
        ++ plainTextList (mapInlineList (finish := finish) f #[] otherPage.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish firstPage.toList #[],
      mapInlineListFinish_text f hf finish hfinish otherPage.toList #[]]
    simp [plainTextList, plainTextOne]
  | .footnote n body =>
    show plainTextList (mapInlineList (finish := finish) f #[] body.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish body.toList #[]]
    simp [plainTextList, plainTextOne]
  | .cited t ks ink =>
    show plainTextList (mapInlineList (finish := finish) f #[] ink.toList).toList = _
    rw [mapInlineListFinish_text f hf finish hfinish ink.toList #[]]
    simp [plainTextList, plainTextOne]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ => exact hf _

public theorem mapInlineListFinish_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) (xs : List Inline)
    (out : Array Inline) :
    plainTextList (mapInlineList (finish := finish) f out xs).toList
      = plainTextList out.toList ++ plainTextList xs := by
  match xs with
  | [] => simpa [mapInlineList, plainText, plainTextList] using hfinish out
  | x :: rest =>
    rw [mapInlineList, mapInlineListFinish_text f hf finish hfinish rest (out.push (mapInline (finish := finish) f x))]
    rw [Array.toList_push, plainTextList_append]
    simp [plainTextList, mapInlineFinish_text f hf finish hfinish x, String.append_assoc]

end

public theorem mapInlinesFinish_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) :
    Conserves plainText (mapInlines (finish := finish) f) := fun xs => by
  show plainTextList (mapInlineList (finish := finish) f #[] xs.toList).toList = _
  rw [mapInlineListFinish_text f hf finish hfinish xs.toList #[]]
  simp [plainTextList, plainText]

public theorem mapInline_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (x : Inline) :
    plainTextOne (mapInline f x) = plainTextOne x :=
  mapInlineFinish_text f hf id (fun _ => rfl) x

public theorem mapInlineList_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (xs : List Inline)
    (out : Array Inline) :
    plainTextList (mapInlineList f out xs).toList
      = plainTextList out.toList ++ plainTextList xs :=
  mapInlineListFinish_text f hf id (fun _ => rfl) xs out

public theorem mapInlines_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) :
    Conserves plainText (mapInlines f) :=
  mapInlinesFinish_text f hf id (fun _ => rfl)

private theorem mapAlgLines_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) (ls : List AlgLine)
    (out : Array AlgLine) (acc : String) :
    algLineText acc (mapAlgLines (finish := finish) f out ls).toList
      = algLineText (algLineText acc out.toList) ls := by
  match ls with
  | [] => simp [mapAlgLines, algLineText]
  | l :: rest =>
    rw [mapAlgLines, mapAlgLines_text f hf finish hfinish rest]
    rw [Array.toList_push, algLineText_chain]
    have hm : ∀ xs, plainText (mapInlines (finish := finish) f xs) = plainText xs := mapInlinesFinish_text f hf finish hfinish
    cases hc : l.comment <;> simp [algLineText, hc, hm]

private theorem mapLaidLines_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) (ls : List LaidLine)
    (out : Array LaidLine) (acc : String) :
    laidText acc (mapLaidLines (finish := finish) f out ls).toList
      = laidText (laidText acc out.toList) ls := by
  match ls with
  | [] => simp [mapLaidLines, laidText]
  | l :: rest =>
    rw [mapLaidLines, mapLaidLines_text f hf finish hfinish rest]
    rw [Array.toList_push, laidText_chain]
    have hm : ∀ xs, plainText (mapInlines (finish := finish) f xs) = plainText xs :=
      mapInlinesFinish_text f hf finish hfinish
    simp [laidText, hm]

mutual

public theorem foldInline_or (p : Inline → Bool) (b : Bool) (x : Inline) :
    foldInline (fun a y => a || p y) b x
      = (b || foldInline (fun a y => a || p y) false x) := by
  match x with
  | .styled st body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .colored c n body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .located n body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .role n body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .link u body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .decorated kind body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .boxed b body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .onSteps spec body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .altSteps spec firstPage otherPage =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or,
      foldInlineList_or p (foldInlineList (fun a y => a || p y)
        (false || p (Inline.altSteps spec firstPage otherPage)) firstPage.toList) otherPage.toList,
      foldInlineList_or p (false || p (Inline.altSteps spec firstPage otherPage)) firstPage.toList]
    simp [Bool.or_assoc]
  | .footnote n body =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .cited t ks ink =>
    rw [foldInline, foldInline, foldInlineList_or, foldInlineList_or p (false || p _)]
    simp [Bool.or_assoc]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ => simp [foldInline]

public theorem foldInlineList_or (p : Inline → Bool) (b : Bool) (xs : List Inline) :
    foldInlineList (fun a y => a || p y) b xs
      = (b || foldInlineList (fun a y => a || p y) false xs) := by
  match xs with
  | [] => simp [foldInlineList]
  | x :: rest =>
    rw [foldInlineList, foldInlineList,
      foldInlineList_or p (foldInline (fun a y => a || p y) b x),
      foldInlineList_or p (foldInline (fun a y => a || p y) false x),
      foldInline_or p b x]
    simp [Bool.or_assoc]

end

mutual

public theorem mapInline_id (f : Inline → Inline) (p : Inline → Bool)
    (hf : ∀ x, p x = false → f x = x) (x : Inline)
    (h : foldInline (fun a y => a || p y) false x = false) :
    mapInline f x = x := by
  match x with
  | .styled st body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .colored c n body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .located n body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .role n body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .link u body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .decorated kind body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .boxed b body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .onSteps spec body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .altSteps spec firstPage otherPage =>
    rw [foldInline, foldInlineList_or, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨h1, h3⟩
    rcases Bool.or_eq_false_iff.mp h1 with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf firstPage.toList #[] h2,
      mapInlineList_id f p hf otherPage.toList #[] h3]
    simp
  | .footnote n body =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf body.toList #[] h2]
    simp
  | .cited t ks ink =>
    rw [foldInline, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨-, h2⟩
    rw [mapInline, mapInlineList_id f p hf ink.toList #[] h2]
    simp
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ =>
    exact hf _ (by simpa [foldInline] using h)

public theorem mapInlineList_id (f : Inline → Inline) (p : Inline → Bool)
    (hf : ∀ x, p x = false → f x = x) (xs : List Inline) (out : Array Inline)
    (h : foldInlineList (fun a y => a || p y) false xs = false) :
    mapInlineList f out xs = out ++ xs.toArray := by
  match xs with
  | [] => simp [mapInlineList]
  | x :: rest =>
    rw [foldInlineList, foldInlineList_or] at h
    rcases Bool.or_eq_false_iff.mp h with ⟨h1, h2⟩
    rw [mapInlineList, mapInline_id f p hf x h1,
      mapInlineList_id f p hf rest (out.push x) h2]
    simp

end

public theorem mapInlines_id (f : Inline → Inline) (p : Inline → Bool)
    (hf : ∀ x, p x = false → f x = x) (xs : Array Inline)
    (h : anyInline p xs = false) : mapInlines f xs = xs := by
  rw [mapInlines, mapInlineList_id f p hf xs.toList #[] h]
  simp

private theorem mapBibItems_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish) (items : List BibItem)
    (out : Array BibItem) (acc : String) :
    blockTextBibItems acc (mapBibItems (finish := finish) f out items).toList
      = blockTextBibItems (blockTextBibItems acc out.toList) items := by
  match items with
  | [] => simp [mapBibItems, blockTextBibItems]
  | i :: rest =>
    rw [mapBibItems, mapBibItems_text f hf finish hfinish rest]
    rw [Array.toList_push, blockTextBibItems_chain]
    simp [blockTextBibItems, mapInlinesFinish_text f hf finish hfinish i.content]

private theorem mapContentsEntries_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (entries : List ContentsEntry) (out : Array ContentsEntry) (acc : String) :
    blockTextContentsEntries acc (mapContentsEntries (finish := finish) f out entries).toList
      = blockTextContentsEntries (blockTextContentsEntries acc out.toList) entries := by
  match entries with
  | [] => simp [mapContentsEntries, blockTextContentsEntries]
  | e :: rest =>
    rw [mapContentsEntries, mapContentsEntries_text f hf finish hfinish rest]
    rw [Array.toList_push, blockTextContentsEntries_chain]
    simp [blockTextContentsEntries, mapInlinesFinish_text f hf finish hfinish e.title]

mutual

public theorem mapBlockWith_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText) (acc : String) (b : Block) :
    blockTextOne acc (mapBlock (finish := finish) (listing := listing) gp f b) = blockTextOne acc b := by
  match b with
  | .para content => simp [mapBlock, blockTextOne, mapInlinesFinish_text f hf finish hfinish content]
  | .equation n content =>
    simp [mapBlock, blockTextOne, mapInlinesFinish_text f hf finish hfinish content, mapInlinesFinish_text f hf finish hfinish n]
  | .section l st n title =>
    simp [mapBlock, blockTextOne, mapInlinesFinish_text f hf finish hfinish title]
  | .list o _ items =>
    show blockTextItems acc (mapBlockItems (finish := finish) (listing := listing) gp f #[] items.toList).toList = _
    rw [mapBlockItemsWith_text gp f hf finish hfinish listing hlisting items.toList #[]]
    rfl
  | .center body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .ragged _ body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .quote _ body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .lines ls =>
    show laidText acc (mapLaidLines (finish := finish) f #[] ls.toList).toList = _
    rw [mapLaidLines_text f hf finish hfinish ls.toList #[]]
    rfl
  | .abstract body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .titled kind title body =>
    show blockTextList (acc ++ plainText (mapInlines (finish := finish) f title))
      (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapInlinesFinish_text f hf finish hfinish title, mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .disclosure summary expanded body =>
    show blockTextList (acc ++ plainText (mapInlines (finish := finish) f summary))
      (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapInlinesFinish_text f hf finish hfinish summary, mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .role n body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .link target body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .spaced g body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .columns cols =>
    show blockTextColumns acc (mapBlockCols (finish := finish) (listing := listing) gp f #[] cols.toList).toList = _
    rw [mapBlockColsWith_text gp f hf finish hfinish listing hlisting cols.toList #[]]
    rfl
  | .onSteps spec body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .altSteps spec firstPage otherPage =>
    show blockTextList (blockTextList acc
        (mapBlockList (finish := finish) (listing := listing) gp f #[] firstPage.toList).toList)
        (mapBlockList (finish := finish) (listing := listing) gp f #[] otherPage.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting firstPage.toList #[],
      mapBlockListWith_text gp f hf finish hfinish listing hlisting otherPage.toList #[]]
    rfl
  | .only targets body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .nav spec body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .note body =>
    show blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .frame title st v _ body =>
    show blockTextList (acc ++ plainText (mapInlines (finish := finish) f title))
      (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapInlinesFinish_text f hf finish hfinish title, mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .framefoot content =>
    simp [mapBlock, blockTextOne, mapInlinesFinish_text f hf finish hfinish content]
  | .float k num ca body caption =>
    show blockTextList (acc ++ plainText (mapInlines (finish := finish) f caption))
      (mapBlockList (finish := finish) (listing := listing) gp f #[] body.toList).toList = _
    rw [mapInlinesFinish_text f hf finish hfinish caption, mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
    rfl
  | .table c pl pr rows rules spans =>
    show blockTextTableRows acc
      (mapTableRows (finish := finish) (listing := listing) gp f #[] rows.toList).toList = _
    rw [mapTableRowsWith_text gp f hf finish hfinish listing hlisting rows.toList #[]]
    rfl
  | .algorithm n sm lines =>
    show algLineText acc (mapAlgLines (finish := finish) f #[] lines.toList).toList = _
    rw [mapAlgLines_text f hf finish hfinish lines.toList #[]]
    rfl
  | .logo content => simp [mapBlock, blockTextOne, mapInlinesFinish_text f hf finish hfinish content]
  | .bibliography src style items =>
    show blockTextBibItems acc (mapBibItems (finish := finish) f #[] items.toList).toList = _
    rw [mapBibItems_text f hf finish hfinish items.toList #[]]
    rfl
  | .contents spec entries =>
    show blockTextContentsEntries acc
      (mapContentsEntries (finish := finish) f #[] entries.toList).toList = _
    rw [mapContentsEntries_text f hf finish hfinish entries.toList #[]]
    rfl
  | .verbatim _ _ spec =>
    simp only [mapBlock, blockTextOne, hlisting]
    cases hc : spec.caption with
    | none => simp [ListingSpec.capText, hc]
    | some p =>
      simp [ListingSpec.capText, hc,
        mapInlinesFinish_text f hf finish hfinish p.2]
  | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ => rfl
termination_by structural b

public theorem mapBlockListWith_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText) (bs : List Block)
    (out : Array Block) (acc : String) :
    blockTextList acc (mapBlockList (finish := finish) (listing := listing) gp f out bs).toList
      = blockTextList (blockTextList acc out.toList) bs := by
  match bs with
  | [] => simp [mapBlockList, blockTextList]
  | b :: rest =>
    rw [mapBlockList, mapBlockListWith_text gp f hf finish hfinish listing hlisting rest]
    rw [Array.toList_push, blockTextList_chain]
    simp [blockTextList, mapBlockWith_text gp f hf finish hfinish listing hlisting]
termination_by structural bs

public theorem mapBlockItemsWith_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (mapBlockItems (finish := finish) (listing := listing) gp f out items).toList
      = blockTextItems (blockTextItems acc out.toList) items := by
  match items with
  | [] => simp [mapBlockItems, blockTextItems]
  | item :: rest =>
    rw [mapBlockItems, mapBlockItemsWith_text gp f hf finish hfinish listing hlisting rest]
    rw [Array.toList_push, blockTextItems_chain]
    simp [blockTextItems, blockTextList,
      mapBlockListWith_text gp f hf finish hfinish listing hlisting item.toList #[]]
termination_by structural items

public theorem mapBlockColsWith_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText)
    (cols : List (BoxWidth × Array Block))
    (out : Array (BoxWidth × Array Block)) (acc : String) :
    blockTextColumns acc (mapBlockCols (finish := finish) (listing := listing) gp f out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols := by
  match cols with
  | [] => simp [mapBlockCols, blockTextColumns]
  | (w, body) :: rest =>
    rw [mapBlockCols, mapBlockColsWith_text gp f hf finish hfinish listing hlisting rest]
    rw [Array.toList_push, blockTextColumns_chain]
    simp [blockTextColumns, blockTextList,
      mapBlockListWith_text gp f hf finish hfinish listing hlisting body.toList #[]]
termination_by structural cols

public theorem mapTableRowsWith_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText)
    (rows : List (Array (Array Block)))
    (out : Array (Array (Array Block))) (acc : String) :
    blockTextTableRows acc (mapTableRows (finish := finish) (listing := listing) gp f out rows).toList
      = blockTextTableRows (blockTextTableRows acc out.toList) rows := by
  match rows with
  | [] => simp [mapTableRows, blockTextTableRows]
  | row :: rest =>
    rw [mapTableRows, mapTableRowsWith_text gp f hf finish hfinish listing hlisting rest]
    rw [Array.toList_push, blockTextTableRows_chain]
    simp [blockTextTableRows, blockTextItems,
      mapBlockItemsWith_text gp f hf finish hfinish listing hlisting row.toList #[]]
termination_by structural rows

end

public theorem mapBlocksPicWith_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText) :
    Conserves blocksText (mapBlocksPic (finish := finish) (listing := listing) gp f) := fun xs => by
  show blockTextList "" (mapBlockList (finish := finish) (listing := listing) gp f #[] xs.toList).toList = _
  rw [mapBlockListWith_text gp f hf finish hfinish listing hlisting xs.toList #[]]
  rfl

public theorem mapBlocksWith_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (finish : Array Inline → Array Inline) (hfinish : Conserves plainText finish)
    (listing : ListingSpec → ListingSpec)
    (hlisting : ∀ spec, (listing spec).capText = spec.capText) :
    Conserves blocksText (mapBlocks (finish := finish) (listing := listing) f) :=
  mapBlocksPicWith_text id f hf finish hfinish listing hlisting

public theorem mapBlock_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (acc : String) (b : Block) :
    blockTextOne acc (mapBlock gp f b) = blockTextOne acc b :=
  mapBlockWith_text gp f hf id (fun _ => rfl) id (fun _ => rfl) acc b

public theorem mapBlockList_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (bs : List Block)
    (out : Array Block) (acc : String) :
    blockTextList acc (mapBlockList gp f out bs).toList
      = blockTextList (blockTextList acc out.toList) bs :=
  mapBlockListWith_text gp f hf id (fun _ => rfl) id (fun _ => rfl) bs out acc

public theorem mapBlockItems_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) (items : List (Array Block))
    (out : Array (Array Block)) (acc : String) :
    blockTextItems acc (mapBlockItems gp f out items).toList
      = blockTextItems (blockTextItems acc out.toList) items :=
  mapBlockItemsWith_text gp f hf id (fun _ => rfl) id (fun _ => rfl) items out acc

public theorem mapBlockCols_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x)
    (cols : List (BoxWidth × Array Block))
    (out : Array (BoxWidth × Array Block)) (acc : String) :
    blockTextColumns acc (mapBlockCols gp f out cols).toList
      = blockTextColumns (blockTextColumns acc out.toList) cols :=
  mapBlockColsWith_text gp f hf id (fun _ => rfl) id (fun _ => rfl) cols out acc

public theorem mapBlocksPic_text (gp : Pic.Picture → Pic.Picture) (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) :
    Conserves blocksText (mapBlocksPic gp f) :=
  mapBlocksPicWith_text gp f hf id (fun _ => rfl) id (fun _ => rfl)

public theorem mapBlocks_text (f : Inline → Inline)
    (hf : ∀ x, plainTextOne (f x) = plainTextOne x) :
    Conserves blocksText (mapBlocks f) :=
  mapBlocksPic_text id f hf

/-- Push one leaf onto a reversed region, joining neighbouring text leaves
only, never across a style, link, overlay, footnote or other semantic
boundary. -/
private def pushLocationText (out : List Inline) (x : Inline) : List Inline :=
  match x with
  | .text s =>
    match out with
    | .text t :: rest => .text (t ++ s) :: rest
    | _ => x :: out
  | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _ | .located _ _
  | .role _ _ | .link _ _ | .label _ | .ref _ _ _ _ | .decorated _ _ | .boxed _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .pageNumber | .pageCount | .linebreak _
  | .strut _ | .italicCorr _ | .onSteps _ _ | .altSteps _ _ _ | .image _ _ _
  | .icon _ _ | .cite _ _ | .cited _ _ _ | .footnote _ _ => x :: out

private def joinLocationBody (out : List Inline) : List Inline → List Inline
  | [] => out
  | x :: rest => joinLocationBody (pushLocationText out x) rest

private def spliceLocationOne (out : List Inline) (x : Inline) : List Inline :=
  match x with
  | .located _ body => joinLocationBody out body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _
  | .role _ _ | .link _ _ | .label _ | .ref _ _ _ _ | .decorated _ _ | .boxed _ _
  | .fill | .hspace _ _ | .rule _ _ _ | .pageNumber | .pageCount | .linebreak _
  | .strut _ | .italicCorr _ | .onSteps _ _ | .altSteps _ _ _ | .image _ _ _
  | .icon _ _ | .cite _ _ | .cited _ _ _ | .footnote _ _ => pushLocationText out x

private def spliceLocations (out : List Inline) : List Inline → List Inline
  | [] => out
  | x :: rest => spliceLocations (spliceLocationOne out x) rest

private def finishLocations (xs : Array Inline) : Array Inline :=
  (spliceLocations [] xs.toList).reverse.toArray

private theorem pushLocationText_reading (out : List Inline) (x : Inline) :
    plainTextList (pushLocationText out x).reverse =
      plainTextList out.reverse ++ plainTextOne x := by
  cases x <;>
    try simp [pushLocationText, List.reverse_cons, plainTextList_append,
      plainTextList]
  cases out with
  | nil => simp [plainTextList, plainTextOne]
  | cons y rest =>
    cases y <;> simp [List.reverse_cons, plainTextList_append,
      plainTextList, plainTextOne, String.append_assoc]

private theorem joinLocationBody_reading (xs : List Inline) (out : List Inline) :
    plainTextList (joinLocationBody out xs).reverse =
      plainTextList out.reverse ++ plainTextList xs := by
  match xs with
  | [] => simp [joinLocationBody, plainTextList]
  | x :: rest =>
    rw [joinLocationBody, joinLocationBody_reading rest, pushLocationText_reading]
    simp [plainTextList, String.append_assoc]

private theorem spliceLocations_reading (xs : List Inline) (out : List Inline) :
    plainTextList (spliceLocations out xs).reverse =
      plainTextList out.reverse ++ plainTextList xs := by
  match xs with
  | [] => simp [spliceLocations, plainTextList]
  | x :: rest =>
    cases x <;>
      simp [spliceLocations, spliceLocationOne, spliceLocations_reading rest, joinLocationBody_reading,
        pushLocationText_reading, plainTextList, plainTextOne, String.append_assoc]

private theorem finishLocations_text : Conserves plainText finishLocations := by
  intro xs
  simp [finishLocations, plainText, spliceLocations_reading, plainTextList]

/-- Erase diagnostic wrappers and join adjacent text throughout an inline region. -/
public def eraseLocationInlines (xs : Array Inline) : Array Inline :=
  mapInlines id xs finishLocations

public theorem eraseLocationInlines_text : Conserves plainText eraseLocationInlines :=
  mapInlinesFinish_text id (fun _ => rfl) finishLocations finishLocations_text

private theorem joinLocationBody_append (out xs ys : List Inline) :
    joinLocationBody out (xs ++ ys) =
      joinLocationBody (joinLocationBody out xs) ys := by
  induction xs generalizing out with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, joinLocationBody, ih]

private theorem pushLocationText_append (out : List Inline) (s t : String) :
    pushLocationText (pushLocationText out (.text s)) (.text t) =
      pushLocationText out (.text (s ++ t)) := by
  cases out with
  | nil => rfl
  | cons x xs => cases x <;> simp [pushLocationText, String.append_assoc]

private theorem joinLocationBody_push (out acc : List Inline) (x : Inline) :
    joinLocationBody out (pushLocationText acc x).reverse =
      pushLocationText (joinLocationBody out acc.reverse) x := by
  cases x <;>
    try simp only [pushLocationText, List.reverse_cons, joinLocationBody_append, joinLocationBody]
  rename_i s
  cases acc with
  | nil => rfl
  | cons y rest =>
    cases y <;>
      try simp only [pushLocationText, List.reverse_cons, joinLocationBody_append, joinLocationBody]
    rename_i t
    exact (pushLocationText_append (joinLocationBody out rest.reverse) t s).symm

private theorem joinLocationBody_join (out acc xs : List Inline) :
    joinLocationBody out (joinLocationBody acc xs).reverse =
      joinLocationBody (joinLocationBody out acc.reverse) xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [joinLocationBody, ih, joinLocationBody_push]

private theorem joinLocationBody_splice (out acc xs : List Inline) :
    joinLocationBody out (spliceLocations acc xs).reverse =
      spliceLocations (joinLocationBody out acc.reverse) xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp only [spliceLocations, ih, spliceLocationOne,
      joinLocationBody_join, joinLocationBody_push]

private theorem spliceLocations_append (out xs ys : List Inline) :
    spliceLocations out (xs ++ ys) =
      spliceLocations (spliceLocations out xs) ys := by
  induction xs generalizing out with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, spliceLocations, ih]

public theorem eraseLocationInlines_located_exact (span : Span)
    (before body after : Array Inline) :
    eraseLocationInlines (before ++ #[.located span body] ++ after) =
      eraseLocationInlines (before ++ body ++ after) := by
  simp only [eraseLocationInlines, mapInlines, mapInlineList_finish_exact,
    Array.toList_append, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, mapInline]
  simp only [finishLocations, spliceLocations_append,
    spliceLocations, spliceLocationOne, joinLocationBody_splice, List.reverse_nil, joinLocationBody]

private def eraseLocationPicture (pic : Pic.Picture) : Pic.Picture :=
  pic.mapLabels eraseLocationInlines

private def eraseListingSource (spec : ListingSpec) : ListingSpec :=
  { spec with source := none }

/-- The source-free view of a compiled document: diagnostic provenance erased
in every body and furniture region, adjacent text rejoined. -/
public def eraseLocations (doc : Doc) : Doc :=
  mapDoc eraseLocationInlines
    (mapBlocksPic eraseLocationPicture id · finishLocations eraseListingSource) doc

public theorem eraseLocations_text :
    Conserves (fun doc : Doc =>
      (blocksText doc.body, (furnitureInlines doc).map plainText)) eraseLocations := by
  intro doc
  apply Prod.ext
  · exact mapBlocksPicWith_text eraseLocationPicture id (fun _ => rfl)
      finishLocations finishLocations_text eraseListingSource (fun _ => rfl) doc.body
  · simp only [eraseLocations, furnitureInlines_mapDoc, Array.map_map, Function.comp_def]
    congr 1
    funext xs
    exact eraseLocationInlines_text xs

private theorem linkBlockList_text (url : String) (xs : List Block) (acc : String) :
    blockTextList acc (linkBlockList url xs) = blockTextList acc xs := by
  simp [linkBlockList, blockTextList, blockTextOne]

public theorem linkBlocks_text (url : String) : Conserves blocksText (linkBlocks url) := by
  intro xs
  simp [linkBlocks, blocksText, linkBlockList_text]

public theorem Styles.linkBodyAfford_text (s : Styles) (kind : String) :
    Conserves blocksText (s.linkBodyAfford kind) := by
  unfold Styles.linkBodyAfford
  exact mapBlocks_text (s.linkLeafAfford kind) (s.linkLeafAfford_text kind)

/-- A caption fills only an undeclared alternative. -/
private def setAltFill (alt : Alt) : Alt → Alt
  | .undeclared => alt
  | .decorative => .decorative
  | .described t => .described t
  | .citing runs => .citing runs

private theorem setAltFill_fixed_point (alt : Alt) (a : Alt) (h : a ≠ .undeclared) :
    setAltFill alt a = a := by
  cases a with
  | undeclared => exact absurd rfl h
  | decorative => rfl
  | described _ => rfl
  | citing _ => rfl

/-- Give every non-text object with no alternative yet this one, as a
`figure` caption names what it captions. -/
private def setAltLeaf (alt : Alt) (x : Inline) : Inline :=
  match x with
  | .image src size old => .image src size (setAltFill alt old)
  | _ => x

private def setAltPic (alt : Alt) (pic : Pic.Picture) : Pic.Picture :=
  { pic with alt := setAltFill alt pic.alt }

public def setAltBlocks (alt : Alt) (xs : Array Block) : Array Block :=
  mapBlocksPic (setAltPic alt) (setAltLeaf alt) xs

public theorem setAltBlocks_text (alt : Alt) :
    Conserves blocksText (setAltBlocks alt) :=
  mapBlocksPic_text _ _ (fun x => by cases x <;> rfl)

/-- Runs with `s` joined to the words that end them. -/
public def AltRun.pushText (acc : Array AltRun) (s : String) : Array AltRun :=
  match acc.back? with
  | some (.text t) => acc.pop.push (.text (t ++ s))
  | _ => if s.isEmpty then acc else acc.push (.text s)

mutual

/-- A caption's first page as an alternative's runs onto `acc`: its words as `firstPageText` reads
them, each citation a run the reference list sets. -/
-- conserves: none — one page's reading.
public def captionRunsOne (acc : Array AltRun) (x : Inline) : Array AltRun :=
  match x with
  | .cite form keys => acc.push (.cite form keys none)
  | .altSteps spec firstPage otherPage =>
    let blank (xs : Array Inline) : Bool := !(plainText xs).toList.any (!·.isWhitespace)
    if spec.maxStep == 0 || (blank firstPage && !blank otherPage) then
      captionRunsList acc otherPage.toList
    else captionRunsList acc firstPage.toList
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body
  | .link _ body | .decorated _ body | .boxed _ body | .onSteps _ body | .footnote _ body | .cited _ _ body =>
    captionRunsList acc body.toList
  -- A page reference's folio is the layout's, as the first page's reading leaves it.
  | .ref _ .page _ _ => acc
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .label _
  | .ref _ _ _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _
  | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ =>
    AltRun.pushText acc (plainTextOne x)

public def captionRunsList (acc : Array AltRun) : List Inline → Array AltRun
  | [] => acc
  | x :: rest => captionRunsList (captionRunsOne acc x) rest

end

private theorem said_join_push (acc : Array AltRun) (r : AltRun) :
    String.join ((acc.push r).toList.map AltRun.said) =
      String.join (acc.toList.map AltRun.said) ++ r.said := by
  simp [String.join_append]

private theorem pushText_said (acc : Array AltRun) (s : String) :
    String.join ((AltRun.pushText acc s).toList.map AltRun.said) =
      String.join (acc.toList.map AltRun.said) ++ s := by
  unfold AltRun.pushText
  split
  · next t h =>
    have hne : acc ≠ #[] := by
      intro he; simp [he] at h
    have hacc : acc = acc.pop.push (.text t) := by
      rw [Array.back?_eq_some_iff] at h
      obtain ⟨ys, hys⟩ := h
      rw [hys]; simp
    conv => rhs; rw [hacc]
    rw [said_join_push, said_join_push]
    simp [AltRun.said, String.append_assoc]
  · split
    · next hs =>
      have he : s = "" := by simpa [String.isEmpty_iff] using hs
      simp [he]
    · rw [said_join_push]; rfl

mutual

private theorem captionRunsOne_said (acc : Array AltRun) (x : Inline) :
    String.join ((captionRunsOne acc x).toList.map AltRun.said) =
      firstPageTextOne (String.join (acc.toList.map AltRun.said)) x := by
  cases x with
  | cite form keys =>
    simp only [captionRunsOne, firstPageTextOne, said_join_push, AltRun.said, Option.getD_none,
      plainTextOne]
    rfl
  | altSteps spec firstPage otherPage =>
    simp only [captionRunsOne, firstPageTextOne]
    split
    · exact captionRunsList_said acc otherPage.toList
    · exact captionRunsList_said acc firstPage.toList
  | styled _ body | colored _ _ body | located _ body | role _ body | link _ body
  | decorated _ body | boxed _ body | onSteps _ body | footnote _ body | cited _ _ body =>
    simp only [captionRunsOne, firstPageTextOne]
    exact captionRunsList_said acc body.toList
  | ref key form text target =>
    cases form <;> simp only [captionRunsOne, firstPageTextOne, pushText_said] <;> rfl
  | text _ | math _ _ | formula _ _ _ | image _ _ _ | icon _ _ | label _ | fill
  | hspace _ _ | rule _ _ _ | strut _ | italicCorr _ | pageNumber | pageCount | linebreak _ =>
    simp only [captionRunsOne, firstPageTextOne, pushText_said]
    rfl

private theorem captionRunsList_said (acc : Array AltRun) : (l : List Inline) →
    String.join ((captionRunsList acc l).toList.map AltRun.said) =
      firstPageTextList (String.join (acc.toList.map AltRun.said)) l
  | [] => rfl
  | x :: rest => by
    simp only [captionRunsList, firstPageTextList]
    rw [captionRunsList_said (captionRunsOne acc x) rest, captionRunsOne_said acc x]

end

/-- A caption's citing alternative says what its words say until its citations resolve. -/
public theorem captionRuns_said (caption : Array Inline) :
    String.join ((captionRunsList #[] caption.toList).toList.map AltRun.said) =
      firstPageText caption := by
  rw [captionRunsList_said]
  simp [firstPageText]

/-- A caption's first page as the alternative of what it captions: its words, or, where it cites,
its runs, whose citations the reference list sets as the caption's. -/
public def captionAlt (caption : Array Inline) : Alt :=
  let runs := captionRunsList #[] caption.toList
  if runs.any (· matches .cite ..) then .citing runs else Alt.declare (firstPageText caption)

/-- A caption's first-page words as the alternative of what it captions. -/
public def captionAltBlocks (caption : Array Inline) (xs : Array Block) : Array Block :=
  setAltBlocks (captionAlt caption) xs

public theorem captionAltBlocks_text (caption : Array Inline) :
    Conserves blocksText (captionAltBlocks caption) :=
  setAltBlocks_text _

/-- A declaration met between blocks (`\footnotesize`, `\bfseries`, a bare
palette name), scoping every following block of its group. -/
public inductive Decl where
  | style (s : Style)
  | color (c : Color) (name : Option ColorRef)
  deriving Repr, BEq

/-- One declaration around a region: the node its grouped spelling elaborates to. -/
public def Decl.wrap : Decl → Array Inline → Array Inline
  | .style s, xs => #[.styled s xs]
  | .color c n, xs => #[.colored c n xs]

public theorem Decl.wrap_exact (d : Decl) (xs : Array Inline) :
    d.wrap xs = (match d with
      | .style s => #[.styled s xs]
      | .color c name => #[.colored c name xs]) := by
  cases d <;> rfl

/-- The open declarations around a region, outermost first. -/
public def wrapDecls (ds : List Decl) (xs : Array Inline) : Array Inline :=
  match ds with
  | [] => xs
  | d :: rest => d.wrap (wrapDecls rest xs)

public theorem wrapDecls_exact (ds : List Decl) (xs : Array Inline) :
    wrapDecls ds xs = (match ds with
      | [] => xs
      | d :: rest => d.wrap (wrapDecls rest xs)) := by
  cases ds <;> rfl

public theorem Decl.wrap_text (d : Decl) (xs : Array Inline) :
    plainText (d.wrap xs) = plainText xs := by
  cases d <;> simp [Decl.wrap, plainText, plainTextList, plainTextOne]

public theorem wrapDecls_text (ds : List Decl) : Conserves plainText (wrapDecls ds) := fun xs => by
  induction ds with
  | nil => rfl
  | cons d rest ih => simp only [wrapDecls, Decl.wrap_text, ih]

mutual

/-- The named size a paragraph is set in: the outermost size scope on the
chain of single wrappers around its whole content; hand-rolled, not a
`foldInlines` leaf, because it stops at that scope. -/
-- conserves: none — a classifier.
public def paraStepIn (xs : List Inline) : Option String :=
  match xs with
  | [x] => paraStepOne x
  | [] => none
  | .role n _ :: y :: rest =>
    if n == descLabelRole || n == itemLabelRole then paraStepIn (y :: rest) else none
  | _ :: _ :: _ => none

-- conserves: none — the one-node classifier.
public def paraStepOne (x : Inline) : Option String :=
  match x with
  | .styled (.size n) _ => some n
  | .styled (.fontSize _ _) _ | .styled .normal _ => none
  | .styled .bold body | .styled .italic body | .styled .mono body
  | .styled .smallcaps body | .styled .emph body | .styled .sans body
  | .styled .roman body | .styled .medium body | .styled (.series _) body
  | .styled .upright body | .styled (.lang _) body | .styled (.family _) body =>
    paraStepIn body.toList
  | .colored _ _ body => paraStepIn body.toList
  | .located _ body => paraStepIn body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .role _ _ | .link _ _ | .label _
  | .ref _ _ _ _ | .decorated _ _ | .boxed _ _ | .fill | .hspace _ _ | .rule _ _ _ | .pageNumber
  | .pageCount | .linebreak _ | .strut _ | .italicCorr _ | .onSteps _ _
  | .altSteps _ _ _ | .image _ _ _ | .icon _ _ | .cite _ _ | .cited _ _ _
  | .footnote _ _ => none

end

/-- The size step a paragraph is set at: the named size of the outermost scope
wrapping its whole content. -/
public def paraStep? (xs : Array Inline) : Option String := paraStepIn xs.toList

/-- The size step text a template inserts leads at: its own step at or above
the body's on `scale`; `none`, the template's own leading, for a smaller
one. -/
public def insertedStep? (scale : List (String × Nat)) (xs : Array Inline) : Option String :=
  (paraStep? xs).filter fun n => 1000 ≤ ((scale.find? (·.1 == n)).map (·.2)).getD 1000

mutual

/-- The wrapper chain with the size scope `paraStepIn` reads removed, every
other wrapper kept; hand-rolled, not `mapInlines`, as it rewrites only that
chain. -/
public def liftParaStepIn (xs : List Inline) : Array Inline :=
  match xs with
  | [x] => liftParaStepOne x
  | [] => #[]
  | y :: z :: rest => (y :: z :: rest).toArray

public def liftParaStepOne (x : Inline) : Array Inline :=
  match x with
  | .styled (.size _) body => body
  | .styled (.fontSize s l) body => #[.styled (.fontSize s l) body]
  | .styled .normal body => #[.styled .normal body]
  | .styled .bold body => #[.styled .bold (liftParaStepIn body.toList)]
  | .styled .italic body => #[.styled .italic (liftParaStepIn body.toList)]
  | .styled .mono body => #[.styled .mono (liftParaStepIn body.toList)]
  | .styled .smallcaps body => #[.styled .smallcaps (liftParaStepIn body.toList)]
  | .styled .emph body => #[.styled .emph (liftParaStepIn body.toList)]
  | .styled .sans body => #[.styled .sans (liftParaStepIn body.toList)]
  | .styled .roman body => #[.styled .roman (liftParaStepIn body.toList)]
  | .styled .medium body => #[.styled .medium (liftParaStepIn body.toList)]
  | .styled (.series w) body => #[.styled (.series w) (liftParaStepIn body.toList)]
  | .styled .upright body => #[.styled .upright (liftParaStepIn body.toList)]
  | .styled (.lang tag) body => #[.styled (.lang tag) (liftParaStepIn body.toList)]
  | .styled (.family k) body => #[.styled (.family k) (liftParaStepIn body.toList)]
  | .colored c n body => #[.colored c n (liftParaStepIn body.toList)]
  | .located span body => #[.located span (liftParaStepIn body.toList)]
  | .text s => #[.text s]
  | .math d src => #[.math d src]
  | .formula d src body => #[.formula d src body]
  | .role n body => #[.role n body]
  | .link url body => #[.link url body]
  | .label k => #[.label k]
  | .ref k f t g => #[.ref k f t g]
  | .decorated k body => #[.decorated k body]
  | .boxed b body => #[.boxed b body]
  | .fill => #[.fill]
  | .hspace g k => #[.hspace g k]
  | .rule w h r => #[.rule w h r]
  | .pageNumber => #[.pageNumber]
  | .pageCount => #[.pageCount]
  | .linebreak g => #[.linebreak g]
  | .strut h => #[.strut h]
  | .italicCorr m => #[.italicCorr m]
  | .onSteps spec body => #[.onSteps spec body]
  | .altSteps spec a b => #[.altSteps spec a b]
  | .image src size alt => #[.image src size alt]
  | .icon c label => #[.icon c label]
  | .cite f keys => #[.cite f keys]
  | .cited f keys ink => #[.cited f keys ink]
  | .footnote n body => #[.footnote n body]

end

/-- A paragraph's content with its step lifted to the element that carries it. -/
public def liftParaStep (xs : Array Inline) : Array Inline := liftParaStepIn xs.toList

mutual

private theorem liftParaStepIn_text (xs : List Inline) :
    plainText (liftParaStepIn xs) = plainTextList xs := by
  match xs with
  | [x] =>
    rw [liftParaStepIn, liftParaStepOne_text]
    simp [plainTextList]
  | [] => rw [liftParaStepIn]; rfl
  | y :: z :: rest => rw [liftParaStepIn]; simp [plainText]

private theorem liftParaStepOne_text (x : Inline) :
    plainText (liftParaStepOne x) = plainTextOne x := by
  match x with
  | .styled (.size _) body =>
    rw [liftParaStepOne]
    simp [plainText, plainTextOne]
  | .styled (.fontSize _ _) body | .styled .normal body =>
    rw [liftParaStepOne]; simp [plainText, plainTextList]
  | .styled (.bold) body | .styled (.italic) body | .styled (.mono) body
  | .styled (.smallcaps) body | .styled (.emph) body | .styled (.sans) body
  | .styled (.roman) body | .styled (.medium) body | .styled (.series _) body
  | .styled (.upright) body | .styled (.lang _) body | .styled (.family _) body
  | .colored _ _ body | .located _ body =>
    have ih := liftParaStepIn_text body.toList
    simp only [liftParaStepOne, plainText, plainTextList, plainTextOne] at ih ⊢
    simp [ih]
  | .text _ | .math _ _ | .formula _ _ _ | .role _ _ | .link _ _ | .label _
  | .ref _ _ _ _ | .decorated _ _ | .boxed _ _ | .fill | .hspace _ _ | .rule _ _ _ | .pageNumber
  | .pageCount | .linebreak _ | .strut _ | .italicCorr _ | .onSteps _ _
  | .altSteps _ _ _ | .image _ _ _ | .icon _ _ | .cite _ _ | .cited _ _ _ | .footnote _ _ =>
    rw [liftParaStepOne]; simp [plainText, plainTextList]

end

public theorem liftParaStep_text : Conserves plainText liftParaStep := fun xs => by
  show plainText (liftParaStepIn xs.toList) = plainText xs
  rw [liftParaStepIn_text]
  rfl

/-- Whether a declaration sets the size its runs take: a named step, an
explicit `\fontsize`, or `\normalfont`. -/
public def Decl.setsSize : Decl → Bool
  | .style (.size _) | .style (.fontSize _ _) | .style .normal => true
  | .style .bold | .style .italic | .style .mono | .style .smallcaps | .style .emph
  | .style .sans | .style .roman | .style .medium | .style (.series _) | .style .upright
  | .style (.lang _) | .style (.family _) | .color _ _ => false

/-- Whether a font-size length reads the size in force (`em`, `ex`). -/
public def affineFontRelative {α : Type} : Dim.Affine α → Bool
  | .lit g => g.width.em != 0 || g.width.ex != 0
  | .ref _ => false
  | .scale _ _ e => affineFontRelative e
  | .add a b | .sub a b => affineFontRelative a || affineFontRelative b

/-- Whether a declaration sets its runs' size whatever stood before it: a
named step, `\normalfont`, or an absolute `\fontsize`. -/
public def Decl.shadowsSize : Decl → Bool
  | .style (.size _) | .style .normal => true
  | .style (.fontSize s l) => !affineFontRelative s && !affineFontRelative l
  | .style .bold | .style .italic | .style .mono | .style .smallcaps | .style .emph
  | .style .sans | .style .roman | .style .medium | .style (.series _) | .style .upright
  | .style (.lang _) | .style (.family _) | .color _ _ => false

/-- Whether a declaration does nothing but set the size: a named step or a `\fontsize`. -/
public def Decl.onlySize : Decl → Bool
  | .style (.size _) | .style (.fontSize _ _) => true
  | .style .normal | .style .bold | .style .italic | .style .mono | .style .smallcaps
  | .style .emph | .style .sans | .style .roman | .style .medium | .style (.series _)
  | .style .upright | .style (.lang _) | .style (.family _) | .color _ _ => false

/-- The step a size declaration leaves in force: its named size, or `none`
under `\fontsize` or `\normalfont`; off a size declaration, nothing. -/
public def Decl.sizeStep? : Decl → Option (Option String)
  | .style (.size n) => some (some n)
  | .style (.fontSize _ _) | .style .normal => some none
  | .style .bold | .style .italic | .style .mono | .style .smallcaps | .style .emph
  | .style .sans | .style .roman | .style .medium | .style (.series _) | .style .upright
  | .style (.lang _) | .style (.family _) | .color _ _ => none

/-- The named step a list of declarations gives the paragraph they stand over:
the first size declaration's. -/
public def declStep (ds : List Decl) : Option String :=
  (ds.filterMap Decl.sizeStep?).head?.join

/-- The declarations in force where a paragraph ends, each size declaration a
later absolute one shadows dropped. -/
public def dropShadowedSizes : List Decl → List Decl
  | [] => []
  | d :: rest =>
    if d.onlySize && rest.any Decl.shadowsSize then dropShadowedSizes rest
    else d :: dropShadowedSizes rest

/-- A paragraph as it ends: its content wrapped in the declarations in force
there, shadowed sizes dropped. -/
@[expose] public def paraAt (ds : List Decl) (xs : Array Inline) : Array Inline :=
  let ds := dropShadowedSizes ds
  let inner := wrapDecls ds xs
  if !(ds.any Decl.setsSize) && (paraStep? inner).isSome then
    #[.styled (.size "normalsize") inner]
  else inner

public theorem paraAt_text (ds : List Decl) : Conserves plainText (paraAt ds) := fun xs => by
  unfold paraAt
  dsimp only
  split
  · simp only [plainText, plainTextList, plainTextOne]
    simpa [plainText] using wrapDecls_text (dropShadowedSizes ds) xs
  · exact wrapDecls_text _ xs

private theorem Decl.setsSize_iff (d : Decl) : d.setsSize = (d.sizeStep?).isSome := by
  rcases d with ⟨s⟩ | ⟨c, n⟩
  · cases s <;> rfl
  · rfl

private theorem Decl.shadowsSize_sets (d : Decl) (h : d.shadowsSize = true) :
    d.setsSize = true := by
  rcases d with ⟨s⟩ | ⟨c, n⟩
  · cases s <;> simp_all [Decl.shadowsSize, Decl.setsSize]
  · simp [Decl.shadowsSize] at h

private theorem paraStep_wrap_free (d : Decl) (h : d.setsSize = false) (xs : Array Inline) :
    paraStep? (d.wrap xs) = paraStep? xs := by
  rcases d with ⟨s⟩ | ⟨c, n⟩
  · cases s <;> simp_all [Decl.setsSize, Decl.wrap, paraStep?, paraStepIn, paraStepOne]
  · simp [Decl.wrap, paraStep?, paraStepIn, paraStepOne]

private theorem paraStep_wrap_size (d : Decl) (h : d.setsSize = true) (xs : Array Inline) :
    paraStep? (d.wrap xs) = (d.sizeStep?).join := by
  rcases d with ⟨s⟩ | ⟨c, n⟩
  · cases s <;> simp_all [Decl.setsSize, Decl.wrap, Decl.sizeStep?, paraStep?, paraStepIn,
      paraStepOne]
  · simp [Decl.setsSize] at h

private theorem dropShadowed_any (ds : List Decl) :
    (dropShadowedSizes ds).any Decl.setsSize = ds.any Decl.setsSize := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    simp only [dropShadowedSizes]
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      obtain ⟨x, hx, hs⟩ := List.any_eq_true.mp h.2
      have hr : rest.any Decl.setsSize = true :=
        List.any_eq_true.mpr ⟨x, hx, Decl.shadowsSize_sets x hs⟩
      simp [ih, hr]
    · simp [ih]

private theorem paraStep_wrapDecls (ds : List Decl) (xs : Array Inline) :
    paraStep? (wrapDecls ds xs) =
      if ds.any Decl.setsSize then declStep ds else paraStep? xs := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    simp only [wrapDecls]
    cases hs : d.setsSize with
    | true =>
      rw [paraStep_wrap_size d hs]
      cases hz : d.sizeStep? with
      | none =>
        have := Decl.setsSize_iff d
        simp [hs, hz] at this
      | some v => simp [declStep, hz, hs]
    | false =>
      have hz : d.sizeStep? = none := by
        have := Decl.setsSize_iff d
        rw [hs] at this
        cases h : d.sizeStep? with
        | none => rfl
        | some _ => simp [h] at this
      rw [paraStep_wrap_free d hs, ih]
      simp [hs, declStep, hz]

public theorem paraStep_paraAt_exact (ds : List Decl) (xs : Array Inline) :
    (paraStep? (paraAt ds xs)).filter (· != "normalsize") =
      (declStep (dropShadowedSizes ds)).filter (· != "normalsize") := by
  unfold paraAt
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    have hnil : (dropShadowedSizes ds).filterMap Decl.sizeStep? = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro x hx
      have hn := List.any_eq_false.mp h.1 x hx
      have := Decl.setsSize_iff x
      cases hz : x.sizeStep? with
      | none => rfl
      | some _ => simp [hz] at this; simp [this] at hn
    simp [paraStep?, paraStepIn, paraStepOne, declStep, hnil]
  · rename_i h
    rw [paraStep_wrapDecls]
    split
    · rfl
    · rename_i hany
      have hnil : (dropShadowedSizes ds).filterMap Decl.sizeStep? = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro x hx
        have hn := List.any_eq_false.mp (by simpa using hany) x hx
        have := Decl.setsSize_iff x
        cases hz : x.sizeStep? with
        | none => rfl
        | some _ => simp [hz] at this; simp [this] at hn
      have hnone : paraStep? xs = none := by
        rw [paraStep_wrapDecls] at h
        simp only [hany, Bool.false_eq_true, ite_false] at h
        simpa [hany] using h
      simp [hnone, declStep, hnil]

mutual

-- conserves: none — a census, not a rewrite.
/-- The text of inline content that stands under some `.styled st` with `p st`. -/
public def textUnder (p : Style → Bool) (x : Inline) : String :=
  match x with
  | .styled st body =>
    if p st then plainTextList body.toList else textUnderList p "" body.toList
  | .colored _ _ body => textUnderList p "" body.toList
  | .located _ body => textUnderList p "" body.toList
  | .role _ body => textUnderList p "" body.toList
  | .link _ body => textUnderList p "" body.toList
  | .decorated _ body | .boxed _ body => textUnderList p "" body.toList
  | .onSteps _ body => textUnderList p "" body.toList
  | .altSteps _ firstPage otherPage =>
    textUnderList p (textUnderList p "" firstPage.toList) otherPage.toList
  | .footnote _ body => textUnderList p "" body.toList
  | .cited _ _ ink => textUnderList p "" ink.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .linebreak _ => ""

public def textUnderList (p : Style → Bool) (acc : String) (xs : List Inline) : String :=
  match xs with
  | [] => acc
  | x :: rest => textUnderList p (acc ++ textUnder p x) rest

end

/-- Whether some open declaration is a style the predicate accepts. -/
public def Decl.anyStyle (p : Style → Bool) : List Decl → Bool
  | [] => false
  | .style s :: rest => p s || Decl.anyStyle p rest
  | .color _ _ :: rest => Decl.anyStyle p rest

public theorem decl_between_blocks_covers (p : Style → Bool) (ds : List Decl)
    (hd : Decl.anyStyle p ds = true) (xs : Array Inline) :
    textUnderList p "" (wrapDecls ds xs).toList = plainText xs := by
  induction ds with
  | nil => simp [Decl.anyStyle] at hd
  | cons d rest ih =>
    cases d with
    | style s =>
      simp only [Decl.anyStyle, Bool.or_eq_true] at hd
      simp only [wrapDecls, Decl.wrap]
      have hw : plainTextList (wrapDecls rest xs).toList = plainText xs :=
        wrapDecls_text rest xs
      show textUnderList p ("" ++ textUnder p (.styled s _)) [] = _
      rcases hd with h | h
      · simp [textUnderList, textUnder, h, hw]
      · cases hp : p s
        · simp [textUnderList, textUnder, hp, ih h]
        · simp [textUnderList, textUnder, hp, hw]
    | color c n =>
      simp only [Decl.anyStyle] at hd
      simp only [wrapDecls, Decl.wrap]
      show textUnderList p ("" ++ textUnder p (.colored c n _)) [] = _
      simp [textUnderList, textUnder, ih hd]

public theorem decl_spellings_agree (s : Style) (xs : Array Inline) :
    wrapDecls [.style s] xs = #[.styled s xs] := by rfl

/-- One character of a label's anchor: Unicode characters, ASCII word
characters and the conventional label punctuation survive. -/
private def labelAnchorChar (c : Char) : Char :=
  if c.toNat ≥ 0x80 || c.isAlpha || c.isDigit || c == ':' || c == '.' ||
      c == '-' || c == '_' then c
  else '-'

/-- The id a `\label` key takes in the HTML page and a resolved reference
targets: the key sanitised character-wise. -/
public def labelAnchor (key : String) : String :=
  match key.toList.map labelAnchorChar with
  | [] => "label"
  | l => String.ofList l

/-- Each top-level level-one section's anchor at its body index, claimed after every label's, whose
ids are their keys', and the ledger of their claims; a section yielding to a label clashes with
no title. -/
private def sectionClaims (body : Array Block) :
    Array (Option SectionAnchor) × NameClaim.Claims .dashed := Id.run do
  let labels := blockLabelKeys body
  let held : Std.HashSet String := labels.foldl (·.insert ·) {}
  let mut taken : NameClaim.Claims .dashed := {}
  for key in labels do
    taken := (taken.claim (labelAnchor key) key).2.2
  let mut out : Array (Option SectionAnchor) := #[]
  for b in body do
    if let .section 1 _ _ title := b then
      let base := if (slug title).isEmpty then "section" else slug title
      let (id, clash, next) := taken.claim base (firstPageText title)
      taken := next
      out := out.push (some { base, id, clash := clash.filter (!held.contains ·) })
    else out := out.push none
  -- A chapter claims after every section, so none of theirs moves.
  for h : i in [0:body.size] do
    if let .section .h1 _ _ title := body[i] then
      let base := if (slug title).isEmpty then "section" else slug title
      let (id, clash, next) := taken.claim base (firstPageText title)
      taken := next
      out := out.setIfInBounds i (some { base, id, clash := clash.filter (!held.contains ·) })
  return (out, taken)

/-- Each top-level chapter's and level-one section's anchor, at its body index, in flow order. -/
public def sectionAnchors (body : Array Block) : Array (Option SectionAnchor) :=
  (sectionClaims body).1

/-- Each top-level heading's anchor at its body index: a chapter's and a level-one section's its
`sectionAnchors` one, a deeper heading's claimed after every label's and every section's, so none of theirs moves. -/
public def headingAnchors (body : Array Block) : Array (Option SectionAnchor) := Id.run do
  let (sections, ledger) := sectionClaims body
  let mut taken := ledger
  let mut out := sections
  for h : i in [0:body.size] do
    if let .section level _ _ title := body[i] then
      if level != .title && level != .h1 && level != .h2 then
        let base := if (slug title).isEmpty then "section" else slug title
        let (id, clash, next) := taken.claim base (firstPageText title)
        taken := next
        out := out.setIfInBounds i (some { base, id, clash })
  return out

/-- Whether blocks hold a table of contents anywhere. -/
public def holdsContents (body : Array Block) : Bool :=
  foldBlocks (fun acc b => acc || b matches .contents ..) (fun acc _ => acc) false body

/-- The anchors a flow's top-level headings answer to: every heading's where a table of contents
lists them, else the level-one sections' alone. -/
public def flowAnchors (body : Array Block) : Array (Option SectionAnchor) :=
  if holdsContents body then headingAnchors body else sectionAnchors body

public theorem labelAnchor_fixed_point (key : String) (hne : key ≠ "")
    (hkeep : ∀ c ∈ key.toList,
      (c.toNat ≥ 0x80 || c.isAlpha || c.isDigit || c == ':' || c == '.' ||
        c == '-' || c == '_') = true) :
    labelAnchor key = key := by
  have hm : key.toList.map labelAnchorChar = key.toList := by
    have h := List.map_congr_left (l := key.toList) (f := labelAnchorChar) (g := id)
      (fun c hc => by simp [labelAnchorChar, hkeep c hc])
    simpa using h
  unfold labelAnchor
  rw [hm]
  split
  · rename_i he
    exact False.elim (hne (String.toList_eq_nil_iff.mp he))
  · exact String.ofList_toList

private theorem labelAnchorChar_not (c bad : Char)
    (hbad : (bad.toNat ≥ 0x80 || bad.isAlpha || bad.isDigit || bad == ':' ||
      bad == '.' || bad == '-' || bad == '_') = false) :
    labelAnchorChar c ≠ bad := by
  unfold labelAnchorChar
  split <;> rintro rfl <;> simp_all

public theorem labelAnchor_single_token (key : String) :
    ((labelAnchor key).toList.all fun c =>
      !(c == ' ' || c == '\t' || c == '\n' || c == '\r' ||
        c == '"' || c == '\'')) = true := by
  unfold labelAnchor
  split
  · decide
  · simp only [String.toList_ofList, List.all_eq_true, List.mem_map]
    rintro c ⟨a, _, rfl⟩
    have h1 := labelAnchorChar_not a ' ' (by decide)
    have h2 := labelAnchorChar_not a '\t' (by decide)
    have h3 := labelAnchorChar_not a '\n' (by decide)
    have h4 := labelAnchorChar_not a '\r' (by decide)
    have h5 := labelAnchorChar_not a '"' (by decide)
    have h6 := labelAnchorChar_not a '\'' (by decide)
    simp [h1, h2, h3, h4, h5, h6]

/-- What a label names: the kind of the numbered thing it bound to, read by
cleveref's name prefixes. -/
public inductive RefKind where
  | heading | chapter | equation | figure | table | algorithm
  deriving Repr, BEq

/-- One label's binding: the number it bound to, with the kind of the numbered
thing when elaboration made one, and the statement it stands in: its heading and its own number. -/
public structure RefBinding where
  kind : Option RefKind
  num : String
  statement : Option (String × Option String) := none
  /-- The title of what the label names, as hyperref's `\nameref` sets it. -/
  name : Option (Array Inline) := none
  deriving Repr, BEq

private def indexStep {α : Type} (m : Std.HashMap String (String × α))
    (e : String × α) : Std.HashMap String (String × α) :=
  if m.contains e.1 then m else m.insert e.1 e

/-- The lookup index of a keyed store: each key to its earliest entry. -/
public def keyIndex {α : Type} (xs : Array (String × α)) :
    Std.HashMap String (String × α) :=
  xs.foldl (init := ∅) indexStep

private theorem absent_of_getElem?_none {α : Type}
    (m : Std.HashMap String (String × α)) (k : String) (h : m[k]? = none) :
    m.contains k = false := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, h]
  rfl

private theorem key_ne_of_absent {α : Type} (m : Std.HashMap String (String × α))
    (e : String × α) (k : String) (hc : m.contains e.1 = true) (hk : m[k]? = none) :
    (e.1 == k) = false := by
  cases hEq : (e.1 == k) with
  | true =>
    rw [eq_of_beq hEq, absent_of_getElem?_none m k hk] at hc
    exact absurd hc (by simp)
  | false => rfl

private theorem absent_of_beq {α : Type} (m : Std.HashMap String (String × α))
    (e : String × α) (k : String) (hc : m.contains e.1 = false)
    (hEq : (e.1 == k) = true) : m[k]? = none := by
  rw [eq_of_beq hEq, Std.HashMap.contains_eq_isSome_getElem?] at hc
  simpa using hc

private theorem indexList {α : Type} :
    ∀ (l : List (String × α)) (m : Std.HashMap String (String × α)) (k : String),
      (l.foldl indexStep m)[k]? = m[k]?.or (l.find? (·.1 == k))
  | [], m, k => by cases h : m[k]? <;> simp [h]
  | e :: rest, m, k => by
    rw [List.foldl_cons, indexList rest]
    cases hc : m.contains e.1 with
    | true =>
      cases hk : m[k]? with
      | some v => simp [indexStep, hc, hk]
      | none => simp [indexStep, hc, hk, key_ne_of_absent m e k hc hk]
    | false =>
      cases hEq : (e.1 == k) with
      | true =>
        have hk := absent_of_beq m e k hc hEq
        have hstep : indexStep m e = m.insert e.1 e := by simp [indexStep, hc]
        rw [hstep, Std.HashMap.getElem?_insert, hEq]
        simp [hk, hEq]
      | false => simp [indexStep, hc, hEq, Std.HashMap.getElem?_insert]

public theorem keyIndex_find? {α : Type} (xs : Array (String × α)) (k : String) :
    (keyIndex xs)[k]? = xs.find? (·.1 == k) := by
  unfold keyIndex
  rw [← Array.foldl_toList, indexList, Std.HashMap.getElem?_empty,
    ← Array.find?_toList]
  rfl

/-- Each label key with the binding its `\label` took in flow order; `none`
where nothing numbers. -/
public abbrev RefTable := Array (String × Option RefBinding)

/-- cleveref's name for a kind; every heading level below the chapter takes the section name. -/
public def crefNameOf (loc : Locale) : RefKind → CrefName
  | .heading => loc.crefSection
  | .chapter => loc.crefChapter
  | .equation => loc.crefEquation
  | .figure => loc.crefFigure
  | .table => loc.crefTable
  | .algorithm => loc.crefAlgorithm

/-- Every kind, for the coverage contract. -/
public def RefKind.all : List RefKind :=
  [.heading, .chapter, .equation, .figure, .table, .algorithm]

public theorem RefKind.all_complete (k : RefKind) : RefKind.all.contains k := by
  cases k <;> rfl

public theorem crefNameOf_covers :
    (Locale.builtin.all fun l =>
      (RefKind.all.all fun k =>
        !(crefNameOf l k).one.isEmpty && !(crefNameOf l k).many.isEmpty &&
        !(crefNameOf l k).capOne.isEmpty && !(crefNameOf l k).capMany.isEmpty)
      && !l.crefRangeTo.isEmpty) = true := by decide +kernel

/-- A cref-form number: equation numbers keep their parentheses in every
cleveref form; every other kind shows the bare number. -/
public def crefNum (b : RefBinding) : String :=
  if b.kind == some .equation then "(" ++ b.num ++ ")" else b.num

/-- The text one resolved reference shows: `\ref`'s bare number, `\eqref`'s
parentheses, and cleveref's forms over the binding's kind. -/
public def refText (loc : Locale) (form : RefForm) (b : RefBinding) : String :=
  let numText := crefNum b
  match form with
  | .plain => b.num
  | .paren => "(" ++ b.num ++ ")"
  | .labelOnly => numText
  | .cref cap =>
    match b.kind with
    | some k =>
      (if cap then (crefNameOf loc k).capOne else (crefNameOf loc k).one)
        ++ "\u00a0" ++ numText
    | none => b.num
  | .crefRange cap =>
    (match b.kind with
     | some k =>
       (if cap then (crefNameOf loc k).capMany else (crefNameOf loc k).many)
         ++ "\u00a0" ++ numText
     | none => b.num)
      ++ " " ++ loc.crefRangeTo ++ "\u00a0"
  | .name cap =>
    match b.kind with
    | some k => if cap then (crefNameOf loc k).capOne else (crefNameOf loc k).one
    | none => b.num
  | .headed =>
    match b.statement, b.kind with
    | some (h, some n), _ => h ++ "\u00a0" ++ n
    | some (h, none), _ => h
    | none, some k => (crefNameOf loc k).capOne ++ "\u00a0" ++ numText
    | none, none => b.num
  | .title => (b.name.map metaText).getD ""
  -- A page's folio is known only once a setting places the label (`fillPages`).
  | .page => "??"
  | .starred f => refText loc f b

/-- What a resolved reference shows: `\nameref` the title it names as set, linked unless starred,
and `??` where nothing gave a title; any other form its text, targeting the label's anchor. -/
public def refInline (loc : Locale) (key : String) (form : RefForm) (b : RefBinding) : Inline :=
  match form.titled, b.name with
  | true, some n => if form.linked then .link ("#" ++ labelAnchor key) n else .role titleTextRole n
  | true, none => .ref key form "??" none
  | false, _ => .ref key form (refText loc form b) (some (labelAnchor key))

/-- A reference against its label's binding: a label nothing numbered keeps `??` and no target
unless the form prints its title. -/
public def refResolved (loc : Locale) (key : String) (form : RefForm) (b : RefBinding) : Inline :=
  if b.num.isEmpty && !form.titled && !form.paged then .ref key form "??" none
  else refInline loc key form b

/-- A reference to a label nothing numbers: a page reference still targets the label, whose page
it prints once a setting places it, and any other form keeps `??` and no target. -/
public def unboundRef (key : String) (form : RefForm) : Inline :=
  .ref key form "??" (if form.paged then some (labelAnchor key) else none)

public def resolveOneRefWith (loc : Locale)
    (look : String → Option (String × Option RefBinding)) (key : String)
    (form : RefForm) : Inline :=
  match look key with
  | some (_, some b) => refResolved loc key form b
  | some (_, none) => unboundRef key form
  | none => .ref key form "??" none

/-- One reference against the table: a numbered key takes its form's text and
the label's anchor; any other keeps `??` and no target. -/
public def resolveOneRef (loc : Locale) (table : RefTable) (key : String)
    (form : RefForm) : Inline :=
  resolveOneRefWith loc (fun k => table.find? (·.1 == k)) key form

public theorem resolveOneRef_scan (loc : Locale) (table : RefTable) (key : String)
    (form : RefForm) :
    resolveOneRef loc table key form =
      match table.find? (·.1 == key) with
      | some (_, some b) => refResolved loc key form b
      | some (_, none) => unboundRef key form
      | none => .ref key form "??" none := by rfl

/-- Resolution's one rewrite: every `.ref` rewritten from the lookup,
everything else walked by the generic map. -/
private def resolveRefLeaf (loc : Locale)
    (look : String → Option (String × Option RefBinding))
    (x : Inline) : Inline :=
  match x with
  | .ref key form _ _ => resolveOneRefWith loc look key form
  | _ => x

public def refScan (table : RefTable) : String → Option (String × Option RefBinding) :=
  fun k => table.find? (·.1 == k)

public theorem refLook_agree (table : RefTable) :
    (fun k => (keyIndex table)[k]?) = refScan table := by
  funext k
  exact keyIndex_find? table k

/-- The pass over an index already built, taken as a parameter so it is
evaluated once rather than per leaf. -/
private def resolveRefsIdx (loc : Locale)
    (idx : Std.HashMap String (String × Option RefBinding))
    (xs : Array Block) : Array Block :=
  -- No picture label holds a reference: the label reader refuses `\ref`.
  mapBlocks (resolveRefLeaf loc (fun k => idx[k]?)) xs

private def resolveRefInlinesIdx (loc : Locale)
    (idx : Std.HashMap String (String × Option RefBinding))
    (xs : Array Inline) : Array Inline :=
  mapInlines (resolveRefLeaf loc (fun k => idx[k]?)) xs

-- conserves: none — rewrites a ref's placeholder to its number.
public def resolveRefInline (loc : Locale) (table : RefTable) (x : Inline) : Inline :=
  mapInline (resolveRefLeaf loc (refScan table)) x

-- conserves: none — rewrites ref placeholders to numbers.
public def resolveRefs (loc : Locale) (table : RefTable) (xs : Array Block) : Array Block :=
  resolveRefsIdx loc (keyIndex table) xs

public theorem resolveRefs_agree (loc : Locale) (table : RefTable) (xs : Array Block) :
    resolveRefs loc table xs = mapBlocks (fun x => match x with
      | .ref key form _ _ => resolveOneRef loc table key form
      | _ => x) xs := by
  unfold resolveRefs resolveRefsIdx
  rw [refLook_agree]
  congr 1

public theorem resolveOneRef_exact (loc : Locale) (table : RefTable) (key : String)
    (form : RefForm)
    (b : RefBinding) (h : ∃ e ∈ table, e.1 = key ∧ e.2 = some b)
    (huniq : ∀ e ∈ table, e.1 = key → e.2 = some b) :
    resolveOneRef loc table key form = refResolved loc key form b := by
  rw [resolveOneRef_scan]
  obtain ⟨e, hmem, hkey, _⟩ := h
  have hfind : ∃ f, table.find? (·.1 == key) = some f := by
    have : (table.find? (·.1 == key)).isSome := by
      rw [Array.find?_isSome]
      exact ⟨e, hmem, by simp [hkey]⟩
    exact Option.isSome_iff_exists.mp this
  obtain ⟨f, hf⟩ := hfind
  have hfmem := Array.mem_of_find?_eq_some hf
  have hfkey : f.1 = key := by
    have := Array.find?_some hf
    simpa using this
  have hfval : f.2 = some b := huniq f hfmem hfkey
  obtain ⟨fk, fv⟩ := f
  simp only at hfval
  subst hfval
  rw [hf]

public theorem resolveOneRef_missing (loc : Locale) (table : RefTable) (key : String)
    (form : RefForm) (h : ∀ e ∈ table, e.1 ≠ key) :
    resolveOneRef loc table key form = .ref key form "??" none := by
  rw [resolveOneRef_scan]
  have hfind : table.find? (·.1 == key) = none := by
    rw [Array.find?_eq_none]
    intro e hmem
    simp [h e hmem]
  rw [hfind]

/-- The inline face of `resolveRefs`, for the furniture regions `mapDoc` hands it. -/
-- conserves: none — rewrites ref placeholders to numbers.
public def resolveRefInlines (loc : Locale) (table : RefTable) (xs : Array Inline) :
    Array Inline :=
  resolveRefInlinesIdx loc (keyIndex table) xs

private theorem resolveRefInlines_agree (loc : Locale) (table : RefTable) (xs : Array Inline) :
    resolveRefInlines loc table xs = mapInlines (resolveRefLeaf loc (refScan table)) xs := by
  unfold resolveRefInlines resolveRefInlinesIdx
  rw [refLook_agree]

/-- One unresolved node the IR carries, by the key a diagnostic can be matched to. -/
public inductive Unresolved where
  | ref (key : String)
  | cite (key : String)
  deriving Repr, BEq, DecidableEq

@[expose] public def Unresolved.isCite : Unresolved → Bool
  | .cite _ => true
  | .ref _ => false

/-- One pending thing a backend would ship unnamed: a node of the IR, or an
image source with no payload in the store. -/
public inductive Pending where
  | node (u : Unresolved)
  | image (src : String)
  deriving Repr, BEq, DecidableEq

public def Pending.key : Pending → String
  | .node (.ref k) => k
  | .node (.cite k) => k
  | .image s => s

/-- Whether a diagnostic names a pending node: its structured subject is the node's key. -/
public def _root_.LeanTex.Core.Diag.mentions (d : Diag) (p : Pending) : Bool :=
  d.subject == some p.key

/-- One node's contribution: a `.ref` with no target, or any `.cite`, which
`Bib.apply` replaces when it answers. -/
@[expose] public def pendingLeaf : Inline → Array Unresolved
  | .ref key _ _ none => #[.ref key]
  | .cite _ keys => keys.map .cite
  | .image _ _ alt => alt.pendingKeys.map .cite
  | _ => #[]

/-- The fold step of the census: each node's leaf appended. -/
@[expose] public def pendingStep (acc : Array Unresolved) (x : Inline) : Array Unresolved :=
  let leaf := pendingLeaf x
  acc ++ leaf

/-- Every unresolved reference and citation the document's regions carry, in document order. -/
@[expose] public def pendingNodes (doc : Doc) : Array Unresolved :=
  foldDoc pendingStep #[] doc

public theorem pendingNodes_withListNotes (doc : Doc) (m : Nat) :
    pendingNodes (doc.withListNotes m) = pendingNodes doc := by
  simp only [pendingNodes, foldDoc, furnitureInlines, Doc.withListNotes]

public theorem pendingNodes_addPictures (doc : Doc) (more : Array (String × PicSrc)) :
    pendingNodes (doc.addPictures more) = pendingNodes doc := by
  simp only [pendingNodes, foldDoc, furnitureInlines, Doc.addPictures]

/-- Every image source the document names that the store holds no payload for. -/
public def pendingImages (doc : Doc) (store : Image.Store) : Array Pending :=
  ((imageRequests doc).filter fun req => (store.infoRequest? req).isNone).map
    (fun req => .image req.src)

/-- Everything a backend would ship as `??`, `?`, or a placeholder box. -/
public def pending (doc : Doc) (store : Image.Store) : Array Pending :=
  let images := pendingImages doc store
  (pendingNodes doc).map .node ++ images

/-- The distinct keys of the unresolved references, first occurrence first. -/
public def pendingRefKeys (doc : Doc) : Array String :=
  (pendingNodes doc).foldl (init := #[]) fun out p =>
    match p with
    | .ref k => if out.contains k then out else out.push k
    | .cite _ => out

/-- W0349's judge: every distinct key a `\ref` still shows `??` for, named at
its first site with the cause the table knows. -/
private def refDiagLeaf (look : String → Option (String × Option RefBinding))
    (spanOf : String → Option Span) (key : String) : Diag :=
  let unnumbered := Diag.of .W0349 (Diag.say .W0349 .reference key)
    (spanOf key) (detail := some "its \\label stands where nothing is numbered")
    (help := "move the \\label after a numbered heading, a captioned float, or into an equation")
    (subject := some key)
  match look key with
  | some (_, some b) =>
    if b.num.isEmpty then unnumbered
    else
      Diag.of .W0349 (Diag.say .W0349 .reference key)
        (spanOf key) (detail := some "its \\label stands where no heading or caption gives it a title")
        (help := "\\nameref sets the title of the heading or caption its \\label follows")
        (subject := some key)
  | some (_, none) => unnumbered
  | _ =>
    Diag.of .W0349 (Diag.say .W0349 .reference key) (spanOf key)
      (help := s!"declare \\label\{{key}} after the numbered thing it names")
      (subject := some key)

private def refDiagsIdx (idx : Std.HashMap String (String × Option RefBinding))
    (spanOf : String → Option Span) (keys : Array String) : Array Diag :=
  keys.map (refDiagLeaf (fun k => idx[k]?) spanOf)

public def refDiags (table : RefTable) (spanOf : String → Option Span) (doc : Doc) :
    Array Diag :=
  refDiagsIdx (keyIndex table) spanOf (pendingRefKeys doc)

private theorem refDiags_agree (table : RefTable) (spanOf : String → Option Span) (doc : Doc) :
    refDiags table spanOf doc
      = (pendingRefKeys doc).map (refDiagLeaf (refScan table) spanOf) := by
  unfold refDiags refDiagsIdx
  rw [refLook_agree]

private theorem pendingRefKeys_grow (l : List Unresolved) :
    ∀ (out : Array String) (k : String), k ∈ out →
      k ∈ l.foldl (init := out) fun out p => match p with
        | .ref k => if out.contains k then out else out.push k
        | .cite _ => out := by
  induction l with
  | nil => intro out k hk; simpa using hk
  | cons p rest ih =>
    intro out k hk
    simp only [List.foldl_cons]
    apply ih
    cases p with
    | ref k' =>
      show k ∈ (if out.contains k' = true then out else out.push k')
      split <;> simp [hk]
    | cite _ => exact hk

private theorem pendingRefKeys_mem (doc : Doc) (key : String)
    (h : Unresolved.ref key ∈ pendingNodes doc) : key ∈ pendingRefKeys doc := by
  unfold pendingRefKeys
  rw [← Array.foldl_toList]
  rw [Array.mem_def] at h
  generalize (pendingNodes doc).toList = l at h ⊢
  generalize (#[] : Array String) = out
  induction l generalizing out with
  | nil => simp at h
  | cons p rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hrest
    · apply pendingRefKeys_grow
      show key ∈ (if out.contains key = true then out else out.push key)
      split
      · rename_i hc; exact Array.contains_iff_mem.mp hc
      · simp
    · exact ih hrest _

public theorem refDiags_named (table : RefTable) (spanOf : String → Option Span) (doc : Doc)
    (key : String) (h : Unresolved.ref key ∈ pendingNodes doc) :
    ∃ d ∈ refDiags table spanOf doc, d.mentions (.node (.ref key)) = true := by
  have hk := pendingRefKeys_mem doc key h
  rw [refDiags_agree]
  unfold refDiagLeaf refScan
  refine ⟨_, Array.mem_map_of_mem hk, ?_⟩
  cases hf : table.find? (·.1 == key) with
  | none => simp [Diag.mentions, Diag.of_subject, Pending.key]
  | some e =>
    obtain ⟨_, b⟩ := e
    cases b with
    | none => simp [Diag.mentions, Diag.of_subject, Pending.key]
    | some b =>
      simp only [Diag.mentions, Pending.key]
      split <;> simp [Diag.of_subject]

/-- One label leaf into the rows, bound to the float binding in force. -/
private def floatLabelPush (float : Option RefBinding)
    (out : Array (String × Option RefBinding)) : Inline → Array (String × Option RefBinding)
  | .label k => out.push (k, float)
  | _ => out

/-- The float binding in force at every `.label` of the numbered IR; `float`
is the enclosing captioned float's, `none` outside. -/
public def floatLabelEnter (float : Option RefBinding) (out : Array (String × Option RefBinding))
    (b : Block) : Array (String × Option RefBinding) × Option RefBinding :=
  match b with
  | .equation _ _ | .section _ _ _ _ => (out, none)
  | .float kind num _ _ _ =>
    (out, match num with
      | none => float
      | some m =>
        match kind with
        -- A subfloat keeps its parent's kind, as cleveref's subfigure names are the figure's.
        | .sub => some { kind := float.bind (·.kind)
                         num := ((float.map (·.num)).getD "") ++ subLetter m.n }
        | .figure => some { kind := some .figure, num := m.render }
        | .table => some { kind := some .table, num := m.render }
        | .algorithm => some { kind := some .algorithm, num := m.render })
  | .para _ | .list _ _ _ | .center _ | .ragged _ _ | .quote _ _ | .lines _ | .abstract _
  | .titled _ _ _ | .disclosure _ _ _ | .role _ _ | .link _ _ | .spaced _ _ | .columns _ | .onSteps _ _
  | .altSteps _ _ _ | .only _ _ | .nav _ _ | .note _ | .frame _ _ _ _ _
  | .framefoot _ | .table _ _ _ _ _ _ | .algorithm _ _ _ | .logo _
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .picture _ | .bibliography _ _ _ | .contents _ _ => (out, float)

/-- The label walk over the shared context fold: `floatLabelEnter` binds,
`floatLabelPush` collects. -/
public def floatLabelWalk : CtxFold (Option RefBinding) (Array (String × Option RefBinding)) where
  openBlock := floatLabelEnter
  closeBlock := fun _ out _ => out
  openInline := fun float out x => (floatLabelPush float out x, float)
  closeInline := fun _ out _ => out

/-- The float rows of the numbered body: every label with the float binding in
force where it stands. -/
public def floatLabelRows (xs : Array Block) : RefTable :=
  foldCtxBlocks floatLabelWalk none #[] xs

/-- A label table entry whose key's first `.label` stands under a captioned
float takes that float's number. -/
private def floatRowLeaf (look : String → Option (String × Option RefBinding))
    (e : String × Option RefBinding) : String × Option RefBinding :=
  match look e.1 with
  | some (_, some n) => (e.1, some n)
  | _ => e

/-- The merge over an index already built, taken as a parameter so it is evaluated once. -/
private def withFloatRowsIdx (labels : RefTable)
    (idx : Std.HashMap String (String × Option RefBinding)) : RefTable :=
  labels.map (floatRowLeaf (fun k => idx[k]?))

public def withFloatRows (labels rows : RefTable) : RefTable :=
  withFloatRowsIdx labels (keyIndex rows)

/-- Every label inside a top-level frame, bound to the frame's number, as beamer's `\label` in a
frame takes it. -/
public def frameLabelRows (xs : Array Block) (nums : Array (Option Nat)) : RefTable := Id.run do
  let keyOf := fun (out : Array String) (x : Inline) =>
    if let .label k := x then out.push k else out
  let mut out : RefTable := #[]
  for (b, i) in xs.zipIdx do
    if let .frame title _ _ _ body := b then
      if let some n := nums[i]?.join then
        let keys := foldBlocks (fun out _ => out) keyOf (foldInlines keyOf #[] title) body
        out := out ++ keys.map fun k => (k, some { kind := none, num := toString n })
  return out

/-- The table with each key no construct numbered taking its row's binding. -/
public def withUnboundRows (labels rows : RefTable) : RefTable :=
  let idx := keyIndex rows
  labels.map fun e => match e.2, idx[e.1]? with
    | none, some (_, some b) => (e.1, some b)
    | _, _ => e

/-- A title as `\nameref` and a bookmark set it: without the labels and notes it holds, which
name and mark the heading alone. -/
-- conserves: none — drops the labels and notes a title holds.
public def nameOf (title : Array Inline) : Array Inline :=
  let keep := fun (x : Inline) => match x with
    | .label _ | .footnote _ _ => false
    | _ => true
  mapInlines id title (finish := fun xs => xs.filter keep)

/-- The title each label names, as hyperref's `\@currentlabelname` holds it: a float's caption
inside the float, else the last heading's title before it, its short one among `shorts` where it
declared one; a blank one names nothing. -/
public def labelNames (xs : Array Block) (shorts : Array ShortTitle := #[]) :
    Std.HashMap String (Array Inline) := Id.run do
  let keyOf := fun (out : Array String) (x : Inline) =>
    if let .label k := x then out.push k else out
  let named := fun (m : Std.HashMap String (Array Inline)) (keys : Array String)
      (n : Array Inline) =>
    keys.foldl (fun m k => if m.contains k then m else m.insert k n) m
  let titled := fun (n : Array Inline) => if (metaText n).trimAscii.isEmpty then none else some n
  let mut current : Option (Array Inline) := none
  let mut out : Std.HashMap String (Array Inline) := {}
  let listed := shortTitlesAt (shorts.filter (·.named)) xs
  for h : i in [0:xs.size] do
    let b := xs[i]
    if let .section _ _ _ title := b then
      current := titled (nameOf (listedTitleAt listed i title))
    if let .float _ _ _ body caption := b then
      -- A subfloat's label names its own caption, as subcaption's `\nameref`.
      let subs := foldBlocks (fun acc blk => if let .float _ _ _ sb sc := blk then acc.push (sb, sc)
        else acc) (fun acc _ => acc) #[] body
      for (sb, sc) in subs do
        if let some sn := titled (nameOf sc) then
          out := named out (foldBlocks (fun out _ => out) keyOf (foldInlines keyOf #[] sc) sb) sn
      if let some n := (titled (nameOf caption)).orElse fun _ => current then
        out := named out (foldBlocks (fun out _ => out) keyOf (foldInlines keyOf #[] caption) body) n
    else if let some n := current then
      out := named out (foldBlocks (fun out _ => out) keyOf #[] #[b]) n
  return out

/-- The label keys a name's own `\nameref`s reach. -/
private def titleRefKeys (n : Array Inline) : Array String :=
  foldInlines (fun out x =>
    if let .ref k f _ _ := x then (if f.titled then out.push k else out) else out) #[] n

/-- A table lookup whose bindings carry the names resolved so far. -/
private def namedLook (base : String → Option (String × Option RefBinding))
    (memo : Std.HashMap String (Array Inline)) (k : String) : Option (String × Option RefBinding) :=
  match base k, memo[k]? with
  | some (key, some b), n => some (key, some { b with name := n })
  | some (key, none), some n => some (key, some { kind := none, num := "", name := some n })
  | some (key, none), none => some (key, none)
  | none, some n => some (k, some { kind := none, num := "", name := some n })
  | none, none => none

private theorem filter_length_le {α : Type} (p q : α → Bool) (hqp : ∀ x, q x = true → p x = true) :
    ∀ l : List α, (l.filter q).length ≤ (l.filter p).length
  | [] => by simp
  | x :: xs => by
    have ih := filter_length_le p q hqp xs
    by_cases hq : q x = true
    · simp [hq, hqp x hq]; omega
    · by_cases hp : p x = true
      · simp [hq, hp]; omega
      · simp [hq, hp]; omega

private theorem filter_length_lt {α : Type} (p q : α → Bool) (hqp : ∀ x, q x = true → p x = true) :
    ∀ (l : List α) (k : α), k ∈ l → p k = true → q k = false →
      (l.filter q).length < (l.filter p).length
  | [], _, hk, _, _ => absurd hk List.not_mem_nil
  | x :: xs, k, hk, hpk, hqk => by
    have hle := filter_length_le p q hqp xs
    rcases List.mem_cons.mp hk with rfl | hk'
    · simp [hpk, hqk]; omega
    · have ih := filter_length_lt p q hqp xs k hk' hpk hqk
      by_cases hq : q x = true
      · simp [hq, hqp x hq]; omega
      · by_cases hp : p x = true
        · simp [hq, hp]; omega
        · simp [hq, hp]; omega

/-- One label's name with its references resolved, after the names it reaches, into `memo`; a name
reached again on its own chain is left out, so the `\nameref` closing the loop keeps `??`. -/
private def nameClose (loc : Locale) (base : String → Option (String × Option RefBinding))
    (raw : Std.HashMap String (Array Inline)) (visiting : Std.HashSet String)
    (memo : Std.HashMap String (Array Inline)) (k : String) : Std.HashMap String (Array Inline) :=
  if _hc : memo.contains k || visiting.contains k then memo
  else match _h : raw[k]? with
    | none => memo
    | some n =>
      let memo := (titleRefKeys n).foldl (init := memo) fun memo d =>
        nameClose loc base raw (visiting.insert k) memo d
      memo.insert k (mapInlines (resolveRefLeaf loc (namedLook base memo)) n)
termination_by (raw.keys.filter (fun x => !visiting.contains x)).length
decreasing_by
  have hv : visiting.contains k = false := by
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at _hc
    exact _hc.2
  have hk : k ∈ raw.keys := by
    rw [Std.HashMap.mem_keys]
    exact (Std.HashMap.getElem?_eq_some_iff.mp _h).1
  apply filter_length_lt (fun x => !visiting.contains x) (fun x => !(visiting.insert k).contains x)
    _ _ k hk (by simp [hv]) (by simp)
  intro x hx
  simp only [Std.HashSet.contains_insert, Bool.not_or, Bool.and_eq_true] at hx
  exact hx.2

/-- Every label's name with the references inside it resolved, numbers from `base` and titles from
the names they reach. -/
private def resolvedNames (loc : Locale) (base : String → Option (String × Option RefBinding))
    (raw : Std.HashMap String (Array Inline)) : Std.HashMap String (Array Inline) :=
  raw.fold (init := {}) fun memo k _ => nameClose loc base raw {} memo k

/-- The table with each binding carrying the title its label names (`labelNames`), the references
inside it resolved, a label nothing numbered taking a binding with its title alone. -/
public def withLabelNames (loc : Locale) (labels : RefTable) (xs : Array Block)
    (shorts : Array ShortTitle := #[]) : RefTable :=
  let idx := keyIndex labels
  let raw := idx.fold (init := labelNames xs shorts) fun m k e => match e.2.bind (·.name) with
    | some n => m.insert k n
    | none => m
  let names := resolvedNames loc (fun k => idx[k]?) raw
  labels.map fun e => match e.2, names[e.1]? with
    | some b, n => (e.1, some { b with name := n })
    | none, some n => (e.1, some { kind := none, num := "", name := some n })
    | none, none => e

private theorem withFloatRows_agree (labels rows : RefTable) :
    withFloatRows labels rows
      = labels.map (floatRowLeaf (refScan rows)) := by
  unfold withFloatRows withFloatRowsIdx
  rw [refLook_agree]

public theorem withFloatRows_finds (labels rows : RefTable) (key : String) (b : RefBinding)
    (hrow : rows.find? (·.1 == key) = some (key, some b))
    (hkey : (labels.find? (·.1 == key)).isSome) :
    (withFloatRows labels rows).find? (·.1 == key) = some (key, some b) := by
  rw [withFloatRows_agree]
  unfold refScan
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hkey
  have hekey : e.1 = key := by simpa using Array.find?_some he
  rw [Array.find?_map]
  have hp : ((fun x : String × Option RefBinding => x.1 == key) ∘
      floatRowLeaf (fun k => rows.find? (·.1 == k)))
      = fun e : String × Option RefBinding => e.1 == key := by
    funext x
    cases hx : rows.find? (·.1 == x.1) with
    | none => simp [Function.comp, floatRowLeaf, hx]
    | some p =>
      obtain ⟨pk, pv⟩ := p
      cases pv <;> simp [Function.comp, floatRowLeaf, hx]
  rw [hp, he, Option.map_some]
  unfold floatRowLeaf
  rw [hekey]
  simp [hrow]

public theorem refs_agree_with_numbering (loc : Locale) (labels : RefTable) (xs : Array Block)
    (within : Bool) (key : String) (b : RefBinding) (form : RefForm) (t : String) (a : Option String)
    (hrow : (floatLabelRows (numberFloats xs within)).find? (·.1 == key)
      = some (key, some b))
    (hkey : (labels.find? (·.1 == key)).isSome) :
    resolveRefInline loc (withFloatRows labels (floatLabelRows (numberFloats xs within)))
        (.ref key form t a)
      = refResolved loc key form b := by
  have h := withFloatRows_finds labels _ key b hrow hkey
  show resolveOneRef _ _ key form = _
  rw [resolveOneRef_scan]
  rw [h]

private def dumpDiag (d : Diag) : String :=
  let where' := match d.span with
    | some sp => s!"{sp.pos.line}:{sp.pos.col}"
    | none => "-"
  let detail := match d.detail with
    | some t => s!" | detail: {t}"
    | none => ""
  let help := match d.help with
    | some h => s!" | help: {h}"
    | none => ""
  s!"{d.severity.label}[{d.code}] {where'} {d.message}{detail}{help}\n"

public def dump (doc : Doc) (diags : Array Diag) : String :=
  let opts := if doc.classOptions == "" then "" else s!" [{doc.classOptions}]"
  let head := s!"class {doc.docClass.name}{opts}\n"
  let page :=
    s!"page {doc.page.width.toBpString}x{doc.page.height.toBpString} " ++
    s!"vmargin {doc.page.vmargin.toBpString} hmargin {doc.page.hmargin.toBpString}" ++
    (match doc.page.bmargin with
      | some m => s!" bmargin {m.toBpString}"
      | none => "") ++
    (if doc.page.fontSize != baseFontSize
      then s!" fontsize {doc.page.fontSize.toBpString}" else "") ++
    (match doc.page.sizes with
      | some sc => String.join ((sc.filter fun p =>
          sizeScale.lookup p.1 != some p.2).map fun p => s!" size {p.1} {p.2}")
      | none => "") ++
    (match doc.page.skips with
      | some sk => String.join ((sk.filter fun p =>
          sizeSkipScale.lookup p.1 != some p.2).map fun p => s!" skip {p.1} {p.2}")
      | none => "") ++
    (match doc.page.parskip with
      | some g => s!" parskip {dumpGlue g}"
      | none => "") ++
    (if doc.page.bleed != 0 then s!" bleed {doc.page.bleed.toBpString}" else "") ++
    String.join (doc.page.drawn.toList.map fun r =>
      s!" drawn {r.x.toBpString} {r.y.toBpString} {r.w.toBpString} {r.h.toBpString} {r.color}" ++
        (if r.front then " front" else "")) ++
    String.join (doc.page.boxes.toList.map fun b =>
      s!" box {b.kind.key} {b.x0.toBpString} {b.y0.toBpString} {b.x1.toBpString} {b.y1.toBpString}") ++
    (if doc.page.marks then " marks cut" else "") ++
    (if doc.page.markGap != cutMarkGap
      then s!" mark-gap {doc.page.markGap.toBpString}" else "") ++
    (if doc.page.markThickness != cutMarkThickness
      then s!" mark-thickness {doc.page.markThickness.toBpString}" else "") ++
    (match doc.page.hyphenate with
      | some b => s!" hyphenate {if b then "on" else "off"}"
      | none => "") ++
    (match doc.page.justify with
      | some b => s!" justify {if b then "on" else "off"}"
      | none => "") ++ "\n"
  let metaLine (label : String) (v : Option String) : String :=
    match v with
    | some s => s!"meta {label} {s.quote}\n"
    | none => ""
  let fontLine (label : String) (v : Option String) : String :=
    match v with
    | some f => s!"font {label} {f.quote}
"
    | none => ""
  let fontLines :=
    String.join (doc.fonts.dirs.toList.map fun d => fontLine "dir" (some d)) ++
    fontLine "body" doc.fonts.body ++ fontLine "sans" doc.fonts.sans ++
    fontLine "mono" doc.fonts.mono ++
    String.join (doc.fonts.families.toList.map fun (name, f) => fontLine s!"family.{name}" (some f)) ++
    String.join (doc.fonts.faces.toList.map fun ((slot, weight, italic), f) =>
      let slotName := match slot with
        | 0 => "body" | 1 => "sans" | 2 => "mono"
        | s => match doc.fonts.families[s - familySlotBase]? with
          | some (name, _) => s!"family.{name}"
          | none => s!"slot{s}"
      let variant := match weight, italic with
        | 400, false => "upright" | 700, false => "bold"
        | 400, true => "italic" | 700, true => "bolditalic"
        | w, i => (Weight.ofCss w).series ++ (if i then ".italic" else "")
      fontLine s!"{slotName}.{variant}" (some f))
  let paletteLines := String.join (doc.palette.entries.toList.map fun (n, c) =>
    let mark := if doc.palette.decorative.contains n then " decorative" else ""
    s!"palette {n.key} {c.hex}{mark}\n") ++
    (match doc.palette.coveredFraction with
     | some f => s!"palette covered {f}%\n"
     | none => "")
  let tokenLines := String.join (doc.tokens.entries.toList.map fun (n, g) =>
    s!"token {n} {dumpGlue g}\n") ++
    String.join (doc.captionPos.toList.map fun (scope, p) =>
      let pos := match p with
        | .top => "top"
        | .bottom => "bottom"
        | .auto => "auto"
      s!"caption-position {if scope.isEmpty then "*" else scope} {pos}\n")
  let runLines :=
    (match doc.head with
     | some xs => "runninghead\n" ++ dumpInlines "  " xs
     | none => "") ++
    (match doc.foot with
     | some xs => "runningfoot\n" ++ dumpInlines "  " xs
     | none => "") ++
    (if doc.chrome.hasFooter then
      let slot (label : String) (s : Option ChromeSlot) : String :=
        match s with
        | some v => s!" {label} {v.label}"
        | none => ""
      s!"chrome footer{slot "left" doc.chrome.footerLeft}{slot "right" doc.chrome.footerRight}\n"
     else "") ++
    (match doc.logo with
     | some xs => "logo\n" ++ dumpInlines "  " xs
     | none => "") ++
    (match doc.headline with
     | some hl =>
       "headline\n  title\n" ++ dumpInlines "    " hl.title ++
       (if hl.author.isEmpty then "" else "  author\n" ++ dumpInlines "    " hl.author) ++
       (if hl.institute.isEmpty then "" else
         "  institute\n" ++ dumpInlines "    " hl.institute)
     | none => "") ++
    (match doc.logoLeft with
     | some xs => "logoleft\n" ++ dumpInlines "  " xs
     | none => "") ++
    (match doc.logoRight with
     | some xs => "logoright\n" ++ dumpInlines "  " xs
     | none => "")
  let infoLines :=
    metaLine "title" doc.info.title ++ metaLine "author" doc.info.author ++
    metaLine "subject" doc.info.subject ++ metaLine "keywords" doc.info.keywords ++
    metaLine "url" doc.info.url ++ metaLine "image" doc.info.image ++
    metaLine "favicon" doc.info.favicon
  let outputLines :=
    (if doc.output.formats.isEmpty then ""
     else s!"output formats {String.intercalate "," doc.output.formats.toList}\n") ++
    (match doc.output.css with
     | some c => s!"output css {c}\n"
     | none => "") ++
    (match doc.output.stylesheet with
     | some s => s!"output stylesheet {s.quote}\n"
     | none => "")
  let asserts := String.join (doc.asserts.toList.map fun a =>
    s!"assert {a.kind.source}\n")
  let allowLine := if doc.allow.isEmpty then ""
    else s!"allow {String.intercalate ", " doc.allow.toList}\n"
  let body := dumpBlocks "" doc.body
  let ds :=
    if diags.isEmpty then
      "-- diagnostics\n(none)\n"
    else
      "-- diagnostics\n" ++ String.join (diags.toList.map dumpDiag)
  head ++ page ++ fontLines ++ paletteLines ++ tokenLines ++ runLines ++ infoLines ++ outputLines ++
    asserts ++ allowLine ++ body ++ ds

end LeanTex.Core.Ir
