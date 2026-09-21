import Std.Data.HashSet
import LeanTex.Core.Dim
import LeanTex.Core.Font
import LeanTex.Core.Hyphen
import LeanTex.Core.Ir
import LeanTex.Core.Oklab
import LeanTex.Core.ListMark
import LeanTex.Core.Diag
import LeanTex.Core.Struct

namespace LeanTex.Core.Layout

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font LeanTex.Core.Ir

/-- Per-level list indent as a function of the base size: 1.5 em — the
15 pt the engine shipped at the 10 pt base where it was picked, now
following the type, as classes.dtx derives its own leftmargin stack in
ems of the class base. Frozen at 15 pt, an enumerate marker plus its
`\labelsep` (together about 1.45 em) hung left past the print margin at
any base over about 21 pt — the poster's 31 pt body put its "1." 30 pt
into the trim. -/
def listIndentFor (base : Sp) : Sp := base * 3 / 2

structure Geom where
  pageW : Sp := pt 612
  pageH : Sp := pt 792
  hmargin : Sp := inch 1
  vmargin : Sp := inch 1
  fontSize : Sp := Ir.baseFontSize
  /-- The gap between peer paragraphs. The default is the declared token
  (`Ir.parskipDefault`, one rhythm quantum); a document declares its own
  through `\page{ parskip = ... }`. -/
  parskip : SymGlue := Ir.parskipDefault Ir.baseFontSize
  /-- Per-level list indent. The default is the engine's own choice —
  `listIndentFor`'s 1.5 em, shallower than classes.dtx's 2.5/2.2/1.87 em
  stack, which reads deep at this engine's narrower default measure; no
  external authority settles the ratio. A document owns the choice through
  `\style{itemize}{ indent = ... }` (the declared override this default
  yields to). -/
  listIndent : Sp := listIndentFor Ir.baseFontSize
  leading : Nat := 1000
  /-- Whether paragraphs may hyphenate; the class default resolved. Layout
  owns the gate so every caller — build, tests, oracles — obeys it. -/
  hyphenate : Bool := true
  /-- Whether paragraphs justify. Off means ragged right: word spaces stay
  natural, an underfull line costs nothing, and only real overfull is bad. -/
  justify : Bool := true
  /-- Whether boundary glyphs protrude into the margin (microtype's
  character protrusion). Layout owns the gate, as it owns `hyphenate`'s. -/
  protrude : Bool := true
  /-- Whether font boxes may expand within ±`expandLimit` (microtype's
  font expansion). Layout owns the gate, as it owns `protrude`'s. -/
  expand : Bool := true
  /-- Bleed past the trim edge, for the PDF writer: layout works in trim
  coordinates and never sees it. -/
  bleed : Sp := 0
  /-- Whether the pages ship printer's cut marks (`cutMarks`): derived
  from the trim and bleed, drawn on every face. Off by default. -/
  marks : Bool := false
  /-- The cut marks' declared trim clearance (`Ir.cutMarkGap` holds the
  default and its source). -/
  markGap : Sp := Ir.cutMarkGap
  /-- The cut marks' declared thickness (`Ir.cutMarkThickness` holds the
  default and its source). -/
  markThick : Sp := Ir.cutMarkThickness
  /-- The band a page footer reserves above the bottom margin: what its ink
  and body-side gap need beyond the margin. Zero when there is no footer or
  the margin already holds it, so an undeclared page is unchanged.
  `Layout.run` computes it (`furnitureBand`); everything else reads it only
  through `bodyBottom`. -/
  footBand : Sp := 0
  /-- The band a running head reserves below the top margin: what its ink
  and body-side gap need beyond the margin. Zero when there is no head or
  the margin already holds it, so an undeclared page is unchanged.
  `Layout.run` computes it (`furnitureBand`); everything else reads it only
  through `bodyTop`. -/
  headBand : Sp := 0
  /-- The size ladder in force (`Ir.PageSpec.scale`): what a named size
  run (`.styled (.size n)`) resolves through, so a venue's read-out ladder
  reaches the set text. Engine-derived default sizes (`sectionSize`, the
  footnote mark and body, chrome) stay steps of the engine's own scale:
  they are the engine's design, not the document's declarations, and the
  HTML backend keeps the same split. -/
  scale : List (String × Nat) := Ir.sizeScale
  deriving Repr

def Geom.textWidth (g : Geom) : Sp := g.pageW - 2 * g.hmargin

/-- The furniture ink-clearance floor: the least gap between a band's ink
and the body's, and between the body's ink and a picture block. The value
is TeX's own collision floor (`\lineskip=1pt`, TeXbook p.78), surviving
here only as clearance — the interline rule is metric (`B.placeLine`) and
never consults it. -/
def inkClearance : Sp := pt 1 -- TeXbook p.78: `\lineskip=1pt`, TeX's own floor

/-- The lowest y a body line's ink may reach: the bottom margin, less the
band a footer reserves. Every placement decision reads the page bottom from
here and nowhere else — a footer that draws over the last line of body text
is a worse bug than no footer. -/
def Geom.bodyBottom (g : Geom) : Sp := g.pageH - g.vmargin - g.footBand

/-- The highest y a body line's ink may reach: the top margin, plus the
band a running head reserves. Every placement decision reads the page top
from here and nowhere else — a head that draws over the first line of body
text is the same bug as the footer's, at the other edge. -/
def Geom.bodyTop (g : Geom) : Sp := g.vmargin + g.headBand

/-- Where one side's running furniture stands: `edge` is the distance from
the page edge to the furniture's nearest ink — the head's ink top, the
foot's ink *bottom* — and `band` is what the furniture's ink and its
body-side gap need beyond the margin. Both sides resolve through the one
`furnitureBand`, so the two edges are equal by definition
(`furniture_symmetric`): LaTeX's `\headsep` runs from the header's baseline
to the body while `\footskip` runs baseline to baseline (ltpage.dtx,
`\@outputpage`; the geometry manual §5.3 diagram), so equal declared values
leave the gap above the body larger than the gap below by the footer's
strut height — the correction every user of symmetric furniture rediscovers
(tex.sx/375264). Here the two distances are between ink edges by
definition, so the patch is unrepresentable. -/
structure FurnBand where
  edge : Sp
  band : Sp
  deriving Repr

/-- One side's edge gap. Declared gap: whatever of the margin the ink and
the gap leave, floored at zero — `top = g₁ + ink + g₂` read backwards, the
recovery `geometry_roundtrip` states. Default: the furniture hangs from
half the margin, the engine's own convention (no external authority names
the split; the head's ink top sat at `vmargin / 2` before the gap was
declarable, and an undeclared page must not move). -/
def furnEdge (vmargin ink : Sp) (gap : Option Sp) : Sp :=
  match gap with
  | some g => max 0 (vmargin - ink - g)
  | none => vmargin / 2

/-- Resolve one side's furniture band from the geometry, the furniture
line's ink extent, and the declared body-side gap (`none` requires only
`inkClearance` clearance, and the body keeps its margin unless the ink needs
more). A declared gap is exact (`furniture_gap_exact`): the edge gives
first, down to zero, then the band takes the rest from the body. -/
def furnitureBand (vmargin ink : Sp) (gap : Option Sp) : FurnBand :=
  { edge := furnEdge vmargin ink gap
    band := max 0 (furnEdge vmargin ink gap + ink + gap.getD inkClearance - vmargin) }

/-- The head line's baseline: its ink top stands exactly `edge` below the
page's top edge. -/
def furnHeadY (b : FurnBand) (ascent : Sp) : Sp := b.edge + ascent

/-- The foot line's baseline: its ink *bottom* stands exactly `edge` above
the page's bottom edge. Anchoring the ink rather than the baseline is the
whole difference from LaTeX's `\footskip`, and what makes the two edge
gaps one number. -/
def furnFootY (b : FurnBand) (pageH descent : Sp) : Sp := pageH - b.edge - descent

/-- The band arithmetic's one core inequality: the reservation always holds
the edge gap, the ink, and the required body-side gap, and it needs no sign
hypothesis — `\page{ vmargin = -5mm }` parses and flows into `Geom.ofPage`,
and the reservation still suffices there. Bare `Int` binders because
`omega` does not see through the `Sp` abbreviation. -/
private theorem furn_reserves (vm ink req edge : Int) :
    edge + ink + req ≤ vm + max 0 (edge + ink + req - vm) := by
  omega

/-- `furn_reserves` reflected through the page height: what
`bodyBottom_clears_footer` reads. -/
private theorem furn_reserves_below (pageH vm ink req edge band : Int)
    (h : edge + ink + req ≤ vm + band) :
    pageH - vm - band + ink + req ≤ pageH - edge := by
  omega

/-- The reservation is sufficient, for every geometry: the furniture's ink
plus its required body-side gap fit between the edge and the reserved body
boundary. -/
theorem furniture_band_reserves (vmargin ink : Sp) (gap : Option Sp) :
    (furnitureBand vmargin ink gap).edge + ink + gap.getD inkClearance
      ≤ vmargin + (furnitureBand vmargin ink gap).band := by
  simp only [furnitureBand]
  exact furn_reserves vmargin ink (gap.getD inkClearance) (furnEdge vmargin ink gap)

/-- With the band from `furnitureBand`, body ink starts at least the
required gap below the head's ink bottom (`furnHeadY + descent`, which is
`edge + ink`). -/
theorem bodyTop_clears_head (g : Geom) (ink : Sp) (gap : Option Sp)
    (h : g.headBand = (furnitureBand g.vmargin ink gap).band) :
    (furnitureBand g.vmargin ink gap).edge + ink + gap.getD inkClearance ≤ g.bodyTop := by
  simp only [Geom.bodyTop]
  rw [h]
  exact furniture_band_reserves g.vmargin ink gap

/-- The mirror of `bodyTop_clears_head`: body ink stops at least the
required gap above the foot's ink top (`furnFootY - ascent`, which is
`pageH - edge - ink`). -/
theorem bodyBottom_clears_footer (g : Geom) (ink : Sp) (gap : Option Sp)
    (h : g.footBand = (furnitureBand g.vmargin ink gap).band) :
    g.bodyBottom + ink + gap.getD inkClearance
      ≤ g.pageH - (furnitureBand g.vmargin ink gap).edge := by
  simp only [Geom.bodyBottom]
  rw [h]
  exact furn_reserves_below g.pageH g.vmargin ink (gap.getD inkClearance)
    (furnitureBand g.vmargin ink gap).edge (furnitureBand g.vmargin ink gap).band
    (furniture_band_reserves g.vmargin ink gap)

private theorem furn_symmetric (pageH vm a d edge band : Int) :
    (edge + a) - a = pageH - ((pageH - edge - d) + d) ∧
    (vm + band) - ((edge + a) + d) =
      ((pageH - edge - d) - a) - (pageH - vm - band) := by
  omega

/-- The user's rule, by the algebra of the definition: on every page the
head's ink top stands the same distance below the top edge as the foot's
ink bottom stands above the bottom edge, and on a full page the two
body-side gaps — head ink bottom to the body area's top, the body area's
bottom to foot ink top — agree. Over the placed baselines
(`furnHeadY`/`furnFootY`) and the reserved body area
(`Geom.bodyTop`/`bodyBottom`), for one `FurnBand` placing both sides —
which is what the running head and foot are: both set in the body face at
the page's font size, from the same declared gap. -/
theorem furniture_symmetric (g : Geom) (a d : Sp) (b : FurnBand)
    (hh : g.headBand = b.band) (hf : g.footBand = b.band) :
    furnHeadY b a - a = g.pageH - (furnFootY b g.pageH d + d) ∧
    g.bodyTop - (furnHeadY b a + d) =
      (furnFootY b g.pageH d - a) - g.bodyBottom := by
  simp only [furnHeadY, furnFootY, Geom.bodyTop, Geom.bodyBottom, hh, hf]
  exact furn_symmetric g.pageH g.vmargin a d b.edge b.band

private theorem furn_gap_exact (vm ink g : Int) :
    (vm + max 0 (max 0 (vm - ink - g) + ink + g - vm))
      - (max 0 (vm - ink - g) + ink) = g := by
  omega

/-- A declared body-side gap is honoured exactly, for every geometry: the
distance from the furniture's body-side ink edge to the reserved body
boundary is the declared value — the edge gives first, then the band takes
the rest from the body. -/
theorem furniture_gap_exact (vmargin ink gap : Sp) :
    (vmargin + (furnitureBand vmargin ink (some gap)).band)
      - ((furnitureBand vmargin ink (some gap)).edge + ink) = gap := by
  simp only [furnitureBand, furnEdge, Option.getD]
  exact furn_gap_exact vmargin ink gap

/-- The baseline-to-ink correction, applied exactly once, where the LaTeX
spellings are read: `\headsep` positions the header's *baseline* against
the body while the visual gap runs from the ink, and the difference is
what the line hangs below its baseline — the face's descent. `\footskip`
reads through the same correction — the symmetric reading — so equal
declared values mean equal ink gaps: the engine without the strut patch
equals LaTeX with it (tex.sx/375264's `\advance\footskip by \ht\strutbox`
is this correction applied by hand, on the one side LaTeX measures
baseline-to-baseline; a difference that survives the reading is declared
asymmetry, and N0021 names it). -/
def furnGapOfSep (sep descent : Sp) : Sp := sep - descent

/-- The inverse reading, for `geometry_roundtrip`: what a gap would be
declared as. -/
def furnSepOfGap (gap descent : Sp) : Sp := gap + descent

private theorem furn_roundtrip (sep d vm ink : Int) (h : ink + (sep - d) ≤ vm) :
    (sep - d) + d = sep ∧ max 0 (vm - ink - (sep - d)) + ink + (sep - d) = vm := by
  omega

/-- The reader loses nothing: reading a declared sep into the ink gap and
back yields the declared value — the correction is applied and un-applied
consistently — and the recovered edge restores the declared margin
(`top = g₁ + ink + g₂`) whenever the declaration fits it. -/
theorem geometry_roundtrip (sep descent vmargin ink : Sp)
    (h : ink + furnGapOfSep sep descent ≤ vmargin) :
    furnSepOfGap (furnGapOfSep sep descent) descent = sep ∧
    (furnitureBand vmargin ink (some (furnGapOfSep sep descent))).edge + ink +
      furnGapOfSep sep descent = vmargin := by
  simp only [furnGapOfSep, furnSepOfGap, furnitureBand, furnEdge] at h ⊢
  exact furn_roundtrip sep descent vmargin ink h

/-- The height between the margins: what `0.3\textheight` sizes against. -/
def Geom.textHeight (g : Geom) : Sp := g.pageH - 2 * g.vmargin

/-- A band slot's horizontal position: the declared side and the geometry,
plus the slot's own set width — no other slot is an argument, so nothing a
slot contains can move another slot's box. The right slot's box ends at the
right margin whatever it holds (`bandSlotX_right_pinned`): the folio has a
fixed position, and an empty or overlong neighbour is not a case. -/
def bandSlotX (g : Geom) (side : Ir.BandSide) (w : Sp) : Sp :=
  match side with
  | .left => g.hmargin
  | .right => g.pageW - g.hmargin - w

/-- The right slot's right edge is a constant of the geometry: `x + w` is
the right margin for every width, so no content — its own included — moves
the folio's anchor. -/
theorem bandSlotX_right_pinned (g : Geom) (w : Sp) :
    bandSlotX g .right w + w = g.pageW - g.hmargin := by
  have key : ∀ a b c : Int, a - b - c + c = a - b := by intro a b c; omega
  simp only [bandSlotX]
  exact key g.pageW g.hmargin w

/-- Resolve a document's `\page` declaration into layout geometry. One source
of truth: layout reads geometry only from here. -/
def Geom.ofPage (spec : Ir.PageSpec) (base : Geom := {}) : Geom :=
  { base with
    pageW := spec.width
    pageH := spec.height
    hmargin := spec.hmargin
    vmargin := spec.vmargin
    fontSize := spec.fontSize
    listIndent := listIndentFor spec.fontSize
    leading := spec.leading
    parskip := spec.parskip.getD (Ir.parskipDefault spec.fontSize)
    hyphenate := spec.hyphenate.getD base.hyphenate
    justify := spec.justify.getD base.justify
    protrude := spec.protrude.getD base.protrude
    expand := spec.expand.getD base.expand
    bleed := spec.bleed
    marks := spec.marks
    markGap := spec.markGap
    markThick := spec.markThickness
    scale := spec.scale }

/-- The slides stage carries a readable number of text lines. Tantau's rule
for presentations is lines, not points: "between 10 and 20 lines should fit
on each slide; the less lines, the more readable" (beamer user guide
§5.6.1). Every stage in `Ir.slidesStages` at the default margins and the
11 pt base sits inside that band — 16 full lines at 4:3, 15 at 16:9, up to
18 at √2:1 — so a stage cannot enter the table without entering this
contract, and the slides defaults cannot drift apart without failing the
build. -/
theorem slides_lines_in_band :
    ∀ r ∈ Ir.slidesStages,
      10 ≤ (r.2.2 - 2 * Ir.slidesVMargin) / leadingFor Ir.slidesFontSize ∧
      (r.2.2 - 2 * Ir.slidesVMargin) / leadingFor Ir.slidesFontSize ≤ 20 := by
  decide

/-- The bands never eat the measure: any slides-stage geometry whose head
and foot bands come from `furnitureBand` keeps a positive body height, and
Tantau's 10–20 lines (beamer user guide §5.6.1, the band
`slides_lines_in_band` states for the bare stages) still holds between
`bodyTop` and `bodyBottom` — for every stage in `Ir.slidesStages`, so a
stage entering the table enters this contract too. The ink hypotheses
allow each running line two em of the base size. That bound has no
external authority to cite: the OpenType spec bounds no line metric — OS/2
`sTypoAscender`: "It is not a general requirement that sTypoAscender −
sTypoDescender be equal to unitsPerEm", and the hhea ascender/descender
the engine reads are the font's own — so two em is this engine's coverage
choice, chosen generous against real faces (typical line metrics sit at
1.0–1.3 em; the shipped test faces are pinned under the bound in
`Tests.lean`). -/
theorem slides_lines_survive_bands (a d f : Sp)
    (hh : a + d ≤ 2 * Ir.slidesFontSize) (hf : f ≤ 2 * Ir.slidesFontSize)
    (g : Geom)
    (hg : g.pageH ∈ Ir.slidesStages.map (·.2.2))
    (hv : g.vmargin = Ir.slidesVMargin)
    (hhb : g.headBand = (furnitureBand g.vmargin (a + d) none).band)
    (hfb : g.footBand = (furnitureBand g.vmargin f none).band) :
    0 < g.bodyBottom - g.bodyTop ∧
    10 ≤ (g.bodyBottom - g.bodyTop) / leadingFor Ir.slidesFontSize ∧
    (g.bodyBottom - g.bodyTop) / leadingFor Ir.slidesFontSize ≤ 20 := by
  have hvm : Ir.slidesVMargin = 1730150 := by decide
  have hfs : Ir.slidesFontSize = 720896 := by decide
  have hld : leadingFor Ir.slidesFontSize = 865075 := by decide
  have hls : inkClearance = 65536 := by decide
  -- Every table height sits between the 16:9 row's 90 mm and the √2:1
  -- row's 105 mm; the band arithmetic below needs only the interval, and
  -- the interval is decided over the whole table — a taller or shorter
  -- stage fails here, not silently.
  have hrange : ∀ r ∈ Ir.slidesStages,
      16719420 ≤ r.2.2 ∧ r.2.2 ≤ 19505990 := by decide
  have ⟨r, hr, heq⟩ := Array.mem_map.mp hg
  have hH : 16719420 ≤ g.pageH ∧ g.pageH ≤ 19505990 := heq ▸ hrange r hr
  -- The key inequality over bare `Int` binders, as `bodyTop_clears_head`
  -- does it: `omega` does not see through the `Sp` abbreviation.
  have key : ∀ a d f hb fb H : Int,
      a + d ≤ 2 * 720896 → f ≤ 2 * 720896 →
      16719420 ≤ H → H ≤ 19505990 →
      hb = max 0 (1730150 / 2 + (a + d) + 65536 - 1730150) →
      fb = max 0 (1730150 / 2 + f + 65536 - 1730150) →
      0 < H - 1730150 - fb - (1730150 + hb) ∧
      10 ≤ (H - 1730150 - fb - (1730150 + hb)) / 865075 ∧
      (H - 1730150 - fb - (1730150 + hb)) / 865075 ≤ 20 := by
    intro a d f hb fb H hh hf hlo hhi hhb hfb
    omega
  rw [hfs] at hh hf
  simp only [furnitureBand, furnEdge, Option.getD, hls, hv, hvm] at hhb hfb
  rw [hld]
  simp only [Geom.bodyBottom, Geom.bodyTop]
  rw [hv, hvm]
  exact key a d f g.headBand g.footBand g.pageH hh hf hH.1 hH.2 hhb hfb

/-- How a page distributes its leftover vertical space: declared shares of
the stretch above and below the content, the ratio form of beamer's
`\vfil`-glue model. Centring is 1:1, top-flush is 0:1 (all leftover
below), bottom-flush 1:0, and the moloch title page 2618:1000 — the sum
of its `0pt plus 1.618fil` and `\vfil` above against the `plus 1fil`
below (beamerinnerthememoloch.dtx, the "golden ratio spacing" of its
`title page` template). -/
structure VDist where
  above : Nat
  below : Nat
  deriving Repr, BEq, Inhabited

def VDist.top : VDist := ⟨0, 1⟩
def VDist.center : VDist := ⟨1, 1⟩
def VDist.bottom : VDist := ⟨1, 0⟩
def VDist.golden : VDist := ⟨2618, 1000⟩

/-- The shift of a line with `k` of its page's `n` fil units above it:
TeX's first-order infinite glue, as a share of the page's leftover.
`\vspace{\fill}` above and below the content is k=0 for nothing and k=1
of n=2 for every line — the centring sandwich; a leading fil alone pushes
everything down by the whole leftover (bottom-flush), a trailing fil
alone moves nothing. Content taller than the area (leftover ≤ 0) stays
put: it stays top-flush and spills below, never rides off the top of the
page. -/
def filShare (leftover : Sp) (k n : Nat) : Sp :=
  if leftover ≤ 0 then 0
  else if n = 0 then 0
  else leftover * k / n

/-- The fil split loses and invents nothing: a line's shift never leaves
`[0, leftover]` while its fil count stays within the page's, and a line
below another (more fils above it) never moves less — content order is
preserved. -/
theorem filShare_sound (l : Sp) (k k' n : Nat) (hk : k ≤ k') (hk' : k' ≤ n) :
    0 ≤ filShare l k n ∧ (0 ≤ l → filShare l k' n ≤ l) ∧
    filShare l k n ≤ filShare l k' n := by
  unfold filShare
  by_cases hl : l ≤ 0
  · simp [hl]
  · by_cases hn : n = 0
    · simp [hl, hn]
    · have hnn : (0 : Int) < (n : Int) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hl0 : (0 : Int) < l := Int.not_le.mp hl
      simp only [hl, hn, ite_false]
      refine ⟨?_, fun _ => ?_, ?_⟩
      · exact Int.ediv_nonneg (Int.mul_nonneg (by omega) (Int.natCast_nonneg _)) (by omega)
      · calc l * (k' : Int) / (n : Int)
            ≤ l * (n : Int) / (n : Int) :=
              Int.ediv_le_ediv hnn
                (Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hk') (by omega))
          _ = l := Int.mul_ediv_cancel l (by omega)
      · exact Int.ediv_le_ediv hnn
          (Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hk) (by omega))

/-- The share of a page's leftover placed above the content: the ratio
distribution IS the fil distribution — a ratio a:b is a of (a+b) fil
units above the content, division-by-zero convention included. -/
def VDist.aboveShare (d : VDist) (leftover : Sp) : Sp :=
  filShare leftover d.above (d.above + d.below)

/-- The split loses and invents nothing: the above share never leaves
`[0, leftover]` (`filShare_sound` at a of a+b fils), and the below share
is the exact difference — so both shares are non-negative and sum to
exactly the leftover, whatever the ratio and whatever rounding the
division did. -/
theorem VDist.split_exact (d : VDist) (l : Int) :
    0 ≤ d.aboveShare l ∧ (0 ≤ l → d.aboveShare l ≤ l) ∧
    d.aboveShare l + (l - d.aboveShare l) = l := by
  have h := filShare_sound l d.above d.above (d.above + d.below)
    (Nat.le_refl _) (Nat.le_add_right _ _)
  have hcancel : ∀ x y : Int, x + (y - x) = y := by omega
  exact ⟨h.1, h.2.1, hcancel _ _⟩

/-- Ratio 1:1 is the old vertical centring, division and guard included:
the generalisation moves no standout frame and no section page. -/
theorem VDist.center_is_halving (l : Sp) :
    VDist.center.aboveShare l = if l ≤ 0 then 0 else l / 2 := by
  unfold aboveShare filShare center
  split
  · rfl
  · simp

/-- "All leftover below" is the old top-flush behaviour: the article page
and every other undeclared page keep their lines exactly where they were. -/
theorem VDist.top_is_flush (l : Sp) : VDist.top.aboveShare l = 0 := by
  unfold aboveShare filShare top
  split
  · rfl
  · simp

/-- The distribution a frame's declaration names: a projection of the one
IR table (`Ir.VAlign.shares`), so the PDF page cannot drift from the HTML
deck's spacers. `golden` is the moloch title page's 2618:1000. -/
def VDist.of (v : Ir.VAlign) : VDist :=
  ⟨v.shares.1, v.shares.2⟩

inductive Item where
  | box (w : Sp) (fontIdx : Nat) (color : Ir.Color) (link : Option String)
      (glyphs : Array (Nat × Char × Sp)) (size : Sp) (underline : Bool) (raise : Sp)
      (ground : Option Ir.Color)
  | glue (g : Glue)
  | pen (w : Sp) (cost : Int) (flagged : Bool) (fontIdx : Nat) (color : Ir.Color)
      (glyphs : Array (Nat × Char × Sp))
  /-- An image: an unbreakable box `w` wide standing `h` above the baseline
  with no depth. `store` indexes the `Image.Store`; `none` (or an entry that
  did not load) is placed as a placeholder box of the same size. -/
  | img (store : Option Nat) (w : Sp) (h : Sp)
  /-- A horizontal rule in the stream — a fraction bar, a radical's
  overbar: `w` wide, `thickness` tall, its bottom at the baseline plus
  `raise`. Never a breakpoint, like any box. -/
  | rule (w : Sp) (thickness : Sp) (raise : Sp) (color : Ir.Color)
  deriving Repr, Inhabited

def forcedCost : Int := -10000

/-- plain TeX's `\hyphenpenalty=50` (TeXbook p.96): the cost of ending a
line at a hyphen, against the badness scale the breaker shares with TeX. -/
def hyphenPenalty : Int := 50

inductive Seg where
  /-- A glyph run. `width` is carried so link rectangles and alignment can be
  computed without re-measuring against the font. `raise` lifts the run's
  baseline above the line's (negative sinks it): a superscript is a raised
  run at script size. -/
  | run (fontIdx : Nat) (color : Ir.Color) (link : Option String) (width : Sp)
      (glyphs : Array (Nat × Char)) (size : Sp) (underline : Bool) (raise : Sp)
      (ground : Option Ir.Color)
  | gap (w : Sp)
  /-- A horizontal rule, `w` wide and `thickness` thick, on the baseline plus
  `raise`. The heading rule of a designed section, filling its line. -/
  | rule (w : Sp) (thickness : Sp) (raise : Sp) (color : Ir.Color)
  /-- An image box: its bottom on the baseline, `h` up from there. `store`
  indexes the `Image.Store` the backends were given; an entry that did not
  load renders as an outlined placeholder of the same size. -/
  | image (store : Option Nat) (w : Sp) (h : Sp)
  deriving Repr, Inhabited

structure LineOut where
  x : Sp
  y : Sp
  size : Sp
  segs : Array Seg
  setWidth : Sp
  /-- How far the line's first glyph deliberately hangs left of the
  measure — character protrusion's left overhang. `x` is the ink truth
  the backends paint at; `x + hang` is the measure edge, where the text
  block logically starts. -/
  hang : Sp := 0
  /-- The line's font-expansion factor in per-mille (`expandFactor`,
  within ±`expandLimit`): every run's width is already rescaled by it,
  and the PDF writer paints the line's glyphs under the same horizontal
  scale so ink and metrics agree. -/
  expand : Int := 0
  /-- Engine-placed running furniture — head, foot, chrome slots, the
  logo — laid into its reserved margin band by the furniture pass. Marked
  so a judge of the document's own ink (`Check.Shipped.ofOut`'s area
  walk) can tell the band's ink from the flow's: furniture stands in the
  margin by design, exactly where LaTeX's own page styles put it. -/
  furniture : Bool := false
  /-- A footnote line (or the footnote rule): body ink laid by the
  bottom-anchored flush in `finishPage`, above `Geom.bodyBottom`, never in
  the furniture band — marked so the census can tell the note apparatus
  from the flow structurally. -/
  note : Bool := false
  /-- A counted body line: a text line the paragraph pipeline laid in the
  galley, outside any float — what `\page{ linenumbers = on }`'s margin
  numbers attach to. The scope is lineno's own (lineno.sty, the
  introduction: "line numbers on paragraphs", attached by the output
  routine to the lines of every paragraph of the main text): paragraphs,
  headings, list items and display math are all galley paragraph lines
  here — display math is numbered like every line, where lineno's default
  linenomath does not (the recorded divergence,
  tests/compat-index/lineno.txt) — while a float's caption and body (a
  floated box, not galley lines), footnotes (insertions), bare rule ink,
  picture labels and furniture are not counted. -/
  counted : Bool := false
  /-- The preorder index of the `Struct.leaves (Struct.ofDoc (pdfView doc))`
  entry whose text this line paints — the first leaf of the block the line
  sets (a footnote's lines name the note's first leaf; a picture's label
  lines its picture leaf). `none` on furniture, rules-only lines, and
  generated ink the structure tree does not census (the abstract heading,
  the headline band). Decoration the walk adds to a block — a section
  number, a list marker, a caption prefix — rides the block's leaf; 18b's
  run channel names it apart. -/
  leaf : Option Nat := none
  deriving Repr, Inhabited

/-- A filled rectangle behind a page's text: the page background, a frame
title's colour bar, a progress bar. `x`/`y` are the top-left corner in
layout coordinates (y grows downward); the PDF writer paints fills before
the text, in order. -/
structure Fill where
  x : Sp
  y : Sp
  w : Sp
  h : Sp
  color : Ir.Color
  deriving Repr, Inhabited

/-- The eight printer's cut marks a page ships under `\page{ marks = cut }`:
a pure function of the trim box (`W × H`), the bleed, the gap, and the
thickness — derived, never placed by hand, so the drawn marks and the
declared TrimBox cannot drift apart. Each mark is a hairline inside the
bleed strip, anchored at a medium edge and running inward along a trim
line, stopping `gap` short of the trim line it approaches: the strip it
occupies is the strip the cutter discards. Coordinates are layout (trim)
space, y down — the medium spans `−bleed … W+bleed` — and the painted
thickness is `2·(thick/2)`: the odd sp (1/65536 pt, far below any press's
resolution) is dropped so the mark centres exactly on its trim line
(`cutmarks_on_trim_exact`) and the duplex flip maps marks onto marks
exactly (`cutmarks_symmetric_mem`). -/
def cutMarks (trimW trimH bleed gap thick : Sp) (color : Ir.Color) : Array Fill :=
  let hw := thick / 2
  let len := bleed - gap
  #[-- vertical, along the left and right trim lines, from the top and
    -- bottom medium edges
    ⟨-hw, -bleed, 2 * hw, len, color⟩,
    ⟨-hw, trimH + gap, 2 * hw, len, color⟩,
    ⟨trimW - hw, -bleed, 2 * hw, len, color⟩,
    ⟨trimW - hw, trimH + gap, 2 * hw, len, color⟩,
    -- horizontal, along the top and bottom trim lines, from the left and
    -- right medium edges
    ⟨-bleed, -hw, len, 2 * hw, color⟩,
    ⟨trimW + gap, -hw, len, 2 * hw, color⟩,
    ⟨-bleed, trimH - hw, len, 2 * hw, color⟩,
    ⟨trimW + gap, trimH - hw, len, 2 * hw, color⟩]

/-- The centre-line arithmetic behind `cutmarks_on_trim_exact`, over bare
`Int` binders: omega reads the bare spelling only, and the `Sp`-typed
mark components are silently invisible to it (the `furn_reserves`
pattern). -/
private theorem cutmarks_trim_arith (W H t : Int) :
    2 * -(t / 2) + 2 * (t / 2) = 0 ∧
    2 * (W - t / 2) + 2 * (t / 2) = 2 * W ∧
    2 * (H - t / 2) + 2 * (t / 2) = 2 * H := by omega

/-- Each mark's centre line lies exactly on a trim line — the card
source's own argument made a theorem: positions derive from the same
lengths as the page boxes, so the drawn marks and the declared TrimBox
cannot drift apart. Spelled doubled (`2x + w = 2·trim`) so the statement
needs no division and no parity hypothesis. -/
theorem cutmarks_on_trim_exact (W H b g t : Int) (c : Ir.Color) :
    ∀ f ∈ cutMarks W H b g t c,
      2 * f.x + f.w = 0 ∨ 2 * f.x + f.w = 2 * W ∨
      2 * f.y + f.h = 0 ∨ 2 * f.y + f.h = 2 * H := by
  intro f hf
  have h := cutmarks_trim_arith W H t
  simp only [cutMarks, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl h.1
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.2.1)
  · exact Or.inr (Or.inl h.2.1)
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inr (Or.inr h.2.2))
  · exact Or.inr (Or.inr (Or.inr h.2.2))

/-- The bounds behind `cutmarks_in_bleed_covers`, over bare `Int`
binders, one pack per mark: its four medium bounds and its trim
disjointness fact. -/
private theorem cutmarks_bleed_arith (W H b g t : Int)
    (hW : 0 ≤ W) (hH : 0 ≤ H) (hg : 0 ≤ g) (hgb : g ≤ b) (htg : t ≤ 2 * g) :
    ((-b ≤ -(t / 2) ∧ -(t / 2) + 2 * (t / 2) ≤ W + b ∧
      -b ≤ -b ∧ -b + (b - g) ≤ H + b) ∧ -b + (b - g) ≤ 0) ∧
    ((-b ≤ -(t / 2) ∧ -(t / 2) + 2 * (t / 2) ≤ W + b ∧
      -b ≤ H + g ∧ H + g + (b - g) ≤ H + b) ∧ H ≤ H + g) ∧
    ((-b ≤ W - t / 2 ∧ W - t / 2 + 2 * (t / 2) ≤ W + b ∧
      -b ≤ -b ∧ -b + (b - g) ≤ H + b) ∧ -b + (b - g) ≤ 0) ∧
    ((-b ≤ W - t / 2 ∧ W - t / 2 + 2 * (t / 2) ≤ W + b ∧
      -b ≤ H + g ∧ H + g + (b - g) ≤ H + b) ∧ H ≤ H + g) ∧
    ((-b ≤ -b ∧ -b + (b - g) ≤ W + b ∧
      -b ≤ -(t / 2) ∧ -(t / 2) + 2 * (t / 2) ≤ H + b) ∧ -b + (b - g) ≤ 0) ∧
    ((-b ≤ W + g ∧ W + g + (b - g) ≤ W + b ∧
      -b ≤ -(t / 2) ∧ -(t / 2) + 2 * (t / 2) ≤ H + b) ∧ W ≤ W + g) ∧
    ((-b ≤ -b ∧ -b + (b - g) ≤ W + b ∧
      -b ≤ H - t / 2 ∧ H - t / 2 + 2 * (t / 2) ≤ H + b) ∧ -b + (b - g) ≤ 0) ∧
    ((-b ≤ W + g ∧ W + g + (b - g) ≤ W + b ∧
      -b ≤ H - t / 2 ∧ H - t / 2 + 2 * (t / 2) ≤ H + b) ∧ W ≤ W + g) := by
  omega

/-- The bleed strip covers every mark: no mark ink inside the TrimBox and
none outside the MediaBox — the marks live entirely in the strip the
cutter discards. The hypotheses are the geometry that makes marks
drawable at all: a gap inside the bleed, and a hairline no wider than
twice the gap (so a mark cannot reach the trim corner either). -/
theorem cutmarks_in_bleed_covers (W H b g t : Int) (c : Ir.Color)
    (hW : 0 ≤ W) (hH : 0 ≤ H) (hg : 0 ≤ g) (hgb : g ≤ b) (htg : t ≤ 2 * g) :
    ∀ f ∈ cutMarks W H b g t c,
      (-b ≤ f.x ∧ f.x + f.w ≤ W + b ∧ -b ≤ f.y ∧ f.y + f.h ≤ H + b) ∧
      (f.x + f.w ≤ 0 ∨ W ≤ f.x ∨ f.y + f.h ≤ 0 ∨ H ≤ f.y) := by
  intro f hf
  have h := cutmarks_bleed_arith W H b g t hW hH hg hgb htg
  simp only [cutMarks, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨h.1.1, Or.inr (Or.inr (Or.inl h.1.2))⟩
  · exact ⟨h.2.1.1, Or.inr (Or.inr (Or.inr h.2.1.2))⟩
  · exact ⟨h.2.2.1.1, Or.inr (Or.inr (Or.inl h.2.2.1.2))⟩
  · exact ⟨h.2.2.2.1.1, Or.inr (Or.inr (Or.inr h.2.2.2.1.2))⟩
  · exact ⟨h.2.2.2.2.1.1, Or.inl h.2.2.2.2.1.2⟩
  · exact ⟨h.2.2.2.2.2.1.1, Or.inr (Or.inl h.2.2.2.2.2.1.2)⟩
  · exact ⟨h.2.2.2.2.2.2.1.1, Or.inl h.2.2.2.2.2.2.1.2⟩
  · exact ⟨h.2.2.2.2.2.2.2.1, Or.inr (Or.inl h.2.2.2.2.2.2.2.2)⟩

/-- The flip arithmetic behind `cutmarks_symmetric_mem`, over bare `Int`
binders with the half-thickness as one atom: omega reads the bare
spelling only (the `furn_reserves` pattern). -/
private theorem cutmarks_flip_arith (W b g d : Int) :
    W - d = W - -d - 2 * d ∧ -d = W - (W - d) - 2 * d ∧
    W + g = W - -b - (b - g) ∧ -b = W - (W + g) - (b - g) := by
  omega

/-- The duplex fact: under the horizontal flip `x ↦ W − x` the mark set
maps onto itself — for every mark, some mark stands exactly at its
flipped rectangle — so the sheet turned for its back face lands marks on
marks and the two faces cut as one. -/
theorem cutmarks_symmetric_mem (W H b g t : Int) (c : Ir.Color) :
    ∀ f ∈ cutMarks W H b g t c,
      ∃ f' ∈ cutMarks W H b g t c,
        f'.x = W - f.x - f.w ∧ f'.y = f.y ∧ f'.w = f.w ∧ f'.h = f.h := by
  intro f hf
  have h := cutmarks_flip_arith W b g (t / 2)
  simp only [cutMarks, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at hf
  simp only [cutMarks]
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_toArray.mpr (.tail _ (.tail _ (.head _))),
      h.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr (.tail _ (.tail _ (.tail _ (.head _)))),
      h.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr (.head _), h.2.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr (.tail _ (.head _)), h.2.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))),
      h.2.2.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr
      (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))),
      h.2.2.2, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))),
      h.2.2.1, rfl, rfl, rfl⟩
  · exact ⟨_, List.mem_toArray.mpr
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))),
      h.2.2.2, rfl, rfl, rfl⟩

/-- A path on the page, in layout coordinates (y down): what a picture's
node outlines — and, as the subset grows, its edges — become. The
placement transform is affine (translate + y flip), so a circle stays a
circle and an axis-aligned rectangle a rectangle; the PDF writer turns
the circle into its Bézier arcs, SVG keeps it native. -/
inductive PagePath where
  /-- A circle: centre and radius. -/
  | circle (cx cy r : Sp)
  /-- An axis-aligned rectangle: top-left corner and non-negative extents. -/
  | rect (x y w h : Sp)
  /-- An edge's segments, endpoints already in page coordinates. -/
  | segs (segs : Array Ir.Pic.PathSeg)
  /-- A filled triangle: an arrow tip. -/
  | tri (x1 y1 x2 y2 x3 y3 : Sp)
  deriving Repr, Inhabited

/-- A placed path with its declared paint: stroke and/or fill, exactly as
the picture shape carried them. -/
structure PathOut where
  path : PagePath
  stroke : Option Ir.Pic.Stroke := none
  fill : Option Ir.Color := none
  deriving Repr, Inhabited

structure PageOut where
  lines : Array LineOut := #[]
  fills : Array Fill := #[]
  /-- Picture paths, painted after the fills and before the text, so a
  node's own fill sits under its label. -/
  paths : Array PathOut := #[]
  /-- The chrome footer this page carries, resolved at collection time (the
  frame's own number, the section in force): the band of slots the final
  pass lays into the margin once the page count is known. `none` on section
  pages, standout frames, and every page of an unthemed document. -/
  foot : Option (Array Ir.BandSlot) := none
  /-- The countable frame this page belongs to — its `Ir.frameNumbers`
  number, written at `finishPage` from the same `.foot` op that carries
  the footer, so a stepped or spilling frame's pages all bear it. `none`
  on section pages, the title page, standout frames, and every page of a
  flow-class document: the page→frame attribution the partition statement
  `pages_partition_frames` (Obligations) ranges over. -/
  frame : Option Nat := none
  /-- The bottom edge of this page's page-top chrome bar (`.titleBar`),
  when one painted: the extent the furniture pass lays the headline
  band's corner logos into. -/
  band : Option Sp := none
  deriving Repr, Inhabited

/-- One entry of the PDF document outline (ISO 32000-2 §12.3.3): a link of
an unpinned navigation landmark. An in-document target that resolved
carries the 0-based index of the page holding its section heading; an
external target carries its URL; a target that resolved to neither is a
bare entry (legal: an outline item need carry no destination). -/
structure OutlineEntry where
  title : String
  page : Option Nat := none
  url : Option String := none
  deriving Repr, BEq, Inhabited

structure Out where
  pages : Array PageOut
  diags : Array Diag
  /-- The document outline: one entry per unpinned-nav link, in document
  order; empty when the document declares no unpinned nav. -/
  outline : Array OutlineEntry := #[]

-- Flattening: inlines → word/space/break tokens ------------------------------

/-- A resolved text style: which family slot, and the bold/italic bits. -/
structure TextStyle where
  slot : Nat := 0
  /-- The weight axis in force (`Ir.Weight`): `\fontseries`'s series, with
  `\textbf` selecting `.b` and `\textmd` `.m` — `bold : Bool` grown into
  the axis. The face a run sets in is
  `FontSet.lookup (slot, weight.css, italic)`. -/
  weight : Ir.Weight := .m
  italic : Bool := false
  color : Ir.Color := Ir.Color.black
  /-- Destination of the enclosing `\href`, if any. -/
  link : Option String := none
  /-- Size relative to the surrounding text, per mille. Absolute rather than
  compounding, as in LaTeX: `\large\Large` is Large, not the product. -/
  scale : Nat := 1000
  /-- Set as small caps. Applies to the word, not the face: see
  `smallCapSynth`. -/
  smallcaps : Bool := false
  /-- Under a drawn underline; the run carries it into the set line. -/
  underline : Bool := false
  /-- A language switch in force (`Style.lang`), a BCP 47 tag; `none` is
  the document's main language. Hyphenation patterns select through it
  (`patsOf`), the one reader today. -/
  lang : Option String := none
  /-- The surface this run's ink stands on, declared where the walk
  resolves it — the palette epoch's `bg`, the frame-title bar, a titled
  block's bar, the standout inversion; `none` is the undeclared page,
  paper the engine paints no fill for. Carried through `Item.box` onto
  `Seg.run`, so the pair the contrast judge owes completeness over is
  declared, never recovered geometrically. -/
  ground : Option Ir.Color := none
  deriving Repr, BEq, Inhabited

private inductive Tk where
  | word (style : TextStyle) (chars : Array Char)
  | space (style : TextStyle)
  | fill
  /-- A strut: zero width, this much height above the baseline. -/
  | strut (height : SymGlue)
  | brk (extra : SymGlue)
  /-- An image reference, resolved against the store when items are built. -/
  | img (src : String) (spec : Image.SizeSpec)
  /-- An elaborated formula, measured against the math face by
  `itemsOfInlines`: one unbreakable run of boxes and kerns. -/
  | formula (display : Bool) (style : TextStyle) (body : Math.MList)
  /-- An icon: one scalar whose face is whichever the per-scalar fallback
  chain covers it with — an icon face is chosen by coverage, so landing on
  a fallback face is the declared path, not a degradation, and earns no
  W0009. A scalar no face covers is the ordinary coverage loss (E0405). -/
  | icon (style : TextStyle) (c : Char)
  /-- A footnote mark with the note body it owes: the mark sets as a raised
  run at the scriptsize step (`Ir.markRaise` holds the raise); the body is
  staged as its own pre-broken note block whose page is the mark's. -/
  | note (num : Nat) (style : TextStyle) (body : Array Ir.Inline)
  deriving Repr

private structure FlattenSt where
  toks : Array Tk := #[]
  warnedMath : Bool := false
  diags : Array Diag := #[]
  /-- The size ladder named runs resolve through (`Geom.scale`). -/
  ladder : List (String × Nat) := Ir.sizeScale

private def warn (st : FlattenSt) (code : DiagCode) (msg : String)
    (help : Option String := none) : FlattenSt :=
  { st with diags := st.diags.push (Diag.of code msg (help := help)) }

/-- Small caps at synthesis size, relative to the surrounding text. The
fallback for a face that ships no `smcp`+`c2sc` (`Font.smallCaps`): letters
take their capital form set smaller. Real small caps are drawn, not scaled,
so this is a stand-in ratio until the face itself can answer. The 800‰ is
the fontinst fake-caps tradition — it also covers the stroke-weight loss a
bare x-height match would worsen. -/
def smallCapScale : Nat := 800

/-- The scalar core of the per-face synthesis scale, over (x-height, cap
height) in font units: the tradition's 800‰, lifted exactly where it would
drop small caps *below* the lowercase x — Bringhurst, Elements §3.2.2:
small caps sit at the x-height or slightly taller — and never above full
capitals. `smallcap_height_between` is its band. -/
def smallCapScaleCore (x c : Nat) : Nat :=
  min 1000 (max smallCapScale (x * 1000 / c))

/-- The per-face synthesis scale: `smallCapScaleCore` over the face's
measured x-height (`Font.xHeightOptical` — OS/2 sxHeight lies in some
fonts, the trust order the math size match already uses) and its declared
cap height. -/
def smallCapScaleFor (f : Font) : Nat :=
  smallCapScaleCore f.xHeightOptical f.capHeight.toNat

/-- `smallcap_height_between`, in scale space: the synthesis scale is at
least the face's x/cap ratio in mille (floored — so the synthesized cap
height reaches the lowercase x within one division quantum), at least the
800‰ tradition, and at most full capitals. Multiplying through by the cap
height reads: x-height ≲ synthesized cap height ≤ cap height, the honest
band — equality with the x-height only when x/cap ≥ 0.8, so the band is
the statement, not an `_eq`. -/
theorem smallcap_height_between (x c : Nat) (hc : 0 < c) (hx : x ≤ c) :
    x * 1000 / c ≤ smallCapScaleCore x c ∧
      smallCapScale ≤ smallCapScaleCore x c ∧ smallCapScaleCore x c ≤ 1000 := by
  have h1 : x * 1000 ≤ c * 1000 := Nat.mul_le_mul_right 1000 hx
  have hq : x * 1000 / c ≤ 1000 := by
    have h2 : x * 1000 / c ≤ c * 1000 / c := Nat.div_le_div_right h1
    rwa [Nat.mul_div_cancel_left 1000 hc] at h2
  unfold smallCapScaleCore smallCapScale
  omega

/-- The synthesised uniform small-caps form of one word: every letter its
capital form, the whole word at the face's own scale
(`smallCapScaleFor`) — one style, one size, so mixed case cannot come out
at two heights. The invariant whose absence was the defect: the old
synthesis kept capitals full-size beside their scaled neighbours, and
`{\scshape PhD}` set a full P and D against a small H.
Chosen only when the face carries no real small caps (`Font.smallCaps`);
`\scshape` means uniform small capitals in both mechanisms (the PLAN
2026-09-18 entry carries the decision). -/
def smallCapSynth (scale : Nat) (sty : TextStyle) (chars : Array Char) :
    TextStyle × Array Char :=
  ({ sty with scale := sty.scale * scale / 1000 }, chars.map (·.toUpper))

private def pushWord (st : FlattenSt) (sty : TextStyle) (cur : Array Char) : FlattenSt :=
  { st with toks := st.toks.push (.word sty cur) }

private def pushText (st : FlattenSt) (sty : TextStyle) (s : String) : FlattenSt := Id.run do
  let mut st := st
  let mut cur : Array Char := #[]
  for c in s.toList do
    if c == ' ' then
      if !cur.isEmpty then
        st := pushWord st sty cur
        cur := #[]
      st := { st with toks := st.toks.push (.space sty) }
    else
      cur := cur.push c
  if !cur.isEmpty then
    st := pushWord st sty cur
  return st

/-- Apply one markup style to the active text style. Size-only styles do not
change the face; `\normalfont` resets to the body face. -/
private def applyStyle (ladder : List (String × Nat)) (sty : TextStyle) :
    Ir.Style → TextStyle
  | .bold => { sty with weight := .b }
  | .italic => { sty with italic := true }
  | .emph => { sty with italic := !sty.italic }
  | .mono => { sty with slot := 2 }
  | .sans => { sty with slot := 1 }
  | .smallcaps => { sty with smallcaps := true }
  | .roman => { sty with slot := 0 }
  | .medium => { sty with weight := .m }
  | .series w => { sty with weight := w }
  -- NFSS shapes are exclusive (fntguide §2.2): upright clears both.
  | .upright => { sty with italic := false, smallcaps := false }
  | .normal => {}
  | .lang tag => { sty with lang := some tag }
  | .size n => match ladder.lookup n with
    | some k => { sty with scale := k }
    | none => sty

/-- `weight_agree`: the weight a style leaves in force is exactly
`Ir.Style.weight?` — the one projection the HTML emission also reads —
so the face a run selects is one function of `(slot, weight, italic)`
in both backends: the PDF resolves it through `FontSet.lookup`, the
HTML emits `weight.css` and ships each face under its own
`font-weight` (`html_fonts_cover_pdf` carries the coverage half). -/
theorem weight_agree (ladder : List (String × Nat)) (sty : TextStyle)
    (s : Ir.Style) :
    (applyStyle ladder sty s).weight = (s.weight?).getD sty.weight := by
  cases s <;> simp [applyStyle, Ir.Style.weight?]
  case size n => cases ladder.lookup n <;> simp

mutual

private def flatten (mathOk noteOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (xs : Array Inline) : FlattenSt :=
  flattenList mathOk noteOk st sty xs.toList

private def flattenList (mathOk noteOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (xs : List Inline) : FlattenSt :=
  match xs with
  | [] => st
  | x :: rest => flattenList mathOk noteOk (flattenOne mathOk noteOk st sty x) sty rest

private def flattenOne (mathOk noteOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (x : Inline) : FlattenSt :=
  match x with
  | .text s => pushText st sty s
  -- an anchor ships no ink; a resolved reference ships its number
  | .label _ => st
  | .ref _ _ text _ => pushText st sty text
  -- An unresolved citation sets its marks as plain text: something stands
  -- here, and the diagnostic that let it through has already said why.
  | .cite _ keys => pushText st sty (Ir.citeMarks keys)
  -- The mark rides as its own token when the context has a note apparatus
  -- (a paragraph of a paged flow); where none exists — furniture, markers,
  -- captions, a card face — the body stays inline, the declared refusal.
  | .footnote num body =>
    if noteOk then { st with toks := st.toks.push (.note (num.getD 0) sty body) }
    else flatten mathOk noteOk st sty body
  | .icon c _ => { st with toks := st.toks.push (.icon sty c) }
  | .image src spec _ => { st with toks := st.toks.push (.img src spec) }
  | .linebreak extra => { st with toks := st.toks.push (.brk extra) }
  | .fill => { st with toks := st.toks.push .fill }
  | .strut h => { st with toks := st.toks.push (.strut h) }
  -- Math carried as source (the constructs M6 still owes): the elaborator
  -- warned by name; here the source sets as plain text, so nothing drops.
  | .math _ src => pushText st sty src
  | .formula display src body =>
    if mathOk then
      { st with toks := st.toks.push (.formula display sty body) }
    else
      let st := if st.warnedMath then st
        else { warn st .W0003 "no math font is available; math is set as plain text"
                 (some "declare \\fonts{ math = \"...\" } naming an installed \
OpenType math face; `leantex fonts` lists families") with warnedMath := true }
      pushText st sty src
  | .styled s body => flatten mathOk noteOk st (applyStyle st.ladder sty s) body
  | .colored c _ body => flatten mathOk noteOk st { sty with color := c } body
  -- A role is a name, pure grouping: zero metric impact, no style change
  -- (role_transparent_layout is the statement).
  | .role _ body => flatten mathOk noteOk st sty body
  -- The underline is the link's affordance in both backends (the HTML
  -- anchor keeps the browser's): never colour alone, and never nothing
  -- (WCAG 2.2 SC 1.4.1, use of colour).
  | .link url body => flatten mathOk noteOk st { sty with link := some url, underline := true } body
  | .underline body => flatten mathOk noteOk st { sty with underline := true } body
  -- A step is pure grouping here: the PDF path dims pending content by
  -- recolouring copies before layout (`run`'s step driver), never by metrics.
  | .step _ _ body => flatten mathOk noteOk st sty body
  -- Placeholders are substituted before layout; reaching here means the
  -- document used one outside running content.
  | .pageNumber => pushText st sty "?"
  | .pageCount => pushText st sty "?"

end

/-- A role is transparent to layout: the flatten walk recurses into the
body with the state and the style unchanged, so wrapping content in a role
moves no ink and no metric — the `.step` property, and the reason the PDF
page is byte-identical with and without the annotation. The block half is
`collectRole_transparent`, over the collector's own arm. -/
theorem role_transparent_layout (mathOk noteOk : Bool) (st : FlattenSt)
    (sty : TextStyle) (n : String) (body : Array Inline) :
    flattenOne mathOk noteOk st sty (.role n body)
      = flatten mathOk noteOk st sty body := by
  simp [flattenOne]

-- Items -----------------------------------------------------------------------

private def scaledAt (size : Sp) (font : Font) (units : Nat) : Sp :=
  (units * size.toNat) / font.unitsPerEm

private def glyphOf (size : Sp) (font : Font) (c : Char) : Option (Nat × Char × Sp) :=
  match font.gid c with
  | some g => some (g, c, scaledAt size font (font.widths[g]?.getD 0))
  | none => none

/-- `glyphOf`, through the face's own small-caps substitution when the run
is small caps: the substituted glyph carries its own advance, and the char
stays as typed — the artifact's text is the author's casing, only the drawn
form changes. A face that maps a gid nowhere keeps it (digits, punctuation). -/
private def glyphOfSc (smallcaps : Bool) (size : Sp) (font : Font) (c : Char) :
    Option (Nat × Char × Sp) :=
  (font.gid c).map fun g0 =>
    let g := if smallcaps then font.smallCapGid g0 else g0
    (g, c, scaledAt size font (font.widths[g]?.getD 0))

def hyphenGlyph (size : Sp) (font : Font) : Array (Nat × Char × Sp) :=
  match glyphOf size font '-' with
  | some g => #[g]
  | none => #[]

/-- The width a box's glyphs carry: what the KP breaker measures. -/
def boxWidth (box : Array (Nat × Char × Sp)) : Sp :=
  box.foldl (fun w g => w + g.2.2) 0

theorem boxWidth_push (xs : Array (Nat × Char × Sp)) (a : Nat × Char × Sp) :
    boxWidth (xs.push a) = boxWidth xs + a.2.2 := by
  unfold boxWidth
  rw [Array.foldl_push]

/-- The scaled pair kern the next glyph owes against the box's last: 0
at a box head, and 0 for every pair of a face with no kern data (Open
Sans ships none). Both backends read one `Ir.Features` value for whether
kerning applies at all — `features_agree` by construction, `font-kerning`
in CSS and this application being two projections of it. -/
def kernVal (kern : Bool) (size : Sp) (font : Font)
    (box : Array (Nat × Char × Sp)) (g1 : Nat) : Sp :=
  match box.back? with
  | some (pg, _, _) =>
    (if kern then font.kernAdv pg g1 else 0) * size / (font.unitsPerEm : Int)
  | none => 0

/-- Apply a pair kern to the box's last glyph's advance: the pen position
of everything after it — the next glyph first — moves by exactly the
declared value, which is what kerning is. -/
def kernApply (box : Array (Nat × Char × Sp)) (ks : Sp) : Array (Nat × Char × Sp) :=
  match box.back? with
  | some (pg, pc, padv) => box.pop.push (pg, pc, padv + ks)
  | none => box

private theorem back?_pop_push {α : Type} (xs : Array α) (a : α)
    (h : xs.back? = some a) : xs = xs.pop.push a := by
  unfold Array.back? at h
  apply Array.toList_inj.mp
  simp only [Array.toList_push, Array.toList_pop]
  have hg : xs.toList.getLast? = some a := by
    rw [List.getLast?_eq_getElem?]
    simpa using h
  have hne : xs.toList ≠ [] := by rintro h0; simp [h0] at hg
  rw [List.getLast?_eq_some_getLast hne] at hg
  have := List.dropLast_concat_getLast hne
  rw [Option.some_inj.mp hg] at this
  exact this.symm

/-- kern_symmetric_in_measure: setting the next glyph after a kern moves
the box width by exactly the glyph's advance plus the applied pair value,
and nothing else — the KP breaker's widths stay the exact sum of what
the box carries, GPOS application included. -/
theorem kern_symmetric_in_measure (box : Array (Nat × Char × Sp))
    (ks : Sp) (g : Nat × Char × Sp) (h : box.back?.isSome) :
    boxWidth ((kernApply box ks).push g) = boxWidth box + ks + g.2.2 := by
  cases hb : box.back? with
  | none => simp [hb] at h
  | some p =>
    obtain ⟨pg, pc, padv⟩ := p
    have hbox := back?_pop_push box _ hb
    have hw : boxWidth box = boxWidth box.pop + padv := by
      rw [hbox]
      simp [boxWidth, Array.pop_push]
    rw [show kernApply box ks = box.pop.push (pg, pc, padv + ks) by
      unfold kernApply
      rw [hb]]
    rw [boxWidth_push, boxWidth_push, hw]
    change boxWidth box.pop + (padv + ks) + g.2.2
      = boxWidth box.pop + padv + ks + g.2.2
    rw [Int.add_assoc (boxWidth box.pop) padv ks]

/-- At a box head there is nothing to kern against: the applied value is
0 by definition, so the width moves by the glyph's advance alone. -/
theorem kernVal_head (kern : Bool) (size : Sp) (font : Font) (g1 : Nat)
    (box : Array (Nat × Char × Sp)) (h : box.back? = none) :
    kernVal kern size font box g1 = 0 := by
  unfold kernVal
  rw [h]

/-- Fixed-width spaces, as a fraction of the em. These are kerns, not
characters: a Type 1-derived face has no glyph at U+2009, so looking one up
drops the space that `\,` asked for. `\!`-style negative kerns are not here
because there is no Unicode character for them. -/
def fixedSpace (c : Char) : Option (Nat × Nat) :=
  if c == '\u2009' then some (1, 6)        -- thin space, TeX's \,
  else if c == '\u202F' then some (1, 6)   -- narrow no-break: siunitx's \, between number and unit
  else if c == '\u2005' then some (1, 4)   -- four-per-em, \:
  else if c == '\u2004' then some (1, 3)   -- three-per-em, \;
  else if c == '\u2007' then some (1, 2)   -- figure space
  else if c == '\u2003' then some (1, 1)   -- em quad: \paragraph's run-in gap
  else none

/-- One word → items: boxes split by hyphenation points (flagged penalties
carrying the hyphen glyph) and by explicit hyphens (unflagged, no glyph).
A scalar the styled face lacks is set from the precomputed fallback face
(`FontSet.fallback`) at the same size — its own one-glyph box, since a box
carries one face — or dropped when no face covers it. `missing` and `substs`
carry `(styled font, scalar)` so the diagnostic can name the family.
`smallcaps` routes every glyph lookup — styled face and fallback alike —
through that face's own `smcp`+`c2sc` substitution (`glyphOfSc`); it is set
only when the styled face has one, synthesis having already rewritten the
word otherwise. -/
private def wordItems (pats : Option Hyphen.Patterns) (langKey : String)
    (size : Sp) (fontIdx : Nat)
    (color : Ir.Color) (ground : Option Ir.Color) (link : Option String)
    (underline : Bool) (smallcaps : Bool)
    (fs : FontSet) (font : Font) (chars : Array Char) (missing : Array (Nat × Char))
    (substs : Array (Nat × Char × Nat)) (cache : Std.HashMap String (Array Nat)) :
    Array Item × Array (Nat × Char) × Array (Nat × Char × Nat) ×
      Std.HashMap String (Array Nat) := Id.run do
  let mut missing := missing
  let mut substs := substs
  let mut cache := cache
  let hyphW := (hyphenGlyph size font).foldl (fun w (_, _, adv) => w + adv) 0
  let mut items : Array Item := #[]
  let mut box : Array (Nat × Char × Sp) := #[]
  let mut boxW : Sp := 0
  let flush (items : Array Item) (box : Array (Nat × Char × Sp)) (w : Sp) : Array Item :=
    if box.isEmpty then items else items.push (.box w fontIdx color link box size underline 0 ground)
  let mut i := 0
  for _ in [0:chars.size + 1] do
    if h : i < chars.size then
      let c := chars[i]
      if Nfc.isLetter c then
        let mut j := i
        let mut run : Array Char := #[]
        for _ in [i:chars.size] do
          if h' : j < chars.size then
            if Nfc.isLetter chars[j] then
              run := run.push chars[j]
              j := j + 1
            else
              break
          else
            break
        let word := String.ofList run.toList
        -- The cache key carries the language: one paragraph can mix
        -- tagged runs, and a French word's breaks must never answer for
        -- the same spelling under English (a letter run never contains
        -- ':', so the key is unambiguous).
        let key := langKey ++ ":" ++ word
        let mut breaks : Array Nat := #[]
        match pats with
        | some p =>
          match cache[key]? with
          | some b => breaks := b
          | none =>
            let b := Hyphen.hyphenate p word
            cache := cache.insert key b
            breaks := b
        | none => pure ()
        for (c', k) in run.zipIdx do
          if breaks.contains k then
            items := flush items box boxW
            box := #[]
            boxW := 0
            items := items.push
              (.pen hyphW hyphenPenalty true fontIdx color (hyphenGlyph size font))
          match glyphOfSc smallcaps size font c' with
          | some g =>
            let ks := kernVal Ir.features.kern size font box g.1
            box := (kernApply box ks).push g
            boxW := boxW + ks + g.2.2
          | none =>
            match fs.fallbackFor c' |>.bind fun fb =>
                (glyphOfSc smallcaps size (fs.get fb) c').map (fb, ·) with
            | some (fb, g) =>
              items := flush items box boxW
              box := #[]
              boxW := 0
              items := items.push (.box g.2.2 fb color link #[g] size underline 0 ground)
              unless substs.any (fun e => e.1 == fontIdx && e.2.1 == c') do
                substs := substs.push (fontIdx, c', fb)
            | none =>
              unless missing.contains (fontIdx, c') do
                missing := missing.push (fontIdx, c')
        i := j
      else
        match fixedSpace c with
        | some (num, den) =>
          -- A kern: width but no glyph, and never a breakpoint, so `\,` cannot
          -- become a place to end a line.
          items := flush items box boxW
          box := #[]
          boxW := 0
          items := items.push (.box (size * num / den) fontIdx color link #[] size underline 0 ground)
          i := i + 1
        | none =>
        if c == '\u00a0' then
          -- A no-break space is an interword space that is not glue.
          items := flush items box boxW
          box := #[]
          boxW := 0
          items := items.push
            (.box (scaledAt size font font.spaceAdvance) fontIdx color link #[] size underline 0 ground)
          i := i + 1
        else
        match glyphOfSc smallcaps size font c with
        | some g =>
          let ks := kernVal Ir.features.kern size font box g.1
          box := (kernApply box ks).push g
          boxW := boxW + ks + g.2.2
        | none =>
          match fs.fallbackFor c |>.bind fun fb =>
              (glyphOfSc smallcaps size (fs.get fb) c).map (fb, ·) with
          | some (fb, g) =>
            items := flush items box boxW
            box := #[]
            boxW := 0
            items := items.push (.box g.2.2 fb color link #[g] size underline 0 ground)
            unless substs.any (fun e => e.1 == fontIdx && e.2.1 == c) do
              substs := substs.push (fontIdx, c, fb)
          | none =>
            unless missing.contains (fontIdx, c) do
              missing := missing.push (fontIdx, c)
        i := i + 1
        if c == '-' then
          items := flush items box boxW
          box := #[]
          boxW := 0
          items := items.push (.pen 0 hyphenPenalty false fontIdx color #[])
    else
      break
  items := flush items box boxW
  return (items, missing, substs, cache)

/-- Interword glue: the face's space advance, stretching by half and
shrinking by a third. The proportions are TeX's plain-font fontdimens
(TeXbook Ch. 12) and exactly what LuaTeX synthesizes for an OpenType
face, which declares no fontdimens: `space_stretch = spaceunits/2`,
`space_shrink = spaceunits/3` under the default `syncspace`
(luatex-fonts-merged.lua, `constructors.scale`) — so a document set here
gets the same space rubber lualatex gives it. The advance itself comes
from `Font.spaceAdvance`, never zero even for a face with no space
glyph. -/
private def interword (size : Sp) (font : Font) : Glue :=
  let w := scaledAt size font font.spaceAdvance
  { width := w, stretch := w / 2, shrink := w / 3 }

/-- Ragged setting as an item transform, leaving the breaker untouched:
interword glue keeps its natural width, never shrinks, and gains *finite*
stretch — six times its own width, `displayItems`' em-relative pricing, so
the two ragged tiers share one scale. Finite is the point: fil hides all
looseness from the badness function (TeXbook ch. 14), so under fil glue
every same-line-count break sequence ties at demerits and the tie-break
decides the paragraph's shape — packing lines from the end and dumping the
slack on the first line. Plain TeX's `\raggedright` prices looseness
finitely for exactly this reason (TeXbook App. B, p. 356: `\rightskip 0pt
plus2em`, fixed `\spaceskip`); LaTeX's `1fil` `\@flushglue` version is the
documented wart ragged2e exists to fix (ragged2e manual §1, its
`\RaggedRightRightskip 0pt plus 2em`). The paragraph's closing parfill and
an author's own `\hfill` keep their fil: a body paragraph's last line is
free (`\parfillskip 0pt plus 1fil`), and a declared fill means the margin.
The lines are then set unjustified, so the stretch never widens a rendered
space — it only prices the break. -/
def raggedItems (items : Array Item) : Array Item :=
  items.map fun it =>
    match it with
    | .glue g =>
      if g.fil then it
      else .glue { width := g.width, stretch := g.width * 6 }
    | .box .. | .pen .. | .img .. | .rule .. => it

/-- Ragged setting for display lines — titles and headings: interword glue
keeps its natural width and gains *finite* stretch (six times its own
width, ≈1.5 em per space at TeX's quarter-em space, so it scales with the
styled size the glue was built at), and the closing parfill stretches by
half the measure — TeX's minimum-last-line idiom (`\parfillskip 0pt plus
.5\hsize`: a last line shorter than half the measure runs past the
parfill's stretch and its badness rises cubically) — so the breaker
balances the lines instead of packing every line but the last. A display
break never strands one word on a line: a title is not a paragraph. Fil
hides all looseness from the badness function; a finite stretch prices it
(TeXbook ch. 14 on ragged setting). An author's own `\hfill` keeps its
fil. Body ragged setting (`raggedItems`) shares the interword pricing but
keeps the parfill free: paragraphs are reading, not display, and a body
paragraph's last line owes no minimum. -/
def displayItems (target : Sp) (items : Array Item) : Array Item :=
  items.map fun it =>
    match it with
    | .glue g =>
      if g.fil && !g.parfill then it
      else if g.parfill then .glue { width := g.width,
                                     stretch := max 0 (target / 2),
                                     parfill := true }
      else .glue { width := g.width, stretch := g.width * 6 }
    | .box .. | .pen .. | .img .. | .rule .. => it

-- The document's scalars, for the driver's per-glyph fallback ------------------

/-- The scalars a run's leaves ask a face for beyond its plain text: the
Mathematical Alphanumeric code points elaboration mapped formula variables
to, and each icon's glyph (its plain text is its text alternative) — neither
lives in the plain text, so the census must walk the bodies themselves. One
`Ir.foldInlines` projection, both leaf kinds: `.icon` glyphs join `icons`,
formula scalars join `math`, so the two censuses cannot drift apart arm by
arm. An anchor ships no glyphs; a reference's number is plain text, which
`textAndMath` already carries through `plainText`; a note's body ships
glyphs like any inline content — the fold walks every wrapper. -/
private def leafScalars (icons math : Array Char) (xs : Array Ir.Inline) :
    Array Char × Array Char :=
  Ir.foldInlines (fun acc x =>
    match x with
    | .formula _ _ body => (acc.1, Math.MList.scalarsList acc.2 body)
    | .icon c _ => (acc.1.push c, acc.2)
    | _ => acc) (icons, math) xs

/-- The census accumulator: the plain texts a document's faces will be
asked for, and — separately — the scalars its formulas ask the math face
for, so the driver can both cover them (one fallback precompute) and know
whether the document reaches math at all. -/
private structure ScalarAcc where
  texts : Array String := #[]
  math : Array Char := #[]
  /-- The locale whose furniture words (the abstract heading) the census
  counts as shipped text. -/
  locale : Locale := Locale.en

/-- The plain text of a run and, when it carries formulas or icons, their
scalars: what keeps the per-scalar fallback one mechanism — a math or icon
scalar enters the same precompute a text scalar does. -/
private def textAndMath (out : ScalarAcc) (xs : Array Ir.Inline) : ScalarAcc :=
  let (icons, math) := leafScalars #[] out.math xs
  { out with
    texts := (out.texts.push (Ir.plainText xs)).push
      (String.ofList icons.toList)
    math }

mutual

private def scalarTextList (out : ScalarAcc) (itemD enumD : Nat) :
    List Block → ScalarAcc
  | [] => out
  | b :: rest => scalarTextList (scalarTextOne out itemD enumD b) itemD enumD rest

private def scalarTextOne (out : ScalarAcc) (itemD enumD : Nat) :
    Block → ScalarAcc
  | .para xs => textAndMath out xs
  -- the equation's number is set in the body face beside the formula
  | .equation num xs =>
    textAndMath { out with texts := out.texts.push num } xs
  -- A heading's number is set beside its title, so its digits are asked
  -- of the bold face like the title's own text.
  | .section _ _ num title =>
    textAndMath { out with texts := out.texts.push (num.getD "") } title
  -- Each entry's formatted content is shipped text: its scalars enter the
  -- same fallback precompute a paragraph's do.
  | .bibliography _ _ items =>
    items.foldl (fun out item => textAndMath out item.content) out
  | .list ordered items =>
    -- The level's default marker rides along, so the fallback face is
    -- found before layout asks for the glyph. Per-kind depth, as LaTeX
    -- counts it (`\@itemdepth`/`\@enumdepth`).
    let (itemD, enumD) := if ordered then (itemD, enumD + 1) else (itemD + 1, enumD)
    let level := min (if ordered then enumD else itemD) 4
    scalarTextItems { out with texts := out.texts.push (ListMark.scalars ordered level) } itemD enumD items.toList
  | .center body => scalarTextList out itemD enumD body.toList
  | .ragged body => scalarTextList out itemD enumD body.toList
  | .quote body => scalarTextList out itemD enumD body.toList
  -- The abstract's heading word is class furniture set in the bold face;
  -- its glyphs are asked for like any other text.
  | .abstract body =>
    scalarTextList { out with texts := out.texts.push out.locale.abstract } itemD enumD body.toList
  -- The block's title is set in the bold face at the body size; its
  -- glyphs are asked for like a heading's.
  | .titled _ title body => scalarTextList (textAndMath out title) itemD enumD body.toList
  | .role _ body => scalarTextList out itemD enumD body.toList
  | .spaced _ body => scalarTextList out itemD enumD body.toList
  | .columns cols => scalarTextCols out itemD enumD cols.toList
  | .step _ _ body => scalarTextList out itemD enumD body.toList
  | .only _ body => scalarTextList out itemD enumD body.toList
  | .nav _ body => scalarTextList out itemD enumD body.toList
  -- A note is never set in either backend's pages; its glyphs are not asked
  -- for.
  | .note _ => out
  | .logo content => textAndMath out content
  -- The listing word and the caption's digits are furniture set in the
  -- body face beside the declared caption text; line-number digits are
  -- furniture in the mono face. Each is asked of the faces here, before
  -- layout asks for the glyph.
  | .verbatim _ s spec =>
    let out := { out with texts := out.texts.push s }
    let out := if spec.numbers then
        { out with texts := out.texts.push "0123456789\u00a0" } else out
    match spec.caption with
    | some (n, cap) =>
      textAndMath { out with texts := out.texts.push s!"{out.locale.listing} {n}: " } cap
    | none => out
  -- A rule has no glyphs.
  | .rule _ _ _ => out
  -- A page boundary ships no ink.
  | .pagebreak => out
  -- A stateful design declaration ships no glyphs.
  | .setPalette _ => out
  | .setTokens _ => out
  -- A picture's labels are set as inline runs: their text and math
  -- scalars are asked of the faces like any other content.
  | .picture pic => pic.labelContents.foldl textAndMath out
  | .frame title _ _ body =>
    scalarTextList (textAndMath out title) itemD enumD body.toList
  -- A framefoot note is set on the page as footer text.
  | .framefoot content => textAndMath out content
  -- Every cell's text, and a caption's, reaches the scalar census: the
  -- fallback scan must see a glyph before layout asks a face for it.
  | .table _ _ _ rows _ => scalarTextTableRows out rows.toList
  -- The generated keyword words, the io/comment punctuation, and — when
  -- lines are numbered — the digits, plus each line's own content and
  -- comment: generated text must be covered exactly as caption prefixes.
  | .algorithm numbered _ lines =>
    let words := Ir.algWords out.locale.tag
    let texts := (out.texts ++ (Ir.AlgWords.all words).toArray).push ":; /**/"
    let texts := if numbered then texts.push "0123456789" else texts
    scalarTextAlgLines { out with texts := texts } lines.toList
  | .float _ _ _ body caption =>
    scalarTextList (textAndMath out caption) itemD enumD body.toList

private def scalarTextAlgLines (out : ScalarAcc) : List Ir.AlgLine → ScalarAcc
  | [] => out
  | l :: rest =>
    scalarTextAlgLines (match l.comment with
      | some c => textAndMath (textAndMath out l.content) c
      | none => textAndMath out l.content) rest

private def scalarTextTableRows (out : ScalarAcc) :
    List (Array (Array Inline)) → ScalarAcc
  | [] => out
  | row :: rest => scalarTextTableRows (scalarTextTableCells out row.toList) rest

private def scalarTextTableCells (out : ScalarAcc) :
    List (Array Inline) → ScalarAcc
  | [] => out
  | cell :: rest => scalarTextTableCells (textAndMath out cell) rest

private def scalarTextCols (out : ScalarAcc) (itemD enumD : Nat) :
    List (Option Nat × Array Block) → ScalarAcc
  | [] => out
  | (_, body) :: rest =>
    scalarTextCols (scalarTextList out itemD enumD body.toList) itemD enumD rest

private def scalarTextItems (out : ScalarAcc) (itemD enumD : Nat) :
    List (Array Block) → ScalarAcc
  | [] => out
  | bs :: rest =>
    scalarTextItems (scalarTextList out itemD enumD bs.toList) itemD enumD rest

end

/-- Every scalar the document's text can ask a face for, sorted: body text,
titles, verbatim, running content (with the digits page numbers become),
style templates and markers, and each list level's default marker — plus
each cased scalar's uppercase, because
small caps set lowercase as its uppercase. Whitespace and the fixed-space
kerns are excluded; they never look a glyph up. The driver checks these
against the loaded faces to precompute `FontSet.fallback` before layout
begins, which is what keeps layout pure: finding a covering face on disk is
the driver's effect, and by layout time it has already happened. -/
private def docScalarAcc (doc : Doc) : ScalarAcc := Id.run do
  let mut acc : ScalarAcc :=
    scalarTextList { locale := doc.info.locale } 0 0 doc.body.toList
  if let some h := doc.head then
    acc := textAndMath acc h |> fun a => { a with texts := a.texts.push "0123456789" }
  if let some f := doc.foot then
    acc := textAndMath acc f |> fun a => { a with texts := a.texts.push "0123456789" }
  else if doc.pageNumbersOn then
    -- The class-default plain foot ships digits nobody declared: the
    -- precompute must cover them exactly as it covers a declared
    -- `\pagenumber`'s.
    acc := { acc with texts := acc.texts.push "0123456789" }
  if doc.lineNumbersOn then
    -- Margin line numbers ship digits the same way: engine-generated
    -- text the fallback scan must cover before layout asks a face.
    acc := { acc with texts := acc.texts.push "0123456789" }
  if let some hl := doc.headline then
    -- The headline band is furniture from the `\title` family: its text
    -- must be covered exactly as the head's and foot's is.
    acc := textAndMath acc hl.title
    acc := textAndMath acc hl.author
    acc := textAndMath acc hl.institute
  for slot in [doc.logoLeft, doc.logoRight] do
    if let some content := slot then
      acc := textAndMath acc content
  for (_, st) in doc.styles.entries do
    if let some tpl := st.font then
      acc := { acc with texts := acc.texts.push (Ir.plainText tpl) }
    if let some m := st.marker then
      acc := { acc with texts := acc.texts.push (Ir.plainText m) }
  return acc

/-- The scalars the document's formulas ask the math face for: nonempty
exactly when resolving a math face is worth the driver's while, and what
the note that names an engine-picked face is gated on. -/
def docMathScalars (doc : Doc) : Array Char :=
  (docScalarAcc doc).math

def docScalars (doc : Doc) : Array Char := Id.run do
  let acc := docScalarAcc doc
  let texts := acc.texts.push (String.ofList acc.math.toList)
  -- ASCII in a bitmap, the rest gathered and deduplicated after: a hash
  -- insert per character of the document costs ~15 ms on the 30-page bench,
  -- a bitmap update costs nothing. Two folds, so each accumulator threads
  -- linearly and updates in place.
  let skip (c : Char) : Bool :=
    c == ' ' || c == '\n' || c == '\t' || c == '\u00a0' || (fixedSpace c).isSome
  let mut ascii : Array Bool := Array.replicate 128 false
  let mut rest : Array Char := #[]
  for t in texts do
    ascii := t.foldl (init := ascii) fun a c =>
      if c.toNat < 128 && !skip c then
        let a := a.set! c.toNat true
        if c.isLower then a.set! c.toUpper.toNat true else a
      else a
    rest := t.foldl (init := rest) fun a c =>
      if c.toNat >= 128 && !skip c then a.push c else a
  let mut set : Std.HashSet Char := {}
  for c in rest do
    set := set.insert c
  let mut out : Array Char := #[]
  for n in [0:128] do
    if ascii[n]! then
      out := out.push (Char.ofNat n)
  return out ++ set.toArray.qsort (· < ·)

-- Weight keys ------------------------------------------------------------------

/-- Push the face key a styled context resolves to, when its weight is off
the standard corners the driver always loads (regular 400 and bold 700). -/
private def pushWeightKey (acc : Array (Nat × Nat × Bool)) (sty : TextStyle) :
    Array (Nat × Nat × Bool) :=
  let w := sty.weight.css
  if w == 400 || w == 700 then acc
  else
    let key := (sty.slot, w, sty.italic)
    if acc.contains key then acc else acc.push key

mutual
-- conserves: none — a key census, not a tree rewrite: the walk reads and
-- collects, ships no ink, and returns no tree. Hand-rolled rather than a
-- `foldInlines` leaf because the key is a function of the styled
-- *ancestry* (`applyStyle` folded down the spine), which a context-free
-- leaf fold cannot see.
private def weightKeysInline (acc : Array (Nat × Nat × Bool)) (sty : TextStyle) :
    Ir.Inline → Array (Nat × Nat × Bool)
  | .styled st body =>
    -- the ladder never moves a weight (`weight_agree`), so the census may
    -- pass the engine scale
    let sty := applyStyle Ir.sizeScale sty st
    weightKeysInlineList (pushWeightKey acc sty) sty body.toList
  | .colored _ _ body => weightKeysInlineList acc sty body.toList
  | .role _ body => weightKeysInlineList acc sty body.toList
  | .link _ body => weightKeysInlineList acc sty body.toList
  | .underline body => weightKeysInlineList acc sty body.toList
  | .step _ _ body => weightKeysInlineList acc sty body.toList
  -- A note body sets at the page foot in the base style, not the mark's.
  | .footnote _ body => weightKeysInlineList acc {} body.toList
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _
  | .fill | .strut _ | .pageNumber | .pageCount | .linebreak _ => acc

private def weightKeysInlineList (acc : Array (Nat × Nat × Bool))
    (sty : TextStyle) : List Ir.Inline → Array (Nat × Nat × Bool)
  | [] => acc
  | x :: rest => weightKeysInlineList (weightKeysInline acc sty x) sty rest
end

mutual
private def weightKeysBlock (acc : Array (Nat × Nat × Bool)) :
    Ir.Block → Array (Nat × Nat × Bool)
  | .para content => weightKeysInlineList acc {} content.toList
  | .equation _ content => weightKeysInlineList acc {} content.toList
  | .section _ _ _ title => weightKeysInlineList acc {} title.toList
  | .list _ items => weightKeysBlockItems acc items.toList
  | .center body => weightKeysBlockList acc body.toList
  | .ragged body => weightKeysBlockList acc body.toList
  | .quote body => weightKeysBlockList acc body.toList
  | .abstract body => weightKeysBlockList acc body.toList
  | .titled _ title body =>
    weightKeysBlockList (weightKeysInlineList acc {} title.toList) body.toList
  | .role _ body => weightKeysBlockList acc body.toList
  | .spaced _ body => weightKeysBlockList acc body.toList
  | .columns cols => weightKeysBlockCols acc cols.toList
  | .step _ _ body => weightKeysBlockList acc body.toList
  | .only _ body => weightKeysBlockList acc body.toList
  | .nav _ body => weightKeysBlockList acc body.toList
  | .note body => weightKeysBlockList acc body.toList
  | .frame title _ _ body =>
    weightKeysBlockList (weightKeysInlineList acc {} title.toList) body.toList
  | .framefoot content => weightKeysInlineList acc {} content.toList
  | .float _ _ _ body caption =>
    weightKeysBlockList (weightKeysInlineList acc {} caption.toList) body.toList
  | .table _ _ _ rows _ => weightKeysTableRows acc rows.toList
  -- A line's content and comment set at the base style; the generated
  -- keyword bold is a corner face, not an off-corner key.
  | .algorithm _ _ lines =>
    lines.foldl (fun a l =>
      let a := weightKeysInlineList a {} l.content.toList
      match l.comment with
      | some c => weightKeysInlineList a {} c.toList
      | none => a) acc
  | .logo content => weightKeysInlineList acc {} content.toList
  | .picture pic =>
    pic.labelContents.foldl (fun a c => weightKeysInlineList a {} c.toList) acc
  | .verbatim _ _ _ | .setPalette _ | .setTokens _ | .pagebreak
  | .rule _ _ _ | .bibliography _ _ _ => acc

private def weightKeysBlockList (acc : Array (Nat × Nat × Bool)) :
    List Ir.Block → Array (Nat × Nat × Bool)
  | [] => acc
  | b :: rest => weightKeysBlockList (weightKeysBlock acc b) rest

private def weightKeysBlockItems (acc : Array (Nat × Nat × Bool)) :
    List (Array Ir.Block) → Array (Nat × Nat × Bool)
  | [] => acc
  | item :: rest => weightKeysBlockItems (weightKeysBlockList acc item.toList) rest

private def weightKeysBlockCols (acc : Array (Nat × Nat × Bool)) :
    List (Option Nat × Array Ir.Block) → Array (Nat × Nat × Bool)
  | [] => acc
  | (_, body) :: rest => weightKeysBlockCols (weightKeysBlockList acc body.toList) rest

private def weightKeysTableRows (acc : Array (Nat × Nat × Bool)) :
    List (Array (Array Ir.Inline)) → Array (Nat × Nat × Bool)
  | [] => acc
  | row :: rest =>
    weightKeysTableRows (row.foldl
      (fun a cell => weightKeysInlineList a {} cell.toList) acc) rest
end

/-- Every off-corner face key the document's styles can ask
`FontSet.lookup` for: `(slot, weight, italic)` with the styled ancestry
applied exactly as layout will apply it (`applyStyle` folds the spine
here and there alike, so the two cannot drift). The driver resolves an
index entry per key before layout begins — the same precompute contract
as `docScalars` — which is what keeps a `\fontseries{l}` run from
silently falling back to the regular face, and keeps the never-silent
substitution warning (W0366) firing only for weights the document
really uses. Style templates (`\style{...}{ font = ... }`) join at the
base style, as their elaboration does. -/
def docWeightKeys (doc : Doc) : Array (Nat × Nat × Bool) := Id.run do
  let mut acc := weightKeysBlockList #[] doc.body.toList
  if let some h := doc.head then
    acc := weightKeysInlineList acc {} h.toList
  if let some f := doc.foot then
    acc := weightKeysInlineList acc {} f.toList
  for (_, st) in doc.styles.entries do
    if let some tpl := st.font then
      acc := weightKeysInlineList acc {} tpl.toList
    if let some tpl := st.authorFont then
      acc := weightKeysInlineList acc {} tpl.toList
  return acc

-- Math -------------------------------------------------------------------------

/-- One mu: 1/18 of an em at the given size (TeXbook p. 168). -/
private def muAt (size : Sp) (mu : Int) : Sp :=
  size * mu / 18

/-- Everything measuring a formula needs: the math face and its constants,
the font set whose per-scalar fallback serves a glyph the math face lacks,
and the run properties the formula inherits from its surroundings. -/
private structure MathEnv where
  idx : Nat
  font : Font
  consts : MathConsts
  fs : FontSet
  color : Ir.Color
  link : Option String
  underline : Bool
  base : Sp
  ground : Option Ir.Color := none

/-- Font size at a style: base for display and text, the face's declared
percentages for the script styles (`Math.sizeFor`, clamped on parse). -/
private def MathEnv.sizeAt (e : MathEnv) (st : Math.MathStyle) : Sp :=
  Math.sizeFor e.consts.scales e.base st

/-- A MATH constant (font design units) scaled at a size. Constants are read
from the font of the base and scale with the base's size (OpenType MATH
spec, MathConstants). -/
private def MathEnv.constAt (e : MathEnv) (size : Sp) (v : Int) : Sp :=
  v * size / (e.font.unitsPerEm : Int)

/-- A glyph's vertical ink extent `(top, bottom)` scaled at a size, from
its own outline; a face the decoder cannot answer for falls back to the
cap height and the baseline. -/
private def MathEnv.glyphExtent (e : MathEnv) (size : Sp) (g : Nat) : Sp × Sp :=
  match e.font.yExtent g with
  | some (lo, hi) =>
    (hi * size / (e.font.unitsPerEm : Int), lo * size / (e.font.unitsPerEm : Int))
  | none => (e.font.capHeight * size / (e.font.unitsPerEm : Int), 0)

/-- A kern in the math stream: width, no glyphs, never a breakpoint. -/
private def mathKern (e : MathEnv) (size w : Sp) : Item :=
  .box w e.idx e.color e.link #[] size e.underline 0 e.ground

/-- Width of assembled math items: boxes only ever enter the stream, so the
advance of a math box is the sum of what it contains plus the kerns the
spacing table put between them — `mathBoxChecks` holds the two ways of
computing it equal in sp. -/
def mathItemsWidth (items : Array Item) : Sp :=
  items.foldl (fun w it => match it with
    | .box bw _ _ _ _ _ _ _ _ => w + bw
    | _ => w) 0

private abbrev MAcc := Array Item × Array (Nat × Char)

/-- The vertical ink extent `(top, bottom)` of assembled math items,
relative to the surrounding baseline: each glyph's outline extent scaled at
its box's size and shifted by its raise; a rule spans `raise` to
`raise + thickness`. Glyphless boxes — kerns, struts — carry no ink.
`(0, 0)` when nothing has ink. -/
private def mathItemsExtent (font : Font) (items : Array Item) : Sp × Sp := Id.run do
  let mut top : Sp := 0
  let mut bot : Sp := 0
  let upem : Int := font.unitsPerEm
  for it in items do
    match it with
    | .box _ _ _ _ glyphs size _ raise _ =>
      for (g, _, _) in glyphs do
        match font.yExtent g with
        | some (lo, hi) =>
          top := max top (raise + hi * size / upem)
          bot := min bot (raise + lo * size / upem)
        | none =>
          top := max top (raise + font.capHeight * size / upem)
          bot := min bot raise
    | .rule _ t r _ =>
      top := max top (r + t)
      bot := min bot r
    | .glue _ | .pen _ _ _ _ _ _ | .img _ _ _ => pure ()
  return (top, bot)

/-- The same items shifted vertically: every raise moves, no width does. -/
private def raiseItems (delta : Sp) (items : Array Item) : Array Item :=
  if delta == 0 then items else
  items.map fun it => match it with
    | .box w i c l g s u r gr => .box w i c l g s u (r + delta) gr
    | .rule w t r c => .rule w t (r + delta) c
    | .glue g => .glue g
    | .pen w c f i col g => .pen w c f i col g
    | .img s w h => .img s w h

/-- TeX's strut: an invisible box whose only effect is the line's height or
depth. `placeLine` reads a run's height as its cap height (at the run's
size) plus its raise, so a 1 sp box raised to `top` (and one sunk to `bot`)
tells the line builder exactly the room an assembled construction needs —
the fraction hanging above and below, the grown delimiter's reach. -/
private def struts (e : MathEnv) (top bot : Sp) : Array Item :=
  #[.box 0 e.idx e.color e.link #[] 1 false (max 0 top) e.ground,
    .box 0 e.idx e.color e.link #[] 1 false (min 0 bot) e.ground]

/-- The size ladder a glyph grows through: its vertical variants, or just
itself when the face grows it no further. -/
private def variantLadder (e : MathEnv) (g : Nat) : List (Nat × Int) :=
  let vs := e.font.vertVariants g
  if vs.isEmpty then
    match e.font.yExtent g with
    | some (lo, hi) => [(g, hi - lo)]
    | none => [(g, 0)]
  else vs.toList

/-- Assemble a laid `\left…\right` body between its grown delimiters
(TeXbook Appendix G rule 19 with plain TeX's `\delimiterfactor` 901 and
`\delimitershortfall` 5 pt at the 10 pt base): the delimiter grows through
the face's variants until it covers the body's reach from the axis, and
the chosen glyph centres its ink on the axis. The empty `.` delimiter is a
`\nulldelimiterspace` kern. -/
private def delimAssemble (e : MathEnv) (size raise : Sp) (l r : Option Char)
    (bItems : Array Item) (missing0 : Array (Nat × Char)) :
    Array Item × Array (Nat × Char) := Id.run do
  let axis := e.constAt size e.consts.axisHeight
  let (bTop, bBot) := mathItemsExtent e.font bItems
  let δ := max (bTop - axis) (axis - bBot)
  let target := max (2 * δ * 901 / 1000) (2 * δ - size / 2)
  let targetDu := target * (e.font.unitsPerEm : Int) / size
  let nd := size * 12 / 100
  let mut items : Array Item := #[]
  let mut missing := missing0
  let mut top := bTop
  let mut bot := bBot
  let one := fun (c : Char) (items : Array Item) (missing : Array (Nat × Char)) =>
    match glyphOf size e.font c with
    | some (g, _, _) =>
      let (gv, _) := (Math.pickVariant targetDu (variantLadder e g)).getD (g, 0)
      let (vTop, vBot) := e.glyphExtent size gv
      let w := scaledAt size e.font (e.font.widths[gv]?.getD 0)
      let dRaise := raise + axis - (vTop + vBot) / 2
      (items.push (Item.box w e.idx e.color e.link #[(gv, c, w)] size e.underline dRaise e.ground),
       missing, dRaise - raise + vTop, dRaise - raise + vBot)
    | none =>
      (items, if missing.contains (e.idx, c) then missing else missing.push (e.idx, c),
       bTop, bBot)
  match l with
  | some c =>
    let (its, m, t, b) := one c items missing
    items := its
    missing := m
    top := max top t
    bot := min bot b
  | none => items := items.push (mathKern e size nd)
  let raisedBody := raiseItems raise bItems
  items := items ++ raisedBody
  match r with
  | some c =>
    let (its, m, t, b) := one c items missing
    items := its
    missing := m
    top := max top t
    bot := min bot b
  | none => items := items.push (mathKern e size nd)
  items := items ++ struts e (raise + top) (raise + bot)
  return (items, missing)

/-- Assemble laid grid cells (TeXbook ch. 22's `\halign` rule: each column
as wide as its widest cell): cells padded into their columns per the grid
kind at offsets every row shares (`Math.colOffset`), rows a baselineskip
plus `\jot` apart (plain TeX's 12 pt and 3 pt at the 10 pt base; amsmath
opens display alignments by `\jot`) or further when ink would collide, and
the whole grid centred on the axis, as `\vcenter` centres a matrix. -/
private def gridAssemble (e : MathEnv) (size raise : Sp) (kind : Math.GridKind)
    (cells : Array (Array (Array Item))) : Array Item := Id.run do
  let axis := e.constAt size e.consts.axisHeight
  let n := cells.foldl (fun m row => max m row.size) 0
  if n == 0 then
    return #[]
  let mut colW : Array Sp := Array.replicate n 0
  for row in cells do
    for k in [0:row.size] do
      colW := colW.set! k (max colW[k]! (mathItemsWidth row[k]!))
  let cols : List (Sp × Sp) := (List.range n).map fun k =>
    (colW[k]!, muAt size (kind.gapAfter k n : Int))
  let total := Math.colOffset cols n
  -- The grid's baseline distance is the text leading, one source
  -- (`leadingFor`): a maths grid is lines of maths, and its rhythm is the
  -- page's. The old `size * 12 / 10` was the same 6/5 re-spelled.
  let bl := leadingFor size
  -- The least clearance when a row's ink outruns the leading: plain.tex's
  -- `\lineskip` (1.0 pt) made size-relative — 1 pt at the 10 pt base. Its
  -- own name: the page-level `inkClearance` is a different, absolute
  -- quantity, and one name for two values is how a future reader fuses them.
  let gridSkip := size / 10
  -- LaTeX's `\jot` (latex.ltx: 3pt), the extra opening between display
  -- alignment rows, size-relative — 3 pt at the 10 pt base. An `array` is
  -- inline math's grid and takes none, as LaTeX's array does not.
  let jot := match kind with
    | .array _ => 0
    | _ => size * 3 / 10
  let rowExtents := cells.map fun row =>
    row.foldl (fun (t, b) cell =>
      let (ct, cb) := mathItemsExtent e.font cell
      (max t ct, min b cb)) ((0 : Sp), (0 : Sp))
  let mut ys : Array Sp := #[]
  let mut y : Sp := 0
  for i in [0:cells.size] do
    if i > 0 then
      let d := max (bl + jot)
        ((-(rowExtents[i-1]!.2)) + rowExtents[i]!.1 + gridSkip)
      y := y - d
    ys := ys.push y
  let top := rowExtents[0]!.1
  let bot := y + (rowExtents[cells.size - 1]!).2
  let Δ := raise + axis - (top + bot) / 2
  let mut items : Array Item := #[]
  for i in [0:cells.size] do
    let row := cells[i]!
    let mut cur : Sp := 0
    for k in [0:row.size] do
      let cellItems := row[k]!
      let cw := mathItemsWidth cellItems
      let x := Math.colOffset cols k + (kind.colAlign k).pad colW[k]! cw
      items := items.push (mathKern e size (x - cur))
      items := items ++ raiseItems (Δ + ys[i]!) cellItems
      cur := x + cw
    items := items.push (mathKern e size (total - cur))
    items := items.push (mathKern e size (-total))
  items := items.push (mathKern e size total)
  items := items ++ struts e (Δ + top) (Δ + bot)
  return items

/-- Assemble a laid fraction (TeXbook Appendix G rule 15 over the MATH
constants): numerator shifted up, denominator shifted down, the bar
`fractionRuleThickness` thick with its middle on the axis, the shifts
opened until the spec's minimum gaps clear the ink, both parts centred
over the bar, and plain TeX's `\nulldelimiterspace` (1.2 pt at the 10 pt
base) each side. -/
private def fracAssemble (e : MathEnv) (size : Sp) (display : Bool) (raise : Sp)
    (numItems denItems : Array Item) : Array Item :=
  let axis := e.constAt size e.consts.axisHeight
  let θ := e.constAt size e.consts.fractionRuleThickness
  let u0 := e.constAt size (if display then e.consts.fractionNumeratorDisplayStyleShiftUp
    else e.consts.fractionNumeratorShiftUp)
  let v0 := e.constAt size (if display then e.consts.fractionDenominatorDisplayStyleShiftDown
    else e.consts.fractionDenominatorShiftDown)
  let gapN := e.constAt size (if display then e.consts.fractionNumDisplayStyleGapMin
    else e.consts.fractionNumeratorGapMin)
  let gapD := e.constAt size (if display then e.consts.fractionDenomDisplayStyleGapMin
    else e.consts.fractionDenominatorGapMin)
  let (numTop, numBot) := mathItemsExtent e.font numItems
  let (denTop, denBot) := mathItemsExtent e.font denItems
  let u := max u0 (axis + θ / 2 + gapN - numBot)
  let v := max v0 (denTop + gapD - (axis - θ / 2))
  let numW := mathItemsWidth numItems
  let denW := mathItemsWidth denItems
  let ruleW := max numW denW
  let nd := size * 12 / 100
  let numPad := Math.ColAlign.pad .center ruleW numW
  let denPad := Math.ColAlign.pad .center ruleW denW
  (#[mathKern e size nd, mathKern e size numPad]
      ++ raiseItems (raise + u) numItems)
    ++ (#[mathKern e size (ruleW - numPad - numW), mathKern e size (-ruleW),
          Item.rule ruleW θ (raise + axis - θ / 2) e.color,
          mathKern e size (-ruleW), mathKern e size denPad]
      ++ raiseItems (raise - v) denItems)
    ++ #[mathKern e size (ruleW - denPad - denW), mathKern e size nd]
    ++ struts e (raise + u + numTop) (raise - v + denBot)

/-- Assemble a laid radical (MATH spec radical constants): the radicand
under an overbar `radicalRuleThickness` thick and `radicalVerticalGap`
above its ink (`radicalDisplayStyleVerticalGap` in display), the surd
grown through the face's variants until it spans bar and body, its ink top
at the bar's top; the degree kerned by `radicalKernBeforeDegree` /
`radicalKernAfterDegree` and raised `radicalDegreeBottomRaisePercent` of
the surd's height. -/
private def radAssemble (e : MathEnv) (size : Sp) (display : Bool) (raise : Sp)
    (bItems degItems : Array Item) (missing0 : Array (Nat × Char)) :
    Array Item × Array (Nat × Char) :=
  let θ := e.constAt size e.consts.radicalRuleThickness
  let ψ := e.constAt size (if display then e.consts.radicalDisplayStyleVerticalGap
    else e.consts.radicalVerticalGap)
  let (bTop, bBot) := mathItemsExtent e.font bItems
  let ruleBot := bTop + ψ
  let ruleTop := ruleBot + θ
  let bodyW := mathItemsWidth bItems
  let extraAsc := e.constAt size e.consts.radicalExtraAscender
  match glyphOf size e.font '\u221A' with
  | none =>
    let missing := if missing0.contains (e.idx, '\u221A') then missing0
      else missing0.push (e.idx, '\u221A')
    let raisedBody := raiseItems raise bItems
    let items := (#[(Item.rule bodyW θ (raise + ruleBot) e.color),
        mathKern e size (-bodyW)]
      ++ raisedBody)
      ++ struts e (raise + ruleTop + extraAsc) (raise + bBot)
    (items, missing)
  | some (g, _, _) =>
    let targetDu := (ruleTop - min 0 bBot) * (e.font.unitsPerEm : Int) / size
    let (gv, _) := (Math.pickVariant targetDu (variantLadder e g)).getD (g, 0)
    let (vTop, vBot) := e.glyphExtent size gv
    let surdW := scaledAt size e.font (e.font.widths[gv]?.getD 0)
    let surdRaise := raise + ruleTop - vTop
    let raisedBody := raiseItems raise bItems
    let degPrefix :=
      if degItems.isEmpty then #[] else Id.run do
        let degRaise := surdRaise + vBot +
          (vTop - vBot) * e.consts.radicalDegreeBottomRaisePercent / 100
        let kernB := e.constAt size e.consts.radicalKernBeforeDegree
        let kernA := e.constAt size e.consts.radicalKernAfterDegree
        return (#[mathKern e size kernB] ++ raiseItems degRaise degItems).push
          (mathKern e size kernA)
    let items := (degPrefix.push
        (.box surdW e.idx e.color e.link #[(gv, '\u221A', surdW)] size e.underline surdRaise e.ground)
      |>.push (Item.rule bodyW θ (raise + ruleBot) e.color)
      |>.push (mathKern e size (-bodyW)))
      ++ raisedBody
      ++ struts e (raise + ruleTop + extraAsc) (min (raise + bBot) (surdRaise + vBot))
    (items, missing0)

/-- Assemble a laid accent (TeXbook Appendix G rule 12 over the MATH
constants): the mark placed so its own attachment x (MathTopAccentAttachment,
unclamped — `Font.markAttachX`) lands on the base's (`Font.topAccentX`,
clamped into the advance, half the advance where the face lacks the point;
half the assembled width when the base is more than one glyph), and raised
by the base ink's excess over `accentBaseHeight` — rule 12's `h − min(h, χ)`.
A stretching mark takes the widest horizontal variant that does not overhang
the base (`Math.pickWidest`); the U+0305 mark is `\overline`, drawn as a
rule from the overbar constants — exact at any width, the stated fallback
needing no variant. A mark glyph the face lacks is recorded missing (the
E0405 path); the base still renders. -/
private def accentAssemble (e : MathEnv) (size raise : Sp) (mark : Char)
    (stretch : Bool) (bItems : Array Item) (missing0 : Array (Nat × Char)) :
    Array Item × Array (Nat × Char) := Id.run do
  let (bTop, bBot) := mathItemsExtent e.font bItems
  let baseW := mathItemsWidth bItems
  let raisedBody := raiseItems raise bItems
  if mark == '\u0305' then
    let θ := e.constAt size e.consts.overbarRuleThickness
    let ψ := e.constAt size e.consts.overbarVerticalGap
    let extraAsc := e.constAt size e.consts.overbarExtraAscender
    let ruleBot := bTop + ψ
    let items := (raisedBody.push (mathKern e size (-baseW))).push
        (Item.rule baseW θ (raise + ruleBot) e.color)
      ++ struts e (raise + ruleBot + θ + extraAsc) (raise + bBot)
    return (items, missing0)
  match glyphOf size e.font mark with
  | none =>
    let missing := if missing0.contains (e.idx, mark) then missing0
      else missing0.push (e.idx, mark)
    return (raisedBody ++ struts e (raise + bTop) (raise + bBot), missing)
  | some (g, _, _) =>
    -- The base's attachment point: its one glyph's, when the base is one
    -- glyph of the math face; else the assembled width's centre.
    let baseTA :=
      match bItems.filter (fun it => match it with
        | .box _ _ _ _ glyphs _ _ _ _ => !glyphs.isEmpty
        | _ => false) with
      | #[.box _ fi _ _ #[(bg, _, _)] bsize _ _ _] =>
        if fi == e.idx then e.constAt bsize (e.font.topAccentX bg) else baseW / 2
      | _ => baseW / 2
    let gv :=
      if stretch then
        let ladder := (e.font.horizVariants g).toList
        let targetDu := baseW * (e.font.unitsPerEm : Int) / size
        ((Math.pickWidest targetDu (if ladder.isEmpty then [(g, 0)] else ladder)).getD
          (g, 0)).1
      else g
    let wAcc := scaledAt size e.font (e.font.widths[gv]?.getD 0)
    let shift := baseTA - e.constAt size (e.font.markAttachX gv)
    let accRaise := raise +
      max 0 (bTop - e.constAt size e.consts.accentBaseHeight)
    let (mTop, mBot) := e.glyphExtent size gv
    let items := ((raisedBody.push (mathKern e size (-baseW + shift))).push
        (Item.box wAcc e.idx e.color e.link #[(gv, mark, wAcc)] size e.underline accRaise e.ground)
      |>.push (mathKern e size (baseW - shift - wAcc)))
      ++ struts e (max (raise + bTop) (accRaise + mTop))
        (min (raise + bBot) (accRaise + mBot))
    return (items, missing0)

mutual

/-- Lay one math list: spacing between adjacent atoms from the degraded
classes (`cls`, precomputed per level), atoms measured by `layMathItem`.
`prev` is the previous atom's degraded class; an explicit space resets it,
so spacing is inserted only between directly adjacent atoms. -/
private def layMathTail (e : MathEnv) (st : Math.MathStyle) (raise : Sp)
    (cls : List Math.MathClass) (prev : Option Math.MathClass) (acc : MAcc) :
    Math.MList → MAcc
  | .nil => acc
  | .cons x rest =>
    match x.classOf with
    | none =>
      let mu := match x with
        | .space m => m
        | _ => 0
      let size := e.sizeAt st
      let acc := ((acc.1.push (mathKern e size (muAt size mu))), acc.2)
      layMathTail e st raise cls none acc rest
    | some _ =>
      let (c, cs) := match cls with
        | c :: cs => (c, cs)
        | [] => (x.classOf.getD .ord, [])
      let size := e.sizeAt st
      let acc := match prev with
        | some p =>
          let mu := (Math.spacing p c st).mu
          if mu == 0 then acc
          else ((acc.1.push (mathKern e size (muAt size (mu : Int)))), acc.2)
        | none => acc
      let acc := layMathItem e st raise x acc
      layMathTail e st raise cs (some c) acc rest

/-- Lay one atom: its nucleus at the current style — an Op nucleus in
display style grown to the face's display-size variant and centred on the
axis (MATH spec `displayOperatorMinHeight`; TeXbook Appendix G rule 13) —
then its scripts. A limit-taking operator in display style sets its scripts
as limits above and below, centred (rule 13a, gaps and rises from the MATH
constants); everything else takes the script styles at the base's shift
constants (`superscriptShiftUp` / `superscriptShiftUpCramped` /
`subscriptShiftDown`), with `spaceAfterScript` after. When both scripts are
present they stack at one horizontal position: the subscript rewinds by the
superscript's width through a negative kern, and the atom advances by the
wider of the two. -/
private def layMathItem (e : MathEnv) (st : Math.MathStyle) (raise : Sp)
    (x : Math.MItem) (acc : MAcc) : MAcc :=
  match x with
  | .space mu =>
    let size := e.sizeAt st
    ((acc.1.push (mathKern e size (muAt size mu))), acc.2)
  | .atom cls nuc sup sub lim =>
    let size := e.sizeAt st
    let display := st.rank == 3
    -- The nucleus, laid into its own run so the limit path can measure it.
    let (nucItems, m0) :=
      match nuc, cls, display with
      | .sym c, .op, true =>
        match glyphOf size e.font c with
        | some (g, _, _) =>
          let (gv, _) := (Math.pickVariant e.consts.displayOperatorMinHeight
            (variantLadder e g)).getD (g, 0)
          let w := scaledAt size e.font (e.font.widths[gv]?.getD 0)
          let (vTop, vBot) := e.glyphExtent size gv
          let axis := e.constAt size e.consts.axisHeight
          let vRaise := raise + axis - (vTop + vBot) / 2
          (#[(Item.box w e.idx e.color e.link #[(gv, c, w)] size e.underline vRaise e.ground)]
            ++ struts e (vRaise + vTop) (vRaise + vBot), acc.2)
        | none =>
          if acc.2.contains (e.idx, c) then (#[], acc.2)
          else (#[], acc.2.push (e.idx, c))
      | _, _, _ => layMathNucleus e st raise nuc (#[], acc.2)
    if lim && display && !(sup == .nil && sub == .nil) then
      -- Limits: scripts above and below the operator, centred on it.
      let (supItems, m1) := layMathTail e st.sup 0
        (Math.degrade sup.classes) none (#[], m0) sup
      let (subItems, m2) := layMathTail e st.sub 0
        (Math.degrade sub.classes) none (#[], m1) sub
      let (opTop, opBot) := mathItemsExtent e.font nucItems
      let (supTop, supBot) := mathItemsExtent e.font supItems
      let (subTop, subBot) := mathItemsExtent e.font subItems
      let opW := mathItemsWidth nucItems
      let supW := mathItemsWidth supItems
      let subW := mathItemsWidth subItems
      let w := max opW (max supW subW)
      let rise := max (opTop + e.constAt size e.consts.upperLimitBaselineRiseMin)
        (opTop + e.constAt size e.consts.upperLimitGapMin - supBot)
      let low := min (opBot - e.constAt size e.consts.lowerLimitBaselineDropMin)
        (opBot - e.constAt size e.consts.lowerLimitGapMin - subTop)
      let place (items : Array Item) (itemsW : Sp) (delta : Sp) : Array Item :=
        if items.isEmpty then #[] else
        let padK := Math.ColAlign.pad .center w itemsW
        let shifted := raiseItems delta items
        (#[mathKern e size padK] ++ shifted).push
          (mathKern e size (w - padK - itemsW)) |>.push (mathKern e size (-w))
      let placedNuc := place nucItems opW 0
      let placedSup := place supItems supW rise
      let placedSub := place subItems subW low
      let items := placedNuc ++ placedSup ++ placedSub
      -- The last placed run rewound to the start; advance by the width.
      let items := items.push (mathKern e size w)
      let items := items ++ struts e
        (if supItems.isEmpty then opTop else rise + supTop)
        (if subItems.isEmpty then opBot else low + subBot)
      (acc.1 ++ items, m2)
    else
    let acc := (acc.1 ++ nucItems, m0)
    let upShift := e.constAt size
      (if st.cramped then e.consts.superscriptShiftUpCramped
       else e.consts.superscriptShiftUp)
    let downShift := e.constAt size e.consts.subscriptShiftDown
    let (supItems, m1) := layMathTail e st.sup (raise + upShift)
      (Math.degrade sup.classes) none (#[], acc.2) sup
    let (subItems, m2) := layMathTail e st.sub (raise - downShift)
      (Math.degrade sub.classes) none (#[], m1) sub
    if supItems.isEmpty && subItems.isEmpty then
      (acc.1, m2)
    else
      let spaceAfter := e.constAt size e.consts.spaceAfterScript
      let supW := mathItemsWidth supItems
      let subW := mathItemsWidth subItems
      if supItems.isEmpty then
        ((acc.1 ++ subItems).push (mathKern e size spaceAfter), m2)
      else if subItems.isEmpty then
        ((acc.1 ++ supItems).push (mathKern e size spaceAfter), m2)
      else
        let items := (acc.1 ++ supItems).push (mathKern e size (-supW)) ++ subItems
        (items.push (mathKern e size (max supW subW - subW + spaceAfter)), m2)

private def layMathNucleus (e : MathEnv) (st : Math.MathStyle) (raise : Sp)
    (nuc : Math.MNucleus) (acc : MAcc) : MAcc :=
  match nuc with
  | .sym c =>
    let size := e.sizeAt st
    match glyphOf size e.font c with
    | some g =>
      ((acc.1.push (.box g.2.2 e.idx e.color e.link #[g] size e.underline raise e.ground)), acc.2)
    | none =>
      -- A scalar the math face lacks goes through the per-scalar chain the
      -- driver precomputed for text (`FontSet.fallback`) — one mechanism,
      -- at the math size, its own box since a box carries one face.
      match e.fs.fallbackFor c |>.bind fun fb =>
          (glyphOf size (e.fs.get fb) c).map (fb, ·) with
      | some (fb, g) =>
        ((acc.1.push (.box g.2.2 fb e.color e.link #[g] size e.underline raise e.ground)), acc.2)
      | none =>
        -- A math alphabet's scalar uncovered everywhere: the base letter
        -- stands in — bold/italic from the text face where that is the
        -- alphabet's styling, the plain letter otherwise — and the
        -- per-formula post-walk names the loss (N0018). Only when even
        -- the stand-in is uncovered does the scalar go missing (E0405).
        let synth : Option (Nat × (Nat × Char × Sp)) := do
          let (a, base) ← Math.MathAlphabet.unapply c
          let (bold, italic) := a.synthStyle
          let fi := if bold || italic then e.fs.lookup 0 (if bold then 700 else 400) italic else e.idx
          let g ← glyphOf size (e.fs.get fi) base
          return (fi, g)
        match synth with
        | some (fi, g) =>
          ((acc.1.push (.box g.2.2 fi e.color e.link #[g] size e.underline raise e.ground)), acc.2)
        | none =>
          if acc.2.contains (e.idx, c) then acc
          else (acc.1, acc.2.push (e.idx, c))
  | .word s => Id.run do
    -- An upright word (a function name, `\text`): boxes in the math face,
    -- split only where the chain substitutes — a box carries one face.
    let size := e.sizeAt st
    let mut items := acc.1
    let mut missing := acc.2
    let mut cur := e.idx
    let mut glyphs : Array (Nat × Char × Sp) := #[]
    let mut w : Sp := 0
    for c in s.toList do
      let hit := match glyphOf size e.font c with
        | some g => some (e.idx, g)
        | none => e.fs.fallbackFor c |>.bind fun fb =>
            (glyphOf size (e.fs.get fb) c).map (fb, ·)
      match hit with
      | some (fi, g) =>
        if fi != cur && !glyphs.isEmpty then
          items := items.push (.box w cur e.color e.link glyphs size e.underline raise e.ground)
          glyphs := #[]
          w := 0
        cur := fi
        glyphs := glyphs.push g
        w := w + g.2.2
      | none =>
        unless missing.contains (e.idx, c) do
          missing := missing.push (e.idx, c)
    return (items.push (.box w cur e.color e.link glyphs size e.underline raise e.ground), missing)
  | .list body =>
    layMathTail e st raise (Math.degrade body.classes) none acc body
  | .frac num den =>
    let (numItems, m1) := layMathTail e st.fracNum 0
      (Math.degrade num.classes) none (#[], acc.2) num
    let (denItems, m2) := layMathTail e st.fracDen 0
      (Math.degrade den.classes) none (#[], m1) den
    (acc.1 ++ fracAssemble e (e.sizeAt st) (st.rank == 3) raise numItems denItems, m2)
  | .rad deg body =>
    let (bItems, m1) := layMathTail e st.cramp 0
      (Math.degrade body.classes) none (#[], acc.2) body
    let (degItems, m2) := layMathTail e (.scriptscript st.cramped) 0
      (Math.degrade deg.classes) none (#[], m1) deg
    let (items, missing) := radAssemble e (e.sizeAt st) (st.rank == 3) raise
      bItems degItems m2
    (acc.1 ++ items, missing)
  | .delim l r body =>
    let (bItems, m1) := layMathTail e st 0
      (Math.degrade body.classes) none (#[], acc.2) body
    let (items, missing) := delimAssemble e (e.sizeAt st) raise l r bItems m1
    (acc.1 ++ items, missing)
  | .accent mark stretch body =>
    -- The base sets in the cramped current style (TeXbook Appendix G
    -- rule 12), which keeps its size: cramping preserves rank.
    let (bItems, m1) := layMathTail e st.cramp 0
      (Math.degrade body.classes) none (#[], acc.2) body
    let (items, missing) := accentAssemble e (e.sizeAt st) raise mark stretch
      bItems m1
    (acc.1 ++ items, missing)
  | .grid kind rows =>
    let cellSt : Math.MathStyle := match kind with
      | .array _ => if st.rank > 2 then .text st.cramped else st
      | _ => st
    let (cells, missing) := layGridRows e cellSt (#[], acc.2) rows
    (acc.1 ++ gridAssemble e (e.sizeAt st) raise kind cells, missing)

/-- The cells of one row, each laid into its own run. -/
private def layGridRow (e : MathEnv) (st : Math.MathStyle)
    (acc : Array (Array Item) × Array (Nat × Char)) :
    Math.MRow → Array (Array Item) × Array (Nat × Char)
  | .nil => acc
  | .cons cell rest =>
    let (items, m) := layMathTail e st 0
      (Math.degrade cell.classes) none (#[], acc.2) cell
    layGridRow e st (acc.1.push items, m) rest

private def layGridRows (e : MathEnv) (st : Math.MathStyle)
    (acc : Array (Array (Array Item)) × Array (Nat × Char)) :
    Math.MRows → Array (Array (Array Item)) × Array (Nat × Char)
  | .nil => acc
  | .cons row rest =>
    let (cells, m) := layGridRow e st (#[], acc.2) row
    layGridRows e st (acc.1.push cells, m) rest

end

/-- A formula's items: one unbreakable run of boxes and kerns — no glue, so
the line breaker never breaks inside it, and no stretch, so a math box has
one width. Inline math starts in text style, display math in display style
(TeXbook ch. 17). -/
private def mathItems (e : MathEnv) (display : Bool) (body : Math.MList)
    (missing : Array (Nat × Char)) : Array Item × Array (Nat × Char) :=
  let st : Math.MathStyle := if display then .display false else .text false
  layMathTail e st 0 (Math.degrade body.classes) none (#[], missing) body

/-- The one pattern-selection site: which hyphenation table a run's text
consults. An untagged run takes the document's (the main language's)
table; a run tagged `Style.lang` takes its own language's — never the
main table, so a French word under an English main is broken as French
or not at all. `main = none` is hyphenation off (a card, `\page{
hyphenate = off }`) and wins over any tag. -/
def patsOf (main : Option Hyphen.Patterns) (lang : Option String) :
    Option Hyphen.Patterns :=
  match lang with
  | none => main
  | some tag => if main.isNone then none else Hyphen.forTag tag

/-- `hyphenation_follows_language`: the breaks consulted for a run tagged
ℓ are exactly its own language's patterns' — the wiring statement, held
at the selection site. -/
theorem hyphenation_follows_language (main : Option Hyphen.Patterns)
    (tag : String) (h : main.isSome) :
    patsOf main (some tag) = Hyphen.forTag tag := by
  cases main with
  | none => simp at h
  | some _ => rfl

/-- Hyphenation off is off for every language: no tag re-enables it. -/
theorem patsOf_off (lang : Option String) : patsOf none lang = none := by
  cases lang <;> rfl

/-- A footnote mark's box: the number's digits as one raised run at the
scriptsize step of `around`, lifted by `Ir.markRaise` (the OS/2
`ySuperscript*` stand-in; parsing the table is owed) — the shape the
in-text mark and the note's own leading mark share. A box, so no break can
part the mark from the word it follows. Digits the face lacks return
beside the box for the caller's E0405. -/
private def markBox (fs : FontSet) (sty : TextStyle) (around : Sp) (num : Nat) :
    Item × Array (Nat × Char) := Id.run do
  let idx := fs.lookup sty.slot sty.weight.css sty.italic
  let font := fs.get idx
  let markSize := Ir.scaleStep around "scriptsize"
  let raise := around * Ir.markRaise / 1000
  let mut gs : Array (Nat × Char × Sp) := #[]
  let mut w : Sp := 0
  let mut miss : Array (Nat × Char) := #[]
  for c in (toString num).toList do
    match glyphOf markSize font c with
    | some g =>
      gs := gs.push g
      w := w + g.2.2
    | none => miss := miss.push (idx, c)
  return (.box w idx sty.color sty.link gs markSize sty.underline raise sty.ground, miss)

/-- The token fold's state: what the walk has built, and what it has
lost beside it. `dropped` is the never-silent ledger — a (face, char)
pair no face covers lands here and nowhere else, and `itemsOfInlines`
renders every entry as its E0405, so dropped ink is always named to the
user. `substs` (W0009) and `unstyled` (N0018) are the reported
substitutions: set from another face, never lost. -/
private structure ItemsAcc where
  items : Array Item := #[]
  notes : Array (Nat × Nat × Array Inline) := #[]
  dropped : Array (Nat × Char) := #[]
  substs : Array (Nat × Char × Nat) := #[]
  unstyled : Array (Nat × Char × Math.MathAlphabet × Char) := #[]
  extras : Std.HashMap Nat Sp := {}
  cache : Std.HashMap String (Array Nat) := {}

/-- One flatten token into the accumulator — the fold step of
`itemsOfInlines`, named so a conservation statement can induct over it:
every token's ink becomes items, an entry in `dropped`, or a note body
carried whole, and nothing else. -/
private def itemsOfTok (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (imgs : Image.Store) (textW textH : Sp)
    (acc : ItemsAcc) (tk : Tk) : ItemsAcc :=
  match tk with
  | .word sty chars =>
    let idx := fs.lookup sty.slot sty.weight.css sty.italic
    let font := fs.get idx
    -- Small caps: the face's own `smcp`+`c2sc` when it carries them — the
    -- word stays as typed and the gids substitute in `wordItems` — and
    -- uniform synthesis otherwise. One meaning, two mechanisms.
    let useGsub := sty.smallcaps && !font.smallCaps.isEmpty
    let (sty, chars) :=
      if sty.smallcaps && !useGsub then
        smallCapSynth (smallCapScaleFor font) sty chars
      else (sty, chars)
    let sz := size * sty.scale / 1000
    let (ws, m, s, c') :=
      wordItems (patsOf pats sty.lang) (sty.lang.getD "") sz idx sty.color
        sty.ground sty.link sty.underline useGsub fs font chars
        acc.dropped acc.substs acc.cache
    { acc with items := acc.items ++ ws, dropped := m, substs := s, cache := c' }
  | .icon sty c =>
    -- The styled face first (an icon font declared as the body face is
    -- legal), then the fallback chain; either hit is the icon's own face
    -- by design. Only total absence is a loss (E0405, rendered by the
    -- caller from `dropped`).
    let idx := fs.lookup sty.slot sty.weight.css sty.italic
    let sz := size * sty.scale / 1000
    let hit :=
      match glyphOf sz (fs.get idx) c with
      | some g => some (idx, g)
      | none =>
        fs.fallbackFor c |>.bind fun fb =>
          (glyphOf sz (fs.get fb) c).map (fb, ·)
    match hit with
    | some (fb, g) =>
      let box : Item := .box g.2.2 fb sty.color sty.link #[g] sz sty.underline 0
        sty.ground
      { acc with items := acc.items.push box }
    | none =>
      if acc.dropped.contains (idx, c) then acc
      else { acc with dropped := acc.dropped.push (idx, c) }
  | .note num sty body =>
    let (mk, miss) := markBox fs sty (size * sty.scale / 1000) num
    let acc := miss.foldl (fun acc m =>
      if acc.dropped.contains m then acc
      else { acc with dropped := acc.dropped.push m }) acc
    { acc with notes := acc.notes.push (acc.items.size, num, body)
               items := acc.items.push mk }
  | .formula display sty body =>
    -- The flatten pass pushes a formula token only when a math face with
    -- constants is present.
    match fs.mathFont? with
    | some (idx, font, consts) =>
      -- The math face sets at the size that makes its x-height the
      -- surrounding face's — fontspec's `Scale=MatchLowercase`, the rule
      -- `Math.mathSize` states and its agreement theorems bound to the sp.
      let around := fs.get (fs.lookup sty.slot sty.weight.css sty.italic)
      let runSize := size * sty.scale / 1000
      let e : MathEnv := {
        idx, font, consts, fs
        color := sty.color
        link := sty.link
        underline := sty.underline
        ground := sty.ground
        base := (Math.mathSize runSize.toNat around.xHeightOptical
          around.unitsPerEm font.xHeightOptical font.unitsPerEm : Nat) }
      let (ms, m) := mathItems e display body acc.dropped
      -- The substitutions the chain made, named like text's (W0009):
      -- a scalar the math face lacks that a fallback face set. One the
      -- assembly paths recorded missing was never substituted — a grown
      -- construction is one face — so `m` excludes it here. A math
      -- alphabet's scalar no face covers rendered as its stand-in base
      -- letter (`layMathNucleus`): N0018 names the styling difference.
      let acc := (Math.MList.scalarsList #[] body).foldl (fun acc c =>
        if (font.gid c).isNone && !m.contains (idx, c) then
          match fs.fallbackFor c with
          | some fb =>
            if ((fs.get fb).gid c).isSome && !acc.substs.contains (idx, c, fb) then
              { acc with substs := acc.substs.push (idx, c, fb) }
            else acc
          | none =>
            match Math.MathAlphabet.unapply c with
            | some (a, base) =>
              if acc.unstyled.any (·.2.1 == c) then acc
              else { acc with unstyled := acc.unstyled.push (idx, c, a, base) }
            | none => acc
        else acc) acc
      { acc with dropped := m, items := acc.items ++ ms }
    | none => acc
  | .space sty =>
    let idx := fs.lookup sty.slot sty.weight.css sty.italic
    let g : Item := .glue (interword (size * sty.scale / 1000) (fs.get idx))
    { acc with items := acc.items.push g }
  | .fill =>
    -- Stretchable but not a legal breakpoint on its own.
    { acc with items := acc.items.push (.glue { fil := true }) }
  | .strut g =>
    -- Zero width, declared height: raises the line box, ships no ink.
    let strut : Item := .rule 0 (max 0 (g.width.resolve size xHeight)) 0
      Ir.Color.black
    { acc with items := acc.items.push strut }
  | .img src spec =>
    -- The request resolves against the store the driver filled. An entry
    -- that did not load (the driver has said why) keeps the requested
    -- size around a default 1 in square, so the document still compiles
    -- and the placeholder shows where the figure would stand.
    let idx? := imgs.find? src
    let (iW, iH) := match idx?.bind fun k => (imgs.get? k).bind (·.info) with
      | some inf => (inf.width, inf.height)
      | none => (Dim.inch 1, Dim.inch 1) -- the placeholder square: a stated default (comment above), not a design token — the driver already named the load failure
    let (w, h) := Image.resolveSize spec iW iH textW textH
    -- A boundary picture wider than the measure fits it: the box is the
    -- engine's to measure and place (N0023's claim), it is vector — the
    -- form's `/Matrix` scales losslessly — and the document declared no
    -- size to honour, so the only alternatives are an overrun off the
    -- page or a warning about a route the engine chose by default. A
    -- declared `\includegraphics` size is the author's and is never
    -- touched, nor is any ordinary image (LaTeX's overfull, W0005, stays
    -- honest there).
    let (w, h) :=
      if src.startsWith Ir.picSrcPrefix && spec.width.isNone &&
          spec.height.isNone && w > textW && w > 0 then
        (textW, textW * h / w)
      else (w, h)
    { acc with items := acc.items.push (.img idx? (max 0 w) (max 0 h)) }
  | .brk extra =>
    let items := acc.items.push (.glue { fil := true, parfill := true })
    let extras :=
      let sp := extra.width.resolve size xHeight
      if sp != 0 then acc.extras.insert items.size sp else acc.extras
    { acc with items := items.push (.pen 0 forcedCost false 0 Ir.Color.black #[])
               extras := extras }

/-- Inlines to breakable items: one fold of `itemsOfTok` over the flatten
tokens, then every loss the fold ledgered rendered as its diagnostic —
the never-silent contract: no character leaves this function silently,
it is in the items, in a note body, or named by an E0405 (with W0009 and
N0018 naming the substitutions that kept ink at the cost of its face).
The fourth returned component maps the index of a forced-break penalty
to extra vertical space the document asked for there (`\\[1ex]`); it
rides beside the items because the line breaker has no use for it, and
putting it in `Item` would make every pattern carry a field only the
page builder reads. -/
private def itemsOfInlines (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (baseStyle : TextStyle) (xs : Array Inline)
    (cache : Std.HashMap String (Array Nat)) (imgs : Image.Store := {})
    (textW : Sp := 0) (textH : Sp := 0) (noteOk : Bool := false)
    (ladder : List (String × Nat) := Ir.sizeScale) :
    Array Item × Array Diag × Std.HashMap String (Array Nat) ×
      Std.HashMap Nat Sp × Array (Nat × Nat × Array Inline) := Id.run do
  let st := flatten (fs.mathFont?.isSome) noteOk { ladder := ladder } baseStyle xs
  let acc := st.toks.foldl (itemsOfTok pats size xHeight fs imgs textW textH)
    { cache := cache }
  let mut items := acc.items
  -- A paragraph that already ends in a forced break needs no second one: an
  -- empty final line has no feasible predecessor, and the breaker would
  -- return no lines at all -- the whole paragraph, silently gone.
  let endsInBreak := match items.back? with
    | some (.pen _ cost _ _ _ _) => cost ≤ forcedCost
    | _ => false
  if !endsInBreak then
    items := items.push (.glue { fil := true, parfill := true })
    items := items.push (.pen 0 forcedCost false 0 Ir.Color.black #[])
  let mut diags := st.diags
  for (idx, c) in acc.dropped do
    diags := diags.push (Diag.of .E0405
      s!"'{(fs.get idx).family}' has no glyph for '{c}' (U+{hex c.toNat}); dropped"
      (help := "declare a face that covers it in \\fonts, or accept the loss \
with \\allow{E0405}"))
  for (idx, c, fb) in acc.substs do
    diags := diags.push (Diag.of .W0009
      s!"'{(fs.get idx).family}' has no glyph for '{c}' \
        (U+{hex c.toNat}); set from '{(fs.get fb).family}'")
  for (idx, c, a, base) in acc.unstyled do
    let (bold, italic) := a.synthStyle
    if bold || italic then
      diags := diags.push (Diag.of .N0018
        s!"'{(fs.get idx).family}' has no {a.styleLabel} '{base}' \
(U+{hex c.toNat}); set {a.styleLabel} from \
'{(fs.get (fs.lookup 0 (if bold then 700 else 400) italic)).family}'")
    else
      diags := diags.push (Diag.of .N0018
        s!"'{(fs.get idx).family}' has no {a.styleLabel} '{base}' \
(U+{hex c.toNat}); the plain letter stands in"
        (help := "declare a math face that carries it: \\fonts{ math = ... }"))
  return (items, diags, acc.cache, acc.extras, acc.notes)
where
  hex (n : Nat) : String := Id.run do
    let ds := "0123456789ABCDEF".toList
    let mut s := ""
    let mut n := n
    for _ in [0:8] do
      s := String.ofList [ds[n % 16]!] ++ s
      n := n / 16
      if n == 0 then break
    let pad := if s.length < 4 then "".pushn '0' (4 - s.length) else ""
    return pad ++ s

-- Knuth–Plass ------------------------------------------------------------------

def canBreakAt (items : Array Item) (j : Nat) : Bool :=
  match items[j]? with
  | some (.glue _) =>
    match items[j-1]? with
    | some (.box _ _ _ _ _ _ _ _ _) => j > 0
    | some (.img _ _ _) => j > 0
    | some (.rule _ _ _ _) => j > 0
    | _ => false
  | some (.pen _ cost _ _ _ _) => cost < 10000
  | _ => false

structure Measure where
  natural : Sp := 0
  stretch : Sp := 0
  shrink : Sp := 0
  fil : Bool := false
  /-- Total width of the line's font boxes (and the hyphen broken at):
  what font expansion may rescale. Images and rules never scale. -/
  boxW : Sp := 0

/-- Font expansion bound, per-mille of a glyph's width, symmetric:
microtype's own defaults `stretch = 20`, `shrink = 20` (microtype.sty
v3.1, the `\DeclareMicrotypeSet` defaults at lines 229–230), with step 1
as on the modern engines (microtype-luatex.def; the pdfTeX `stretch/5`
step is the legacy fallback). Expansion is a third degree of freedom the
breaker consumes as stretchability (Thành, "Margin kerning and font
expansion with pdfTeX", TUGboat 22(3)). -/
def expandLimit : Nat := 20

/-- Character protrusion factors `(left, right)` in per-mille of the
glyph's own width: how far a line-boundary glyph may hang into the margin
so the optical edge reads straight (Thành, "Margin kerning and font
expansion with pdfTeX", TUGboat 22(3); microtype manual §2). The values
are microtype's `cmr-default` list, mt-cmr.cfg v2.2 (R. Schlicht) — the
generic set microtype itself applies to families without their own
config, which is how one table serves any face here. Curly and double
quotes are the config's `\textquoteleft`-family rows; the dashes its
`\textendash`/`\textemdash`. -/
def protrusionLR (c : Char) : Nat × Nat :=
  match c with
  | 'A' => (50, 50)
  | 'F' => (0, 50)
  | 'J' => (50, 0)
  | 'K' => (0, 50)
  | 'L' => (0, 50)
  | 'T' => (50, 50)
  | 'V' => (50, 50)
  | 'W' => (50, 50)
  | 'X' => (50, 50)
  | 'Y' => (50, 50)
  | 'k' => (0, 50)
  | 'r' => (0, 50)
  | 't' => (0, 70)
  | 'v' => (50, 50)
  | 'w' => (50, 50)
  | 'x' => (50, 50)
  | 'y' => (50, 70)
  | '0' => (0, 50)
  | '1' => (100, 200)
  | '2' => (50, 50)
  | '3' => (50, 50)
  | '4' => (70, 70)
  | '5' => (0, 50)
  | '6' => (0, 50)
  | '7' => (50, 100)
  | '8' => (0, 50)
  | '9' => (0, 50)
  | '.' => (0, 700)
  | ',' => (0, 500)
  | ':' => (0, 500)
  | ';' => (0, 500)
  | '!' => (0, 100)
  | '?' => (0, 200)
  | '@' => (50, 50)
  | '~' => (200, 250)
  | '%' => (50, 50)
  | '*' => (300, 300)
  | '+' => (250, 250)
  | '(' => (300, 0)
  | ')' => (0, 300)
  | '/' => (200, 300)
  | '-' => (400, 500)
  | '–' => (400, 300)
  | '—' => (300, 200)
  | '‘' => (500, 700)
  | '’' => (500, 600)
  | '“' => (500, 300)
  | '”' => (200, 600)
  | _ => (0, 0)

/-- The table never grants a glyph more overhang than its own width: every
entry is under 1000‰ — the source's own largest is the period's 700 right
(mt-cmr.cfg `cmr-default`) — so a protruded boundary glyph always keeps ink
inside the measure and the hang stays within one glyph advance. -/
theorem protrusionLR_covers (c : Char) :
    (protrusionLR c).1 ≤ 1000 ∧ (protrusionLR c).2 ≤ 1000 := by
  unfold protrusionLR
  split <;> decide

/-- How far the line `[a:j)` may hang left of the measure: the left
protrusion of its first glyph, in sp. Kerns (glyphless boxes) and
penalties are passed over; an image or rule at the edge protrudes
nothing. `canBreakAt` puts a box directly before a glue break and a
hyphen pen carries its own glyph, so both boundary scans are O(1) at
every candidate the breaker evaluates. -/
def protrudeLeft (items : Array Item) (a j : Nat) : Sp := Id.run do
  for k in [a:j] do
    match items[k]? with
    | some (.box _ _ _ _ glyphs _ _ _ _) =>
      if let some (_, c, adv) := glyphs[0]? then
        return adv * (protrusionLR c).1 / 1000
    | some (.img ..) | some (.rule ..) => return 0
    | _ => pure ()
  return 0

/-- How far the line breaking at `j` may hang right of the measure: the
right protrusion of its last glyph — the break penalty's own hyphen when
it carries one (the single biggest win: the hyphen protrudes 500‰), else
the last boxed glyph before the break. -/
def protrudeRight (items : Array Item) (a j : Nat) : Sp := Id.run do
  if let some (.pen _ _ _ _ _ glyphs) := items[j]? then
    if let some (_, c, adv) := glyphs.back? then
      return adv * (protrusionLR c).2 / 1000
  for i in [0:j - a] do
    match items[j - 1 - i]? with
    | some (.box _ _ _ _ glyphs _ _ _ _) =>
      if let some (_, c, adv) := glyphs.back? then
        return adv * (protrusionLR c).2 / 1000
    | some (.img ..) | some (.rule ..) => return 0
    | _ => pure ()
  return 0

/-- The largest right overhang any break in `items` can grant: what
`kp`'s deactivation slackens by under protrusion, so a node judged
hopeless at one break cannot become feasible again at a later break
whose boundary glyph protrudes more. -/
def maxProtrudeRight (items : Array Item) : Sp := Id.run do
  let mut best : Sp := 0
  for it in items do
    match it with
    | .box _ _ _ _ glyphs _ _ _ _ =>
      if let some (_, c, adv) := glyphs.back? then
        best := max best (adv * (protrusionLR c).2 / 1000)
    | .pen _ _ _ _ _ glyphs =>
      if let some (_, c, adv) := glyphs.back? then
        best := max best (adv * (protrusionLR c).2 / 1000)
    | _ => pure ()
  return best

def lineStart (items : Array Item) (start : Nat) : Nat := Id.run do
  let mut a := start
  for _ in [a:items.size] do
    match items[a]? with
    | some (.glue _) => a := a + 1
    | some (.pen _ cost _ _ _ _) => if cost ≥ 10000 then break else a := a + 1
    | _ => break
  return a

def measure (items : Array Item) (a j : Nat) (protrude : Bool := false) :
    Measure := Id.run do
  let mut m : Measure := {}
  for k in [a:j] do
    match items[k]! with
    | .box w _ _ _ _ _ _ _ _ =>
      m := { m with natural := m.natural + w, boxW := m.boxW + w }
    | .img _ w _ => m := { m with natural := m.natural + w }
    | .rule w _ _ _ => m := { m with natural := m.natural + w }
    | .glue g => m := { m with
        natural := m.natural + g.width
        stretch := m.stretch + g.stretch
        shrink := m.shrink + g.shrink
        fil := m.fil || g.fil }
    | .pen _ _ _ _ _ _ => pure ()
  if let some (.pen w _ _ _ _ _) := items[j]? then
    m := { m with natural := m.natural + w, boxW := m.boxW + w }
  -- Protrusion, stage 2: the breaker measures a line as it will be set —
  -- boundary glyphs hanging into the margin do not count against the
  -- measure. Fil lines never protrude (`setLine`'s own gate), so the
  -- term drops with fil, and ragged item shapes (all glue fil) are
  -- untouched by construction.
  if protrude && !m.fil then
    m := { m with natural := m.natural - protrudeLeft items a j - protrudeRight items a j }
  return m

/-- What a `Measure`'s font boxes may stretch or shrink beyond the glue,
in sp: the symmetric `expandLimit` fraction of the expandable width, zero
on a fil line (which never expands, as it never protrudes). -/
def Measure.ex (m : Measure) (expand : Bool) : Sp :=
  if expand && !m.fil then m.boxW * expandLimit / 1000 else 0

def overfullDemerits : Int := 100000000

/-- Demerits of one candidate line. Under font expansion the badness
denominators grow by the boxes' own flexibility (`Measure.ex`): the form
of the cost is unchanged, expansion is only more room (Thành tb71 —
expansion gives a font "stretchability and shrinkability … used by the
line-breaking engine"). -/
def lineDemerits (items : Array Item) (m : Measure) (target : Sp) (j : Nat)
    (expand : Bool := false) : Int :=
  let ex := m.ex expand
  let delta := target - m.natural
  let b : Int :=
    if delta == 0 then 0
    else if delta > 0 then
      if m.fil then 0 else badness delta (m.stretch + ex)
    else
      if m.shrink + ex < -delta then -1  -- overfull marker
      else badness delta (m.shrink + ex)
  let base : Int :=
    if b < 0 then overfullDemerits + (m.natural - target)
    else (10 + b) ^ 2
  let penTerm : Int :=
    match items[j]? with
    | some (.pen _ cost _ _ _ _) =>
      if cost ≤ forcedCost then 0
      else if cost > 0 then cost ^ 2
      else -(cost ^ 2)
    | _ => 0
  base + penTerm

def isForced (items : Array Item) (k : Nat) : Bool :=
  match items[k]? with
  | some (.pen _ cost _ _ _ _) => cost ≤ forcedCost
  | _ => false

def isFlagged (items : Array Item) (k : Nat) : Bool :=
  match items[k]? with
  | some (.pen _ _ flagged _ _ _) => flagged
  | _ => false

def doubleHyphenDemerits : Int := 10000

/-- Demerits added when the second-last line of a paragraph ends in a
hyphen (TeXbook ch. 14, `\finalhyphendemerits`; the plain/LaTeX default
5000): a hyphen carrying into the paragraph's last line reads worst. -/
def finalHyphenDemerits : Int := 5000

/-- Prefix sums over item width/stretch/shrink/fil/forced counts, one slot
past the end, so `kp` measures any line by differencing. -/
structure KpSums where
  w : Array Sp
  s : Array Sp
  k : Array Sp
  f : Array Nat
  forced : Array Nat
  /-- Prefix sums of font-box widths: the expandable width of any line by
  differencing, scaled once at the read so it cannot drift from
  `measure`'s own accumulation. -/
  b : Array Sp

def kpSums (items : Array Item) : KpSums := Id.run do
  let n := items.size
  let mut pw : Array Sp := Array.mkEmpty (n + 1)
  let mut ps : Array Sp := Array.mkEmpty (n + 1)
  let mut pk : Array Sp := Array.mkEmpty (n + 1)
  let mut pf : Array Nat := Array.mkEmpty (n + 1)
  let mut pforced : Array Nat := Array.mkEmpty (n + 1)
  let mut pb : Array Sp := Array.mkEmpty (n + 1)
  let mut btot : Sp := 0
  pw := pw.push 0
  ps := ps.push 0
  pk := pk.push 0
  pf := pf.push 0
  pforced := pforced.push 0
  pb := pb.push 0
  for k in [0:n] do
    let (dw, dst, dsh, dfil, db) : Sp × Sp × Sp × Nat × Sp := match items[k]! with
      | .box w _ _ _ _ _ _ _ _ => (w, 0, 0, 0, w)
      | .img _ w _ => (w, 0, 0, 0, 0)
      | .rule w _ _ _ => (w, 0, 0, 0, 0)
      | .glue g => (g.width, g.stretch, g.shrink, if g.fil then 1 else 0, 0)
      | .pen _ _ _ _ _ _ => (0, 0, 0, 0, 0)
    pw := pw.push (pw[k]! + dw)
    ps := ps.push (ps[k]! + dst)
    pk := pk.push (pk[k]! + dsh)
    pf := pf.push (pf[k]! + dfil)
    pforced := pforced.push (pforced[k]! + (if isForced items k then 1 else 0))
    btot := btot + db
    pb := pb.push btot
  return { w := pw, s := ps, k := pk, f := pf, forced := pforced, b := pb }

/-- The line measure `kp` uses: prefix-sum differences over [a:j) plus the
width of the penalty broken at, less the protrusion boundary term when the
breaker is protruding. Must agree with `measure` wherever `kp` evaluates
it; `scripts/kp-fuzz.lean` holds it to that. -/
def kpMeasure (items : Array Item) (sums : KpSums) (a j : Nat)
    (protrude : Bool := false) : Measure :=
  let penW : Sp := match items[j]? with
    | some (.pen w _ _ _ _ _) => w
    | _ => 0
  let m : Measure :=
    { natural := sums.w[j]! - sums.w[a]! + penW
      stretch := sums.s[j]! - sums.s[a]!
      shrink := sums.k[j]! - sums.k[a]!
      fil := sums.f[j]! - sums.f[a]! > 0
      boxW := (sums.b[j]?.getD 0) - (sums.b[a]?.getD 0) + penW }
  if protrude && !m.fil then
    { m with natural := m.natural - protrudeLeft items a j - protrudeRight items a j }
  else m

/-- Optimal breakpoints by dynamic programming over break positions, with
prefix-sum line measures and an active list: a node whose line to the
current position is already overfull beyond shrink can only get worse, so
it is considered one last time and then deactivated (one node is always
retained so a solution exists even for unbreakable content). -/
def kp (items : Array Item) (target : Sp) (protrude : Bool := false)
    (expand : Bool := false) : Array Nat := Id.run do
  let n := items.size
  let sums := kpSums items
  let measureAt (a j : Nat) : Measure := kpMeasure items sums a j protrude
  -- Under protrusion the deactivation test slackens by the largest right
  -- overhang any break can grant: a node overfull beyond shrink at this
  -- break could otherwise become feasible again at a later break whose
  -- boundary glyph protrudes more, and dropping it would lose the
  -- optimum kp-fuzz checks against.
  let slack : Sp := if protrude then maxProtrudeRight items else 0
  let mut best : Array (Option (Int × Nat)) := Array.replicate (n + 1) none
  best := best.set! n (some (0, n))
  let mut active : Array Nat := #[n]
  for j in [0:n] do
    if canBreakAt items j then
      let mut bestHere : Option (Int × Nat) := none
      let mut survivors : Array Nat := #[]
      let mut bestDroppedPlain : Option (Int × Nat) := none
      let mut bestDroppedFlagged : Option (Int × Nat) := none
      for p in active do
        if p == n || p < j then
          let a := lineStart items (if p == n then 0 else p + 1)
          let spansForced := a < j && sums.forced[j]! - sums.forced[a]! > 0
          if !spansForced && a ≤ j then
            match best[p]! with
            | some (d0, _) =>
              let m := measureAt a j
              let dbl := if p != n && isFlagged items p && isFlagged items j then
                doubleHyphenDemerits else 0
              let fin := if p != n && isFlagged items p && j == n - 1 then
                finalHyphenDemerits else 0
              let d := d0 + lineDemerits items m target j expand + dbl + fin
              match bestHere with
              | some (dBest, _) =>
                if d < dBest then bestHere := some (d, p)
              | none => bestHere := some (d, p)
              -- Once overfull beyond shrink, this predecessor only gets
              -- worse. Keep the best one per flagged state because that is
              -- the only predecessor property future line costs observe.
              -- The shrink read is the *expanded* shrink: pruning against
              -- the bare glue would drop predecessors expansion could
              -- still save (kp-fuzz catches the violation).
              if m.natural - (m.shrink + m.ex expand) > target + slack then
                if p != n && isFlagged items p then
                  match bestDroppedFlagged with
                  | some (dD, _) =>
                    if d < dD then bestDroppedFlagged := some (d, p)
                  | none => bestDroppedFlagged := some (d, p)
                else
                  match bestDroppedPlain with
                  | some (dD, _) =>
                    if d < dD then bestDroppedPlain := some (d, p)
                  | none => bestDroppedPlain := some (d, p)
              else
                survivors := survivors.push p
            | none => pure ()
          else if !spansForced then
            survivors := survivors.push p
        else
          survivors := survivors.push p
      if bestHere.isSome then
        best := best.set! j bestHere
        survivors := survivors.push j
      -- Overfull predecessors keep their relative order as j grows. One per
      -- flagged state preserves the optimum (double-hyphen demerits are the
      -- only future cost that distinguishes the two classes).
      if let some (_, p) := bestDroppedPlain then
        survivors := survivors.push p
      if let some (_, p) := bestDroppedFlagged then
        survivors := survivors.push p
      active := survivors
  let last := n - 1
  let mut breaks : Array Nat := #[]
  match best[last]! with
  | none => return #[]
  | some _ =>
    let mut cur := last
    for _ in [0:n + 1] do
      breaks := breaks.push cur
      match best[cur]! with
      | some (_, p) =>
        if p == n then break
        cur := p
      | none => break
    return breaks.reverse

/-- TeX's `\pretolerance` (plain.tex sets 100): the badness bound the
hyphenless first pass must meet, per line, for its breaks to stand. -/
def pretolerance : Nat := 100

/-- Two-pass breaking, TeX's own shape (TeXbook ch. 14: with a
non-negative `\pretolerance` the paragraph is first broken without
hyphenation, and the hyphenating pass runs only when that attempt fails):
hyphenation points are sealed (a 10000 cost is never a legal break,
`canBreakAt`), the optimal hyphenless breaks stand when every line's
badness stays within `pretolerance` and nothing is overfull, and only a
paragraph that fails gets the hyphenating pass. This is what keeps
hyphens rare — a paragraph that sets cleanly without them never
hyphenates, whatever small demerit gain a hyphen could buy. Explicit
hyphens (unflagged pens) and forced breaks keep their pens. -/
def kpTwoPass (items : Array Item) (target : Sp) (protrude : Bool := false)
    (expand : Bool := false) : Array Nat := Id.run do
  let sealable : Item → Bool := fun it => match it with
    | .pen _ cost flagged _ _ _ => flagged && forcedCost < cost && cost < 10000
    | .box .. | .glue .. | .img .. | .rule .. => false
  if !items.any sealable then return kp items target protrude expand
  let plain := items.map fun it => match it with
    | .pen w cost flagged f c g =>
      if flagged && forcedCost < cost && cost < 10000 then .pen w 10000 flagged f c g
      else .pen w cost flagged f c g
    | .box .. | .glue .. | .img .. | .rule .. => it
  let breaks := kp plain target protrude expand
  if breaks.isEmpty then return kp items target protrude expand
  let mut prev := plain.size
  for j in breaks do
    let a := lineStart plain (if prev == plain.size then 0 else prev + 1)
    let m := measure plain a j protrude
    let ex := m.ex expand
    let delta := target - m.natural
    let bad : Int :=
      if delta == 0 then 0
      else if delta > 0 then (if m.fil then 0 else badness delta (m.stretch + ex))
      else if m.shrink + ex < -delta then (pretolerance : Int) + 1
      else badness delta (m.shrink + ex)
    if bad > (pretolerance : Int) then
      return kp items target protrude expand
    prev := j
  return breaks

-- Line setting ----------------------------------------------------------------

/-- The uniform expansion factor a set line applies to its font boxes, in
per-mille: expansion-first, the fonts absorb what they can of the line's
delta up to `expandLimit` in either direction, and glue takes the
remainder — Thành's design, where expansion is chosen to bring the glue
setting closest to natural (TUGboat 22(3)). One factor per line, never
per glyph, so glyphs are only rescaled, never re-ordered. -/
def expandFactor (delta boxW : Int) : Int :=
  if boxW > 0 && delta != 0 then
    min (max (delta * 1000 / boxW) (-(expandLimit : Int))) (expandLimit : Int)
  else 0

/-- Every set line's expansion factor stays inside microtype's bounds:
±`expandLimit` per-mille, whatever the line's delta and expandable width.
Uniformity per line is by construction — `setLine` computes one factor
and applies it to every box. -/
theorem expandFactor_bounded (delta boxW : Int) :
    -(expandLimit : Int) ≤ expandFactor delta boxW ∧
      expandFactor delta boxW ≤ (expandLimit : Int) := by
  unfold expandFactor expandLimit
  split <;> omega

private def setLine (items : Array Item) (a j : Nat) (target : Sp)
    (justify : Bool) (protrude : Bool := false) (expand : Bool := false) :
    Array Seg × Sp × Bool × Sp × Int := Id.run do
  let m := measure items a j
  -- Protrusion (stage 1): boundary glyphs hang into the margin by the
  -- table's fraction of their own width, so the optical edge is straight.
  -- The line is set against the enlarged target and the caller shifts its
  -- x left by the returned hang, so interior glue absorbs exactly the
  -- overhang. Lines with fil keep their exact margins: a last line or
  -- an `\hfill` row never reaches the edge, so nothing is gained there
  -- and a dates row set flush stays flush.
  let doProt := protrude && justify && !m.fil
  let leftHang := if doProt then protrudeLeft items a j else 0
  let target := target + leftHang + (if doProt then protrudeRight items a j else 0)
  let delta := target - m.natural
  -- Font expansion: one bounded factor per line takes its share of the
  -- delta first; the glue arms below distribute what remains. Fil lines
  -- never expand, as they never protrude.
  let f : Int := if expand && justify && !m.fil then expandFactor delta m.boxW else 0
  let mut boxTaken : Sp := 0
  if f != 0 then
    for k in [a:j] do
      if let some (.box w _ _ _ _ _ _ _ _) := items[k]? then
        boxTaken := boxTaken + w * f / 1000
    if let some (.pen w _ _ _ _ _) := items[j]? then
      boxTaken := boxTaken + w * f / 1000
  let delta := delta - boxTaken
  let mut overfull := false
  -- Fill glue shares the leftover, but a line-running fill does not count as a
  -- sharer when the author wrote their own `\hfill`: otherwise
  -- `name \hfill dates` on a paragraph's last line puts the dates halfway to
  -- the margin instead of at it, which is what LaTeX does and what nobody
  -- setting a row of dates wants.
  let mut explicitFils := 0
  let mut allFils := 0
  for k in [a:j] do
    if let some (.glue g) := items[k]? then
      if g.fil then
        allFils := allFils + 1
        unless g.parfill do explicitFils := explicitFils + 1
  let fils := if explicitFils > 0 then explicitFils else allFils
  let mut segs : Array Seg := #[]
  let mut width : Sp := 0
  for k in [a:j] do
    match items[k]! with
    | .box w fontIdx color link glyphs size underline raise ground =>
      -- The declared width is authoritative, as it already is in `measure`: a
      -- kern is a box with a width and no glyphs, and recomputing from the
      -- advances would silently set it to zero. Expansion rescales the box
      -- by the line's one factor; the PDF writer paints the run's glyphs
      -- under the same horizontal scale.
      let w := w + w * f / 1000
      segs := segs.push
        (.run fontIdx color link w (glyphs.map fun (g, c, _) => (g, c)) size underline raise
          ground)
      width := width + w
    | .img idx w h =>
      segs := segs.push (.image idx w h)
      width := width + w
    | .rule w thickness raise color =>
      segs := segs.push (.rule w thickness raise color)
      width := width + w
    | .glue g =>
      let setW : Sp :=
        if !justify then
          g.width
        else if delta == 0 then
          g.width
        else if delta > 0 then
          if fils > 0 then
            if g.fil then g.width + delta / fils else g.width
          else if m.stretch > 0 then
            g.width + delta * g.stretch / m.stretch
          else
            g.width
        else
          if m.shrink > 0 then
            let d := max delta (-m.shrink)
            g.width + d * g.shrink / m.shrink
          else
            g.width
      if m.shrink < -delta then
        overfull := true
      segs := segs.push (.gap (max 0 setW))
      width := width + max 0 setW
    | .pen _ _ _ _ _ _ => pure ()
  -- breaking at a penalty appends its glyphs (the hyphen)
  if let some (.pen w _ _ fontIdx color glyphs) := items[j]? then
    if !glyphs.isEmpty then
      -- A hyphenation point sits inside a word, so the hyphen is set at the
      -- size (and under the underline) of the run it interrupts — and under
      -- the line's expansion factor, like any glyph.
      let w := w + w * f / 1000
      let (inherited, inheritedUl, inheritedGr) := segs.foldl (fun acc s => match s with
        | .run _ _ _ _ _ sz ul _ gr => (if sz != 0 then sz else acc.1, ul, gr)
        | _ => acc) ((0 : Sp), false, (none : Option Ir.Color))
      segs := segs.push
        (.run fontIdx color none w (glyphs.map fun (g, c, _) => (g, c)) inherited inheritedUl 0
          inheritedGr)
      width := width + w
  -- drop trailing gaps (paragraph-final fill)
  let mut segs' := segs
  repeat
    match segs'.back? with
    | some (.gap w) =>
      segs' := segs'.pop
      width := width - w
    | _ => break
  return (segs', width, overfull, leftHang, f)

-- Page assembly ----------------------------------------------------------------

/-- One footnote, set and ready to ship: its lines with `y` measured from
the note block's own top (the first line's `\footnotesep` strut top), and
the block's total height — strut top to last ink bottom. Built where the
paragraph is collected (`collectPara`), attached to the open page when the
mark's line commits (`B.attachNotes`), shipped whole by the
bottom-anchored flush in `finishPage`. -/
private structure NoteBlock where
  lines : Array LineOut
  height : Sp
  deriving Repr, Inhabited

/-- The lowest y body ink may reach on a page carrying `h` of note ink:
the note block and the `\skip\footins` gap above it come out of the text
block's bottom; with no notes the floor is `bodyBottom` itself. Every
placement fit test on a noted page reads the bottom from here. -/
private def noteFloor (geom : Geom) (footins h : Sp) : Sp :=
  if h == 0 then geom.bodyBottom else geom.bodyBottom - h - footins


/-- Page assembly state. A page is set the way a line is: its lines are
boxes, the vertical skips between them are glue, and `y` is the baseline of
the last line at the glue's natural size. Shrink is applied to the whole
page when it closes, so `shrinkAbove` remembers, per line, how much glue
above it can give. -/
private structure B where
  geom : Geom
  ascent : Sp
  descent : Sp
  /-- Body cap height in sp: the height of a line as TeX would measure it
  from its glyphs. `ascent` reserves room for accents and would push every
  line apart. -/
  capHeight : Sp
  /-- Body x-height in sp, so `ex` tokens resolve against the real font. -/
  xHeight : Sp := 0
  pages : Array PageOut := #[]
  cur : PageOut := {}
  /-- Baseline of the last line placed, at natural glue. -/
  y : Sp := 0
  /-- Ink depth of the last line placed (metric descent per run): what
  furniture, pictures, and the page bottom clear against. -/
  prevDepth : Sp := 0
  /-- Leaded below of the last line placed (`LineBox.below`): the upper
  term of the metric interline rule. -/
  prevBelow : Sp := 0
  /-- The last line placed was bare rule ink (`ruleOnly`): the next
  interline is ink-referenced — from the rule's bottom edge to the
  next line's cap line (`interlineFor`). -/
  prevRuleOnly : Bool := false
  /-- Vertical glue since the last line, not yet laid. -/
  skip : Glue := {}
  /-- Per line of the current page: total shrink in the glue above it. -/
  shrinkAbove : Array Sp := #[]
  /-- Total shrink in the glue laid on the current page. -/
  pageShrink : Sp := 0
  /-- How far the current page overflows at natural glue: what closing it
  must take out of the shrink. -/
  needed : Sp := 0
  /-- The next line opens at the page top, even though lines already stand
  on the page: a later column rewound to a fresh page's start must place
  its first line where the first column placed its. -/
  freshStart : Bool := false
  /-- A float group is being replayed on the page that holds it whole
  (`runFloat`): a line that would not fit commits anyway instead of
  breaking, because the group's one legal position has already been
  decided — the page bottom may be honestly overrun (W0358), never a
  silent split. -/
  noBreak : Bool := false
  /-- Background of the page being built, from `.pageStyle`; reset when it
  closes. -/
  pageBg : Option Ir.Color := none
  /-- Background every page gets: the palette's `bg`, when declared. A
  page's own `.pageStyle` background wins. -/
  docBg : Option Ir.Color := none
  /-- How the page being built distributes its leftover vertical space;
  reset when it closes. `.top` (all leftover below) is the undeclared
  default; a standout frame or section page sets `.center`. -/
  vdist : VDist := .top
  /-- Fil units seen on this page so far: each consumed vertical skip
  carrying TeX's first-order infinite stretch counts one. When any exist,
  they own the leftover (`filShare`) and the ratio distribution stands
  aside. -/
  pageFils : Nat := 0
  /-- Per placed line, the fil units above it — parallel to `shrinkAbove`. -/
  filsAbove : Array Nat := #[]
  /-- The chrome footer for pages closed from here on, from `.foot` ops. -/
  curFoot : Option (Array Ir.BandSlot) := none
  /-- The bottom edge of the open page's `.titleBar` fill, for
  `PageOut.band`: written where the bar paints, cleared with the page. -/
  curBand : Option Sp := none
  /-- The countable frame owning pages closed from here on, from the same
  `.foot` ops: written onto each closing page (`finishPage`), so the
  attribution and the footer can only move together. -/
  curFrame : Option Nat := none
  /-- Lines and fills already on the page when `.pin` arrived: page-top
  chrome (the frame title and its bar) the distribution never moves. -/
  pinnedLines : Nat := 0
  pinnedFills : Nat := 0
  /-- The frame's page-top chrome, snapshotted at `.pin`: the title lines
  and bar fills with the baseline and depth content resumes below —
  repeated on every continuation page the frame spills onto (`spillPage`),
  as beamer repeats the frametitle on every page of a broken frame
  (`allowframebreaks`, user guide §8.1: the title is per-frame furniture,
  not first-page content). Cleared at the deliberate frame boundary
  (`.brk`), so only mid-frame overflow repeats it. -/
  chrome : Option (Array LineOut × Array Fill × Sp × Sp × Sp) := none
  /-- Anchors owed to the next committed line: `commit` records each with
  the index of the page that line lands on. -/
  pendingAnchors : Array String := #[]
  /-- Each resolved anchor with its 0-based page index, first declaration
  first — the table the outline's in-document targets resolve against. -/
  anchors : Array (String × Nat) := #[]
  /-- The resolved `\skip\footins` gap for this run — `Ir.footinsDefault`
  or the document's `\tokens{ footins = ... }` — fixed at `Layout.run`. -/
  footins : Sp := 0
  /-- The footnote rule's ink colour: the design's `fg`. -/
  noteInk : Ir.Color := Ir.Color.black
  /-- Footnote lines committed to the open page, y relative to the note
  block's top: the bottom-anchored flush in `finishPage` ships them. A
  note enters only through `attachNotes`, in the same step as its mark's
  committed line — `placeLine_note_with_mark`'s statement. -/
  pendingNotes : Array LineOut := #[]
  /-- Total height of the pending note block (strut tops to ink bottoms):
  what the fit test in `placeLine` reserves above `bodyBottom`. -/
  notesH : Sp := 0
  diags : Array Diag := #[]

/-- Attach a committed line's notes to the open page: each note's lines
join `pendingNotes` shifted below what already stands, whole — no branch
anywhere splits a `NoteBlock`. Called only beside `B.commit`, so a note
and its mark's line enter the builder in one step
(`placeLine_note_with_mark`). -/
private def B.attachNotes (b : B) (notes : Array NoteBlock) : B :=
  if notes.isEmpty then b
  else notes.foldl (fun b nb =>
    { b with pendingNotes := b.pendingNotes
               ++ nb.lines.map (fun l => { l with y := l.y + b.notesH })
             notesH := b.notesH + nb.height }) b

/-- W0372: the note block plus its mark's line reach below the text
block's floor even on a fresh page — the note ships whole and the page is
honestly overrun (the W0358 shape), never silently truncated or split. -/
private def B.warnNoteOverrun (b : B) (y inkBelow : Sp) : B :=
  let over := y + inkBelow - noteFloor b.geom b.footins b.notesH
  if b.notesH > 0 && over > 0 then
    { b with diags := b.diags.push (Diag.of .W0372
        (s!"a footnote is {over.toPtString}pt taller than the text block; " ++
          "it overruns its page")
        (help := "shorten the note, or raise the text height (\\page{ vmargin = ... })")) }
  else b

@[simp] private theorem attachNotes_pages (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).pages = b.pages := by
  unfold B.attachNotes
  split
  · rfl
  · exact Array.foldl_induction (motive := fun _ (acc : B) => acc.pages = b.pages)
      rfl (fun _ _ h => h)

@[simp] private theorem attachNotes_noBreak (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).noBreak = b.noBreak := by
  unfold B.attachNotes
  split
  · rfl
  · exact Array.foldl_induction (motive := fun _ (acc : B) => acc.noBreak = b.noBreak)
      rfl (fun _ _ h => h)

@[simp] private theorem attachNotes_cur (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).cur = b.cur := by
  unfold B.attachNotes
  split
  · rfl
  · exact Array.foldl_induction (motive := fun _ (acc : B) => acc.cur = b.cur)
      rfl (fun _ _ h => h)

/-- Attaching keeps every note line: whatever already pends survives the
append, and each attached note's lines land whole (segs intact, y
restacked). -/
private theorem attachNotes_mem (b : B) (ns : Array NoteBlock)
    (nb : NoteBlock) (hnb : nb ∈ ns) (l : LineOut) (hl : l ∈ nb.lines) :
    ∃ l' ∈ (b.attachNotes ns).pendingNotes, l'.segs = l.segs := by
  unfold B.attachNotes
  split
  · next hemp =>
    rw [Array.isEmpty_iff] at hemp
    subst hemp
    simp at hnb
  · obtain ⟨j, hj, hje⟩ := Array.mem_iff_getElem.mp hnb
    exact Array.foldl_induction
      (motive := fun n (acc : B) => j < n →
        ∃ l' ∈ acc.pendingNotes, l'.segs = l.segs)
      (fun h => absurd h (Nat.not_lt_zero j))
      (fun i acc ih hji => by
        rcases Nat.lt_or_ge j i.val with hlt | hge
        · obtain ⟨l', hl', hseg⟩ := ih hlt
          exact ⟨l', Array.mem_append.mpr (Or.inl hl'), hseg⟩
        · have hji' : j = i.val := Nat.le_antisymm (Nat.lt_succ_iff.mp hji) hge
          refine ⟨{ l with y := l.y + acc.notesH },
            Array.mem_append.mpr (Or.inr (Array.mem_map.mpr ⟨l, ?_, rfl⟩)), rfl⟩
          subst hji'
          exact hje ▸ hl) hj

@[simp] private theorem warnNoteOverrun_pages (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).pages = b.pages := by
  simp only [B.warnNoteOverrun]
  split <;> rfl

@[simp] private theorem warnNoteOverrun_noBreak (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).noBreak = b.noBreak := by
  simp only [B.warnNoteOverrun]
  split <;> rfl

@[simp] private theorem warnNoteOverrun_cur (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).cur = b.cur := by
  simp only [B.warnNoteOverrun]
  split <;> rfl

@[simp] private theorem warnNoteOverrun_pendingNotes (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).pendingNotes = b.pendingNotes := by
  simp only [B.warnNoteOverrun]
  split <;> rfl

/-- The note block as it ships: the footnote rule, then every pending note
line, bottom-anchored — the block's bottom at `bodyBottom`, the rule in
the `footins` gap above the block. The rule follows the source and the
type: `\footnoterule` is a 0.4pt rule over 0.4\columnwidth whose
net-zero kerns place it 2.6pt clear of the notes (ltmiscen.dtx), read
here as 0.04 em and 0.26 em of the body size — the heading rule's
precedent of a sourced absolute following the type. Empty when no note is
pending, so an unnoted page ships exactly what it always shipped. One
`++` per page close, bounded, never a walk's accumulator. -/
private def B.noteLines (b : B) : Array LineOut :=
  if b.pendingNotes.isEmpty then #[] else
    let top := b.geom.bodyBottom - b.notesH
    let thick := b.geom.fontSize * 4 / 100
    let ruleW := b.geom.textWidth * 2 / 5
    let rule : LineOut := { x := b.geom.hmargin
                            y := top - b.geom.fontSize * 26 / 100
                            size := 0
                            segs := #[.rule ruleW thick 0 b.noteInk]
                            setWidth := ruleW
                            note := true }
    #[rule] ++ b.pendingNotes.map (fun l => { l with y := top + l.y, note := true })

/-- `note_whole`: every pending note line ships in the one closing page's
note block — `noteLines` carries each with only its y moved (and the rule
beside them), so no note is ever split across pages. TeX's split
insertions (TeXbook ch. 15) are refused by design: whole-or-move,
`runFloat`'s rule; a note that cannot fit moved with its mark's line
(`placeLine`'s spill path), and one taller than the text block shipped
whole with W0372 naming the overrun. -/
private theorem note_whole (b : B) :
    ∀ l ∈ b.pendingNotes, ∃ l' ∈ b.noteLines, l'.segs = l.segs ∧ l'.note = true := by
  intro l hl
  unfold B.noteLines
  split
  · next hemp =>
    rw [Array.isEmpty_iff] at hemp
    rw [hemp] at hl
    simp at hl
  · exact ⟨_, Array.mem_append.mpr (Or.inr (Array.mem_map.mpr ⟨l, hl, rfl⟩)),
      rfl, rfl⟩

/-- Close the current page. A page that overflowed at natural size within
its shrink is set to fit: every line moves up by its share of the shrink
above it, the glue set at one ratio like a justified line's. -/
private def B.finishPage (b : B) : B :=
  let lines := if b.needed > 0 && b.pageShrink > 0 then
      (b.cur.lines.zip b.shrinkAbove).map fun (l, above) =>
        { l with y := l.y - above * b.needed / b.pageShrink }
    else b.cur.lines
  let diags := if b.needed > 0 then b.diags.push (Diag.of .N0200
      (s!"page {b.pages.size + 1} set {b.needed / 65536}pt short: its skips gave " ++
        s!"{b.needed * 100 / b.pageShrink}% of their {b.pageShrink / 65536}pt of shrink"))
    else b.diags
  -- The leftover between the content's bottom and the bottom margin. Fil
  -- glue owns it when any stands on the page: each line moves by its
  -- share (`filShare`) — the \vspace{\fill} sandwich centres, a leading
  -- \vfill bottom-flushes, exactly TeX's infinite-glue model. A trailing
  -- pending fil (a \vfill nothing follows) joins the denominator. With no
  -- fil, the page's declared ratio (`VDist`) splits it as before. Only
  -- what follows the `.pin` mark moves; the page's fills ride together
  -- with the shift of the last line, which is exact whenever the fil
  -- glue brackets the content whole.
  let pageFils := b.pageFils + (if b.skip.fil then 1 else 0)
  let leftover := if lines.size > b.pinnedLines then
      let lastY := lines.foldl (fun m l => max m l.y) 0
      -- the vertical distribution fills down to the note block's top, so
      -- flush or centred bottoms never move a note (they are appended
      -- after the shift, anchored at bodyBottom)
      noteFloor b.geom b.footins b.notesH - (lastY + b.prevDepth)
    else 0
  let (lines, delta) := if pageFils > 0 then
      (lines.mapIdx fun i l =>
        if i < b.pinnedLines then l
        else { l with y := l.y + filShare leftover (b.filsAbove.getD i 0) pageFils },
       filShare leftover (b.filsAbove.back?.getD 0) pageFils)
    else
      let d := b.vdist.aboveShare leftover
      (if d == 0 then lines else
        lines.mapIdx fun i l => if i < b.pinnedLines then l else { l with y := l.y + d },
       d)
  let fills := if delta == 0 then b.cur.fills else
    b.cur.fills.mapIdx fun i f => if i < b.pinnedFills then f else { f with y := f.y + delta }
  let fills := match b.pageBg.orElse (fun _ => b.docBg) with
    | some c => #[({ x := 0, y := 0, w := b.geom.pageW, h := b.geom.pageH,
                     color := c } : Fill)] ++ fills
    | none => fills
  -- Picture paths ride with the fills: the same vertical-distribution
  -- shift, no pinning (chrome never draws one).
  let paths := if delta == 0 then b.cur.paths else
    b.cur.paths.map fun p =>
      { p with path := match p.path with
          | .circle cx cy r => .circle cx (cy + delta) r
          | .rect x y w h => .rect x (y + delta) w h
          | .segs segs => .segs (segs.map fun sg => match sg with
              | .line x1 y1 x2 y2 => .line x1 (y1 + delta) x2 (y2 + delta)
              | .cubic x1 y1 c1x c1y c2x c2y x2 y2 =>
                .cubic x1 (y1 + delta) c1x (c1y + delta) c2x (c2y + delta)
                  x2 (y2 + delta))
          | .tri x1 y1 x2 y2 x3 y3 =>
            .tri x1 (y1 + delta) x2 (y2 + delta) x3 (y3 + delta) }
  -- The bottom-anchored flush: the pending notes (and their rule) join
  -- the page after the vertical distribution moved the body lines, so
  -- the distribution can never move a note.
  { b with pages := b.pages.push { lines := lines ++ b.noteLines, fills := fills,
                                   paths := paths, foot := b.curFoot,
                                   frame := b.curFrame, band := b.curBand },
           cur := {}, curBand := none,
           shrinkAbove := #[], pageShrink := 0, needed := 0, skip := {},
           pageBg := none, vdist := .top, pageFils := 0, filsAbove := #[],
           pinnedLines := 0, pinnedFills := 0,
           pendingNotes := #[], notesH := 0,
           diags := diags }

/-- A y-only rewrite keeps every line's segs: the projection both closing
transformations (the shrink zip and the distribution `mapIdx`) satisfy. -/
private theorem map_segs_mapIdx (xs : Array LineOut) (f : Nat → LineOut → LineOut)
    (hf : ∀ i l, (f i l).segs = l.segs) :
    (xs.mapIdx f).map (·.segs) = xs.map (·.segs) := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [hf]

private theorem map_segs_zip (xs : Array LineOut) (sh : Array Sp)
    (hsz : sh.size = xs.size) (f : LineOut × Sp → LineOut)
    (hf : ∀ p, (f p).segs = p.1.segs) :
    ((xs.zip sh).map f).map (·.segs) = xs.map (·.segs) := by
  apply Array.ext
  · simp [hsz]
  · intro i h1 h2
    simp [hf]

/-- `footnote_with_mark`, the ship half: the one page `finishPage` pushes
carries every committed line — the mark's among them — and then the whole
note block, segs intact: the close's transformations (shrink, the vertical
distribution, fil glue) move only y, and the notes join after them,
bottom-anchored. With `placeLine`'s attach (a mark's line and its notes
enter `cur`/`pendingNotes` in one step, both spilling together when the
line does) and `stepStaged_extends` (a shipped page never changes), a
committed line carrying mark k has note k's first line on its own page
index. The census tests over `Layout.Out` are the realisation check, as
`float_whole`'s are. Sourced as the behaviour is: a LaTeX footnote is an
insertion on the page of its mark (TeXbook ch. 15; ltmiscen.dtx's
`\@makecol` builds the page as body then rule then notes). -/
private theorem footnote_with_mark (b : B)
    (hs : b.shrinkAbove.size = b.cur.lines.size) :
    (b.finishPage.pages.back?.map fun p => p.lines.map (·.segs)) =
      some (b.cur.lines.map (·.segs) ++ b.noteLines.map (·.segs)) := by
  simp only [B.finishPage, Array.back?_push, Option.map_some, Option.some.injEq,
    Array.map_append]
  congr 1
  repeat' split
  all_goals
    first
    | rfl
    | (exact map_segs_zip _ _ hs _ (fun p => rfl))
    | (refine map_segs_mapIdx _ _ ?_
       intro i l
       split <;> rfl)
    | (refine (map_segs_mapIdx _ _ ?_).trans
        (map_segs_zip _ _ hs _ (fun p => rfl))
       intro i l
       split <;> rfl)

/-- Reopen the frame's page-top chrome on a fresh page: the pinned title
lines and bar fills repeat, and content resumes below the chrome's own
baseline and depth. The repeated lines never move (they are the new
page's pin) and carry no shrink or fil share. -/
private def B.reopenChrome (b : B) : B :=
  match b.chrome with
  | some (lines, fills, y0, d0, bl0) =>
    { b with cur := { lines := lines, fills := fills }
             pinnedLines := lines.size
             pinnedFills := fills.size
             shrinkAbove := .replicate lines.size 0
             filsAbove := .replicate lines.size 0
             y := y0
             prevDepth := d0
             prevBelow := bl0
             -- The chrome's last line is the frame title's text, never a
             -- bare rule: the resumed interline is the metric rule.
             prevRuleOnly := false }
  | none => b

/-- Close an overfull page mid-frame and repeat the frame's chrome on the
next. Where no chrome is set — an article page, a plain or standout
frame — this is exactly `finishPage`. -/
private def B.spillPage (b : B) : B :=
  b.finishPage.reopenChrome

@[simp] private theorem reopenChrome_pages (b : B) :
    b.reopenChrome.pages = b.pages := by
  unfold B.reopenChrome
  split <;> rfl

/-- A spill ships exactly the page `finishPage` ships: the chrome reopen
only seeds the next page's `cur`, so every pages-extension fact about
`finishPage` transports. -/
@[simp] private theorem spillPage_pages (b : B) :
    b.spillPage.pages = b.finishPage.pages := by
  unfold B.spillPage
  simp

/-- The rider door: content that joins the open page with no vertical
negotiation — no skip, no depth, no page close. A sibling `line` shares
its baseline with the last committed one (an underline row, a picture's
label) and rides with it when the page is set short: its share of the
page's shrink is the last line's unless the rider declares its own
(`shrink` — a picture's label rides the picture's), and a
declared-shrink rider, like the picture it rides, holds no fil entry.
`fills` and `paths` paint behind what already stands (a title or block
bar, a progress track, a picture's shapes). With `commit` and
`finishPage` this is the third and last writer of the page being built:
`cur.lines`, `cur.fills`, and `cur.paths` grow nowhere else
(`reopenChrome` seeds a fresh page's repeated chrome whole; it appends
to nothing). -/
private def B.pushSibling (b : B) (line : Option LineOut := none)
    (fills : Array Fill := #[]) (paths : Array PathOut := #[])
    (shrink : Option Sp := none) : B :=
  let b := match line with
    | some l =>
      { b with cur := { b.cur with lines := b.cur.lines.push l },
               shrinkAbove := b.shrinkAbove.push
                 (shrink.getD (b.shrinkAbove.back?.getD 0))
               filsAbove := if shrink.isSome then b.filsAbove
                 else b.filsAbove.push (b.filsAbove.back?.getD 0) }
    | none => b
  if fills.isEmpty && paths.isEmpty then b
  else { b with cur := { b.cur with fills := b.cur.fills ++ fills,
                                    paths := b.cur.paths ++ paths } }

/-- Push a picture's label lines: each a rider on the picture's own
shrink, through the one rider door. -/
private def B.pushLabels (b : B) (ls : Array LineOut) (shrink : Sp) : B :=
  ls.foldl (fun b l => b.pushSibling (some l) (shrink := some shrink)) b

private def B.commit (b : B) (line : LineOut) (depth below : Sp)
    (ruleLine : Bool) (consume : Bool) (overflow : Sp) : B :=
  -- The page's shrink ledger is maintained here and nowhere else: a line
  -- that consumed the pending skip banks its shrink (the fit test in
  -- `fitCommit` read the same sum); a line opening a page owes none.
  let above := if consume then b.pageShrink + b.skip.shrink else 0
  -- The consumed skip's fil counts here, page top included: an author's
  -- \vspace*{\fill} above the first line is what the star means (the
  -- space survives the break), and fil width is zero, so counting it
  -- costs nothing when unused.
  let fils := b.pageFils + (if b.skip.fil then 1 else 0)
  { b with cur := { b.cur with lines := b.cur.lines.push line }
           anchors := b.anchors ++ b.pendingAnchors.map ((·, b.pages.size))
           pendingAnchors := #[]
           shrinkAbove := b.shrinkAbove.push above
           pageFils := fils
           filsAbove := b.filsAbove.push fils
           pageShrink := above
           needed := max b.needed overflow
           y := line.y
           freshStart := false
           prevDepth := depth
           prevBelow := below
           prevRuleOnly := ruleLine
           skip := {} }

/-- `doc_geometry_uniform`, the honest whole-document statement for the
preamble-only declarations (`\page` among the eight W0340 fences from the
body): every page of a run is laid out under the one declared geometry,
because the placement steps never write `geom` — the identity holds
through page close, line commit, and sibling rules, so a second geometry
is unrepresentable on the way to `Out`. The body door for geometry does
not exist, and this is the statement that keeps it that way: a step that
started writing `geom` would fail here at build time. -/
private theorem doc_geometry_uniform (b : B) (l line : LineOut)
    (depth below : Sp) (ruleLine consume : Bool) (overflow : Sp) :
    b.finishPage.geom = b.geom ∧ (b.pushSibling (some l)).geom = b.geom ∧
      (b.commit line depth below ruleLine consume overflow).geom = b.geom :=
  ⟨rfl, rfl, rfl⟩

/-- A run emptied of its glyph payload, every metric field kept: the
transformation `line_box_glyph_free` quantifies over. -/
def Seg.stripGlyphs : Seg → Seg
  | .run idx color link w _ size underline raise ground =>
    .run idx color link w #[] size underline raise ground
  | .gap w => .gap w
  | .rule w t r c => .rule w t r c
  | .image s w h => .image s w h

/-- What a line's box measures: the leaded metric extent above and below
the baseline (CSS 2.1 §10.8.1 — the interline rule's terms), and the ink
extent (cap height up, descent down) the convention's two sanctioned ink
uses read: clearing (page area, furniture bands, flush stacking under a
table rule) never spacing. -/
structure LineBox where
  /-- Box top above the baseline: leaded metric ascent, the interline
  term a line contributes when it is the lower neighbour. -/
  above : Sp
  /-- Box bottom below the baseline: leaded metric descent, the interline
  term a line contributes when it is the upper neighbour. -/
  below : Sp
  /-- Ink above the baseline (cap height per run): what stacks flush
  under a table rule, TeX's `\prevdepth`-ignored convention. -/
  inkAbove : Sp
  /-- Ink below the baseline (descent per run): what the page bottom and
  the furniture bands must clear. -/
  inkBelow : Sp
  deriving Repr

/-- CSS 2.1 §10.8.1's half-leading over one (ascent, descent, leading)
triple: the leading less the metric extent, split into integer halves
that sum back exactly, half above the ascent and half below the descent.
Negative half-leading is legal and real — ascent plus descent exceeds
the 6⁄5 leading for three of the four shipped families — so line boxes
may overlap, which is precisely why TeX's collision test cannot survive
under ascender metrics. -/
def leadedBox (ascent descent leading : Sp) : Sp × Sp :=
  (ascent + (leading - (ascent + descent)) / 2,
   leading - ascent - (leading - (ascent + descent)) / 2)

/-- The half-leading cancellation, `baselines_on_grid`: a leaded box's
extent is exactly the leading — A + D + L(eftover) = leading — whatever
the rounding, because `leadedBox` assigns the odd unit below. So in a
paragraph of one (font, size) the interline rule (below of the previous
line plus above of this one) realizes exactly `Ir.leadingFor`,
unconditionally: uniform text sits on the rhythm's grid by algebra, not
by a per-font accident. The mid-paragraph size change is the documented
displacement, pinned executably in Tests/Layout.lean (spacingChecks). -/
theorem baselines_on_grid (ascent descent leading : Int) :
    (leadedBox ascent descent leading).1 + (leadedBox ascent descent leading).2
      = leading := by
  show ascent + (leading - (ascent + descent)) / 2
    + (leading - ascent - (leading - (ascent + descent)) / 2) = leading
  omega

/-- A line's vertical extent, measured seg by seg, each run its own
leaded metric box (`leadedBox` of the font's ascent and descent at the
run's size, plus `raise`) — a sans title is as tall as the sans says,
not as the body face would be at that size, and glyphs are never
consulted (`line_box_glyph_free`). An image stands `h` above the
baseline with no depth and no half-leading (CSS 2.1 §10.8.1's
replaced-element rule): it raises the box, and the leading after it is
the text's own. A math rule (a fraction bar) reaches from `raise` to
`raise + thickness`: it can add height above the baseline or depth below
it, never both. `fontSize`, `bodyAscent`, and `bodyDescent` are the
page's body metrics — the strut of every line of text, so an empty line
still holds one leading. The strut belongs to lines carrying a glyph
run; a line of rules, gaps, or images has exactly the box its segments
make — TeX's `\hrule` is a rule box with no strut (TeXbook ch. 21), and
the title-bars convention (`interlineFor`) measures to a rule's edges,
which a phantom body ascent above a 1 pt rule would falsify. -/
def lineExtent (fs : FontSet) (fontSize bodyAscent bodyCap bodyDescent : Sp)
    (leadFactor : Nat) (size : Sp) (segs : Array Seg) : LineBox :=
  let nominal := if size == 0 then fontSize else size
  let init : LineBox :=
    if segs.isEmpty || segs.any (· matches .run ..) then
      let strut := leadedBox (bodyAscent * nominal / fontSize)
        (bodyDescent * nominal / fontSize) (Ir.leadingFor nominal leadFactor)
      ⟨strut.1, strut.2, bodyCap * nominal / fontSize,
       bodyDescent * nominal / fontSize⟩
    else ⟨0, 0, 0, 0⟩
  segs.foldl (fun (acc : LineBox) s => match s with
    | .run idx _ _ _ _ sz _ raise _ =>
      let font := fs.get idx
      let sz := if sz == 0 then nominal else sz
      let box := leadedBox (scaledAt sz font font.ascent.toNat)
        (scaledAt sz font (-font.descent).toNat) (Ir.leadingFor sz leadFactor)
      ⟨max acc.above (box.1 + max 0 raise),
       max acc.below (box.2 + max 0 (-raise)),
       max acc.inkAbove (scaledAt sz font font.inkAscent.toNat + max 0 raise),
       max acc.inkBelow (scaledAt sz font (-font.descent).toNat + max 0 (-raise))⟩
    | .image _ _ h => ⟨max acc.above h, acc.below, max acc.inkAbove h, acc.inkBelow⟩
    | .rule _ t r _ => ⟨max acc.above (r + t), max acc.below (-r),
       max acc.inkAbove (r + t), max acc.inkBelow (-r)⟩
    | _ => acc)
    init

/-- The line-box convention's guard: a line's box is the metric extent of
the (font, size, raise) triples present on it — the fonts' declared
vertical metrics at each run's size — and never consults a glyph (CSS 2.1
§10.8.1's model: layout bounds come from font metrics; ink may overflow
the box). Emptying every run's glyph array changes no component, by fold
congruence: no arm reads the payload. Everything placed against a line
measures from these metric lines at the run's own size; ink is read only
to interrupt (the underline band) or to clear (math minimum gaps,
furniture bands), never to position. The accepted cost is stated here
once: a descender-less title keeps its full metric depth, so its optical
gap to the next line is larger than its ink suggests — furniture that
moved with the letters would make the artifact content-dependent. -/
theorem line_box_glyph_free (fs : FontSet)
    (fontSize bodyAscent bodyCap bodyDescent : Sp) (leadFactor : Nat)
    (size : Sp) (segs : Array Seg) :
    lineExtent fs fontSize bodyAscent bodyCap bodyDescent leadFactor size
        (segs.map Seg.stripGlyphs) =
      lineExtent fs fontSize bodyAscent bodyCap bodyDescent leadFactor size segs := by
  unfold lineExtent
  have hrun : (segs.map Seg.stripGlyphs).any (· matches Seg.run ..)
      = segs.any (· matches Seg.run ..) := by
    rw [Array.any_map]
    congr 1
    funext s
    cases s <;> rfl
  have hemp : (segs.map Seg.stripGlyphs).isEmpty = segs.isEmpty := by
    unfold Array.isEmpty
    rw [Array.size_map]
  rw [Array.foldl_map, hrun, hemp]
  congr 1
  funext acc s
  cases s <;> rfl

/-- A line that is bare rule ink: at least one segment, every segment a
rule. The interline convention measures to its edges (`interlineFor`),
and the body strut never applies to it (`lineExtent`). -/
def ruleOnly (segs : Array Seg) : Bool :=
  !segs.isEmpty && segs.all (· matches .rule ..)

/-- The metric interline rule with the rule-line convention: the baseline
distance placement adds beyond the pending skip. Between lines of text it
is the previous line's leaded below plus this line's leaded above
(CSS 2.1 §10.8.1). A full-measure rule stands its declared gap from the
type's *body* — the cap-height line above the text, the baseline below
it — never from the metric box, never from glyph ink (Hochuli, *Detail in
Typography*, "Rules": a rule relates to the type it cuts — the sourcing
at `headingRuleWeight`; Bringhurst §2.2.2 for the unit the default gap is
spelled in). So against a rule-only neighbour the terms are
ink-referenced: an upper rule contributes its ink depth and the lower
line its cap line (`inkAbove`); an upper line of text contributes its
baseline (zero) and a lower rule its top edge. A table rule commits with
zero depth and its baseline at the band's bottom, so the line under it
stacks flush by this same rule — its ink height plus pending skips, no
leading — as TeX marks `\prevdepth` ignored after an `\hrule`; booktabs'
rule padding depends on it. Cap height and baseline
are font metrics, so the artifact stays content-free; the accepted cost,
written once here: a descender-free last line's gap below is not larger —
that is the point — and an accented capital's accent rises into the upper
gap. Equal declared gaps are equal visible gaps by definition
(`title_bars_symmetric`), and under the default gap a descender can never
reach the bottom bar (`bars_clear_descenders`). -/
def interlineFor (prevRule : Bool) (prevDepth prevBelow : Sp)
    (ruleLine : Bool) (box : LineBox) : Sp :=
  (if prevRule then prevDepth else if ruleLine then 0 else prevBelow)
    + (if prevRule || ruleLine then box.inkAbove else box.above)

/-- The furniture-symmetry argument, applied to bars: the realized gap
from an upper rule's bottom edge (`prevDepth` below its baseline) to the
next line's cap line equals the pending skip, and from a line's baseline
to a lower rule's top edge (`inkAbove` above its baseline) equals the
pending skip — so equal declared gaps are equal visible gaps by
definition, whatever the type's metrics or the rule weights. -/
theorem title_bars_symmetric (skip prevDepth prevBelow : Int)
    (above below inkAbove inkBelow : Int) :
    skip + interlineFor true prevDepth prevBelow false
        ⟨above, below, inkAbove, inkBelow⟩ - inkAbove - prevDepth = skip ∧
    skip + interlineFor false prevDepth prevBelow true
        ⟨above, below, inkAbove, inkBelow⟩ - inkAbove = skip := by
  simp only [interlineFor]
  constructor <;> simp <;> omega

/-- Under the default bar gap the bottom bar clears every descender: the
gap below the title runs from the baseline (`interlineFor`), a descender
hangs its face's descent below that, and three rhythm quanta of the body
(1.8 × body with the engine's 6⁄5 leading, `Ir.titleBarGap`) exceed even
a full-em descender at the scale's LARGE title step (1.728 × body) —
stated as the inequality it needs, `descMilli ≤ 1000`: no shipped face's
descent approaches its em (OpenType descents sit near a third of it). -/
theorem bars_clear_descenders (body descMilli : Int)
    (hb : Dim.pt 1 ≤ body) -- 1 pt: the rhythm family's floor hypothesis (Ir.default_rhythm_multiples), not a design value
    (hm : descMilli ≤ 1000) :
    Ir.scaleStep body "LARGE" * descMilli / 1000
      < 3 * Ir.rhythmQuantum body := by
  have hb' : (65536 : Int) ≤ body := hb
  have hL : ((Ir.sizeScale.lookup "LARGE").getD 1000 : Int) = 1728 := by decide
  have hstep : Ir.scaleStep body "LARGE" = body * 1728 / 1000 := by
    unfold Ir.scaleStep
    rw [hL]
  rw [hstep]
  have ht : (0 : Int) ≤ body * 1728 / 1000 := by omega
  have h1 : body * 1728 / 1000 * descMilli ≤ body * 1728 / 1000 * 1000 :=
    Int.mul_le_mul_of_nonneg_left hm ht
  have h2 : body * 1728 / 1000 * descMilli / 1000
      ≤ body * 1728 / 1000 * 1000 / 1000 :=
    Int.ediv_le_ediv (by decide) h1
  have h3 : body * 1728 / 1000 * 1000 / 1000 = body * 1728 / 1000 :=
    Int.mul_ediv_cancel _ (by decide)
  calc body * 1728 / 1000 * descMilli / 1000
      ≤ body * 1728 / 1000 * 1000 / 1000 := h2
    _ = body * 1728 / 1000 := h3
    _ < 3 * Ir.rhythmQuantum body := by
        simp only [Ir.rhythmQuantum, Ir.leadingFor, Ir.leadingMilli]
        omega

/-- The fit-or-spill skeleton every committed band takes — the one
spelling of `overflow ≤ shrink ∨ noBreak → commit | close and retry`:
commit at `stepY b` when the band's ink past `bottom` is within the
page's shrink (or a replayed float forbids breaking, `noBreak`), else
close the page and retry — at `firstY b` when the new page is empty,
else at `retryY b` under the reopened frame chrome. The y's are
functions of the builder because a spill moves it, and the retry's
pending glue died with the break, as TeX discards glue at the top of a
page. Notes attach beside every commit (mark and note enter in one
step), and every unchecked commit reports a note overrun (W0372) — the
checked one proved it fits. -/
private def B.fitCommit (b : B) (mk : Sp → LineOut) (firstY stepY retryY : B → Sp)
    (depth below : Sp) (rl : Bool) (inkBelow bottom : Sp)
    (notes : Array NoteBlock := #[]) : B :=
  if b.cur.lines.isEmpty || b.freshStart then
    ((b.commit (mk (firstY b)) depth below rl false 0).attachNotes
      notes).warnNoteOverrun (firstY b) inkBelow
  else
    let y := stepY b
    let overflow := y + inkBelow - bottom
    let above := b.pageShrink + b.skip.shrink
    if overflow ≤ above ∨ b.noBreak then
      (b.commit (mk y) depth below rl true (min overflow above)).attachNotes notes
    else
      let b := b.spillPage
      if b.cur.lines.isEmpty then
        ((b.commit (mk (firstY b)) depth below rl false 0).attachNotes
          notes).warnNoteOverrun (firstY b) inkBelow
      else
        ((b.commit (mk (retryY b)) depth below rl false 0).attachNotes
          notes).warnNoteOverrun (retryY b) inkBelow

/-- Place one line. Its box follows the tallest run on it (`lineExtent`),
not the paragraph's nominal size: a line carrying `\Huge` needs room above
its baseline and below it.

The baseline distance is the metric interline rule (CSS 2.1 §10.8.1): the
previous line's leaded below plus this line's leaded above — for uniform
text exactly the leading, unconditionally (`baselines_on_grid`); a size
change displaces by the larger leaded extent, deterministically,
glyph-free, with no collision term at all. The HTML backend already ships
this convention (`line-height`); this is what unifies the backends'
baselines. Against a rule-only line the terms are ink-referenced
(`interlineFor`): a full-measure rule stands its gap from the type's
body — the cap line above the text, the baseline below it.

A page fills at natural glue until a line's ink will not fit even with
every skip above it fully shrunk; then the page closes (shrunk to fit if
it overflowed) and the line opens the next (`fitCommit`), its pending glue
discarded as TeX discards glue at the top of a page. Glue is never
stretched: the bottom is ragged. -/
private def B.placeLine (fs : FontSet) (b : B) (x : Sp) (size : Sp) (segs : Array Seg)
    (w : Sp) (hang : Sp := 0) (expand : Int := 0)
    (notes : Array NoteBlock := #[]) (counted : Bool := false)
    (leaf : Option Nat := none) : B :=
  let box := lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
    b.geom.leading size segs
  let rl := ruleOnly segs
  -- A zero-width rule is a strut: it shaped the extent above and ships no
  -- ink — kept, a degenerate rect rasterizes as a hairline in some viewers.
  let segs := segs.filter fun s => match s with
    | .rule w _ _ _ => w != 0
    | _ => true
  -- The fit test reads the note floor: what already stands reserved plus
  -- what THIS line's notes need — decided at commit, so a line that does
  -- not fit spills WITH its notes and the reservation follows the mark.
  let need := if notes.isEmpty then 0
    else notes.foldl (fun s nb => s + nb.height) 0
  let bottom := noteFloor b.geom b.footins (b.notesH + need)
  let mk (y : Sp) : LineOut :=
    { x := x, y := y, size := size, segs := segs, setWidth := w
      hang := hang, expand := expand, counted := counted, leaf := leaf }
  -- The first baseline is the body top plus the larger of the body's
  -- metric ascent and the line's own leaded above (`first_baseline_declared`).
  b.fitCommit mk
    (fun b => b.geom.bodyTop + max b.ascent box.above)
    (fun b => b.y + b.skip.width
      + interlineFor b.prevRuleOnly b.prevDepth b.prevBelow rl box)
    -- Below the reopened frame chrome: interline from the chrome's own
    -- baseline.
    (fun b => b.y + interlineFor b.prevRuleOnly b.prevDepth b.prevBelow rl box)
    box.inkBelow box.below rl box.inkBelow bottom notes

/-- The realization theorem's placement step: a line placed on the same
page (the fit condition holds), under interline spacing (neither neighbour
bare rule ink — a rule's realized gap is
`title_bars_symmetric`'s statement), lands exactly the pending skip's
natural width plus the
metric interline — the previous line's leaded below plus this line's
leaded above — below the previous baseline, with no collision
side-condition: the realized peer gap for uniform-size text is the leading
plus the declared skip, unconditionally (`baselines_on_grid`). The
declared gap reaches the page 1:1 — no scaling, no second emission;
`finishPage_shift_uniform` says page close keeps these deltas, so together
they carry the declared gap into `Layout.Out`. Rubber is the one
negotiation and it is never silent: a page that consumes shrink reports it
(N0200, `finishPage`), and vertical glue is never stretched. At a default
peer boundary the pending skip is the resolved parskip
(`flushGap_default_exact`), so the realized baseline delta is the leading
plus exactly one rhythm quantum (`Ir.default_rhythm_multiples`). -/
private theorem placeLine_gap_exact (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int)
    (hcur : b.cur.lines.isEmpty = false) (hfresh : b.freshStart = false)
    (hpr : b.prevRuleOnly = false) (hrl : ruleOnly segs = false)
    (hnn : b.notesH = 0)
    (hfit : b.y + b.skip.width
        + (b.prevBelow + (lineExtent fs b.geom.fontSize b.ascent b.capHeight
            b.descent b.geom.leading size segs).above)
        + (lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
            b.geom.leading size segs).inkBelow - b.geom.bodyBottom
        ≤ b.pageShrink + b.skip.shrink) :
    (b.placeLine fs x size segs w hang ex).cur.lines.back?.map (·.y) =
      some (b.y + b.skip.width
        + (b.prevBelow + (lineExtent fs b.geom.fontSize b.ascent b.capHeight
            b.descent b.geom.leading size segs).above)) := by
  rcases hle : lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
    b.geom.leading size segs with ⟨ht, bl, ia, dp⟩
  rw [hle] at hfit
  dsimp only at hfit
  unfold B.placeLine B.fitCommit
  rw [hle]
  dsimp only
  simp only [hcur, hfresh, hpr, hrl, interlineFor, hnn, noteFloor,
    Array.isEmpty_empty, Bool.or_self, Bool.false_eq_true, ite_false,
    ite_true, Int.add_zero, beq_self_eq_true]
  simp only [hfit, true_or, ite_true, B.commit, B.attachNotes,
    Array.isEmpty_empty, ite_true]
  simp [Array.back?_push]

/-- The first baseline, declared: on a fresh page the line lands at the
body top plus the larger of the body's metric ascent and the line's own
leaded above — today's `\topskip`-shaped rule restated over metric
ascent. Constant for a document unless a taller first line honestly needs
more; what furniture symmetry measures to. -/
private theorem first_baseline_declared (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w : Sp) (hcur : b.cur.lines.isEmpty = true) :
    (b.placeLine fs x size segs w).cur.lines.back?.map (·.y) =
      some (b.geom.bodyTop + max b.ascent
        (lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
          b.geom.leading size segs).above) := by
  rcases hle : lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
    b.geom.leading size segs with ⟨ht, bl, ia, dp⟩
  unfold B.placeLine B.fitCommit
  rw [hle]
  dsimp only
  simp [hcur, B.commit, B.attachNotes, Array.back?_push]

/-- **The line names the leaf it was given** (`_exact`): the `LineOut`
`placeLine` commits carries `leaf` unchanged — the `mk` closure copies it,
so a later edit cannot drop the attribution channel between the paragraph
job and the page silently. Stated on the fresh-page branch, as
`first_baseline_declared` is; every branch commits the same `mk`. -/
private theorem placeLine_leaf_exact (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w : Sp) (lf : Option Nat) (hcur : b.cur.lines.isEmpty = true) :
    (b.placeLine fs x size segs w (leaf := lf)).cur.lines.back?.map (·.leaf) = some lf := by
  rcases hle : lineExtent fs b.geom.fontSize b.ascent b.capHeight b.descent
    b.geom.leading size segs with ⟨ht, bl, ia, dp⟩
  unfold B.placeLine B.fitCommit
  rw [hle]
  dsimp only
  simp [hcur, B.commit, B.attachNotes, Array.back?_push]

/-- The other half of the PDF realization: what page close does to the gaps
placement realized — nothing, on a page that shipped without consuming
shrink and carries no fil glue. The page's vertical distribution (`VDist`)
moves the unpinned block as one: a single delta `d` moves every unpinned
line, so consecutive baseline deltas — the realized gaps — reach `Out`
exactly as placed. A uniform translation rather than a per-gap equality
because that is the exact statement: the gaps are the invariant; the
block's position belongs to the declared distribution. The two excluded
negotiations are declared, never silent: a consumed-shrink page reports
itself (N0200, below), and fil glue exists only where the document asked
for it. -/
private theorem finishPage_shift_uniform (b : B)
    (hsh : b.needed ≤ 0 ∨ b.pageShrink ≤ 0)
    (hfil : b.pageFils = 0) (hsf : b.skip.fil = false)
    (hpn : b.pendingNotes.isEmpty = true) :
    ∃ d, ∀ i, b.pinnedLines ≤ i →
      (b.finishPage.pages.back?.bind fun p => p.lines[i]?.map (·.y)) =
        (b.cur.lines[i]?.map fun l => l.y + d) := by
  have hcond : (decide (b.needed > 0) && decide (b.pageShrink > 0)) = false := by
    rcases hsh with h | h <;> simp [Int.not_lt.mpr h]
  unfold B.finishPage B.noteLines
  simp only [hcond, hsf, hfil, hpn, Bool.false_eq_true, ite_false, ite_true,
    Array.append_empty, Nat.add_zero,
    Nat.lt_irrefl, Array.back?_push, Option.bind_some]
  refine ⟨b.vdist.aboveShare (if b.cur.lines.size > b.pinnedLines then
      noteFloor b.geom b.footins b.notesH
        - (b.cur.lines.foldl (fun m l => max m l.y) 0 + b.prevDepth)
    else 0), fun i hi => ?_⟩
  split <;> split <;>
    simp_all [Array.getElem?_mapIdx, Option.map_map, Function.comp_def,
      Nat.not_lt.mpr hi]

private def B.warnOverfull (b : B) : B :=
  { b with diags := b.diags.push (Diag.of .W0005 "overfull line; no feasible break") }

/-- A heading's declared rule as the line builder reads it: weight,
position against the baseline, and colour — the print reading of
`Ir.ElementStyle`'s `rule`, `ruleThickness`, `rulePosition`. -/
structure HeadingRule where
  thickness : Sp
  position : Ir.RulePosition
  color : Ir.Color
  deriving Repr, Inhabited

/-- One paragraph, measured and ready to break: everything `kp` and line
placement need, gathered during the block walk so the breaking runs can
happen in parallel between the walk and placement. -/
private structure ParaJob where
  items : Array Item
  extras : Std.HashMap Nat Sp
  diags : Array Diag
  target : Sp
  indent : Sp
  center : Bool
  size : Sp
  /-- Justified or ragged, from the page: ragged lines break free of
  stretch badness and are set at their natural width. -/
  justify : Bool := true
  /-- Whether boundary glyphs protrude into the margin, from the page. -/
  protrude : Bool := true
  /-- Whether font boxes may expand within ±`expandLimit`, from the page. -/
  expand : Bool := true
  /-- Marker content set as its own items and placed before the first line. -/
  markerSegs : Option (Array Seg × Sp) := none
  /-- Where the marker's column stands: right-aligned against this offset
  from the margin instead of the line's own indent — an algorithm's line
  numbers keep one column whatever each line's depth. `none` hangs the
  marker off the indent, the list-bullet shape. -/
  markerIndent : Option Sp := none
  /-- A rule filling the first line after the content. -/
  rule : Option HeadingRule := none
  /-- The paragraph's footnotes, pre-broken: each with the item index of
  its mark's box, so placement can hand a line exactly the notes whose
  marks it carries. -/
  notes : Array (Nat × NoteBlock) := #[]
  /-- The paragraph stands inside a float: its lines are box content, not
  galley lines, and the line-number census must not count them
  (`LineOut.counted`). -/
  inFloat : Bool := false
  /-- The first `Struct` leaf of the block this paragraph sets — what every
  line placed from it names (`LineOut.leaf`). `none` for generated ink. -/
  leaf : Option Nat := none

/-- The block walk emits vertical skips and paragraph jobs; placement replays
them in document order, so the page builder stays sequential and the output
does not depend on task scheduling. -/
private inductive Op where
  | skip (g : Glue)
  | para (job : ParaJob)
  /-- A page boundary: a frame is a page of the handout, whatever fits it. -/
  | brk
  /-- Column markers, kept flat so staging stays a map: `colOpen` saves the
  vertical position, `colNext` rewinds to it for the next column, `colClose`
  resumes below the tallest column. Nesting works through a stack. -/
  | colOpen
  | colNext
  | colClose
  /-- Style for the page being opened: a background fill, and how its
  content distributes the leftover vertical space (a standout frame and a
  section page centre; a title page takes the golden split). Applies when
  the page closes and resets with it. -/
  | pageStyle (bg : Option Ir.Color) (vdist : VDist)
  /-- A colour bar behind the line just placed — the frame title. Full page
  width, from the page top to `pad` below the line's depth. -/
  | titleBar (color : Ir.Color) (pad : Sp)
  /-- A colour bar behind the line just placed — a titled block's title.
  Unlike the frame's bar it stands mid-page: `x` across `w` (the measure
  in force where the block stands), one `pad` above the line's ink top to
  one below its depth. -/
  | blockBar (color : Ir.Color) (pad x w : Sp)
  /-- A full-measure horizontal rule as its own line: the title page's
  separator. Placed through `placeLine`, so it spaces, breaks pages, and
  distributes exactly as a line of text does. -/
  | hrule (color : Ir.Color) (thickness : Sp)
  /-- A table rule row, already set: rule (and gap) segs starting at `x`,
  covering `w`. Placed at exactly the pending skip below the previous ink —
  booktabs' padding is the declared seps and nothing else — and it commits
  with zero depth as a rule line, so the row below stacks flush too
  (`interlineFor`). -/
  | tableRule (thickness : Sp) (x w : Sp) (segs : Array Seg)
  /-- Content placed so far on the open page is chrome pinned to the page
  top — the frame title and its bar: the page's vertical distribution
  moves only the lines and fills that follow, as beamer distributes the
  body below the frametitle, never the frametitle itself. -/
  | pin
  /-- A progress bar under the line just placed: `bg` across `w` from `x`,
  `fg` over the leading `num/den` of it, `thick` tall. -/
  | progress (num den : Nat) (fg bg : Ir.Color) (thick x w : Sp)
  /-- The chrome footer for pages closed from here on, with the number of
  the countable frame the pages belong to: a frame sets both (its own
  number, the section in force), a section page or standout frame clears
  them, and a spill page inherits its frame's. -/
  | foot (content : Option (Array Ir.BandSlot)) (frame : Option Nat)
  /-- The logo state changes here: pages from this point carry `content`
  (empty clears). Applied by the furniture pass, keyed to page indexes. -/
  | setLogo (content : Array Ir.Inline)
  /-- An elaborated picture placed with its left edge at page x — fills and
  label lines through one `Pic.Place` transform, fitted vertically the way
  a line of the picture's height is. `leaf` is its `.picture` leaf, what
  the label lines name. -/
  | picture (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat)
  /-- A float's extent: everything between `floatOpen` and its matching
  `floatClose` — caption, gap, and object — is one unbreakable box, as
  LaTeX floats are (a float is a `\vbox`: placed whole or deferred, never
  split). Placement fits the group where it stands, else moves it whole
  to the next page; a group taller than the text block is placed alone
  and overruns, reported (W0358), never split. -/
  | floatOpen
  | floatClose
  /-- An in-document anchor (a level-1 section heading's slug) stands
  here: the builder attaches it to the page the next committed line lands
  on, which is where the outline's destinations resolve. -/
  | anchor (slug : String)

/-- The block walk owes a gap before the next line rather than emitting one
as it goes, because what the gap is depends on everything declared between
two lines. The rules are LaTeX's. `\vspace` is a `\vskip`: it adds. An
element's own space — a heading's `before`, a list's `topsep` — is an
`\addvspace`: against glue already owed it takes the larger, so a list's
bottom space and the heading after it do not stack. `parskip`, the default
between peers, is paid only when nothing was declared. `wantDefault` marks a
peer boundary, `owed` is the glue sequence, `flushGap` pays it when the next
line comes. -/
private structure Rd where
  geom : Geom
  xHeight : Sp
  /-- Hyphenation patterns; a path that must never hyphenate (display
  type, verbatim) passes the sub-walk a reader with `none`. -/
  pats : Option Hyphen.Patterns := none
  fs : FontSet
  styles : Ir.Styles := {}
  /-- The document's resolved main locale: what the class furniture the
  walk generates (the abstract heading, caption prefixes) is worded in. -/
  locale : Locale := Locale.en
  /-- The `slides` class: frames and sections open fresh pages. -/
  slides : Bool := false
  /-- The document's loaded images, from the driver: layout only measures
  and places them; the bytes ride to the backends. -/
  imgs : Image.Store := {}
  /-- The walk is inside a float: every paragraph collected here is box
  content, marked uncounted for the line-number census (`ParaJob.inFloat`,
  `LineOut.counted`). -/
  inFloat : Bool := false
  /-- The headline band a headline class draws on each frame page
  (`Doc.headline`, the poster record's furniture): title, authors,
  institute in the `frametitle` roles at the page top, the body below. -/
  headline : Option Ir.Headline := none

/-- The threaded state of the block walk, now only what the walk actually
writes; everything it merely reads rides in `Rd`, passed to every
`collect*` once. A scoped override — display type turning justification
off, a verbatim block refusing hyphenation, the abstract's `\small` —
is a modified reader handed to the sub-walk, so no restore code exists
to forget. -/
private structure Acc where
  /-- The right edge paragraphs break against, from the page's left margin:
  the text width, unless a column narrows it. -/
  measure : Option Sp := none
  /-- The document's palette: the semantic keys (`fg`, `standoutbg`, …)
  drive the themed furniture, and their absence turns it off. -/
  pal : Ir.Palette := {}
  /-- The document's tokens: `progressheight` sizes the progress bar. -/
  tokens : Ir.Tokens := {}
  /-- Default text colour: the palette's `fg` when declared, else black. -/
  fg : Ir.Color := Ir.Color.black
  /-- The surface content collected here stands on: the palette epoch's
  declared `bg` (`none` is the undeclared page), overridden where a bar or
  an inversion resolves — the frame-title bar, a titled block's bar, the
  standout pair. Written into every `TextStyle` the walk builds, the
  resolving-site half of the declared ground on `Seg.run`. -/
  ground : Option Ir.Color := none
  /-- The number of the frame being collected, from `Ir.frameNumbers`:
  `some k` for the k-th countable frame, `none` for a title or standout
  frame. Threaded by `run`'s driver off the one numbering — nothing in the
  walk counts. -/
  frameNum : Option Nat := none
  /-- Countable frames elapsed at this point, read off the same numbering
  (the last `some` the driver threaded): a section page's progress bar is
  the deck position. -/
  framesDone : Nat := 0
  /-- The numbering's denominator, `Ir.frameCount`. -/
  frameCount : Nat := 0
  /-- Nesting depth of the list being walked, one counter per list kind, as
  LaTeX counts them (`\@itemdepth`/`\@enumdepth`): an itemize inside an
  enumerate inside an itemize is itemize level 2. -/
  itemDepth : Nat := 0
  enumDepth : Nat := 0
  /-- Diagnostics the block walk itself raises (list depth past the class's
  four levels); joined into the placement diagnostics by `run`. -/
  diags : Array Diag := #[]
  /-- The chrome footer's slots, when a themed deck draws one (`\chrome`
  declared, no `\runningfoot` overriding it). Both `none` turns the whole
  footer off. -/
  chromeL : Option Ir.ChromeSlot := none
  chromeR : Option Ir.ChromeSlot := none
  /-- Slides without a `\runningfoot`: the classes of documents whose pages
  may carry a chrome footer at all. -/
  footAllowed : Bool := false
  /-- The `\framefoot` note in force: it takes the footer's left slot for
  the frames that follow, until an empty one clears it. -/
  frameFoot : Option (Array Inline) := none
  /-- Title of the section in force: what a `\sectiontitle` slot shows. -/
  curSection : Array Inline := #[]
  wantDefault : Bool := false
  owed : Array Glue := #[]
  ops : Array Op := #[]
  hyphCache : Std.HashMap String (Array Nat) := {}
  /-- Links of the unpinned navigation landmarks met so far, in document
  order, as (text, target): the entries the document outline resolves. -/
  navEntries : Array (String × String) := #[]
  /-- The next structure leaf the walk will attribute: the preorder index
  into `Struct.leaves (Struct.ofDoc (pdfView doc))`, advanced through
  `leafRange` at exactly the sites `Struct.blockRaw` enumerates leaves, in
  its order. The counts come from `Struct`'s own walk (`leafCount`), so the
  channel indexes the array the tagger reads by construction; the walk
  decides only where a block's range starts. -/
  leafNext : Nat := 0

/-- The leaves `Struct` gives an inline sequence: the count the walk claims
for one block of set text. Counted by the projection's own walk, never a
second enumeration of the inline arms. -/
private def leafCount (xs : Array Inline) : Nat :=
  (Struct.leaves (Struct.inlinesRaw #[] xs.toList)).size

/-- The leaves `Struct` gives a block sequence the page ships no ink for (a
speaker note, an unpinned nav), so the counter steps over them. -/
private def blockLeafCount (bs : Array Block) : Nat :=
  (Struct.leaves (Struct.blocksRaw #[] bs.toList)).size

/-- Claim the next `n` leaves for one block of set text: the block's first
leaf (what its lines name) — `none` when it owns no leaf: generated ink the
tree does not census — and the counter past them. -/
private def Acc.leafRange (a : Acc) (n : Nat) : Acc × Option Nat :=
  ({ a with leafNext := a.leafNext + n }, if n == 0 then none else some a.leafNext)

mutual

private def noteStartsList (out : Array (Option Nat)) :
    List Struct.Node → Array (Option Nat)
  | [] => out
  | n :: rest => noteStartsList (noteStartsOne out n) rest

/-- Each `.note` node's first leaf id, in preorder; a note is not entered
(a note inside a note is the outer note's text to the page). -/
private def noteStartsOne (out : Array (Option Nat)) : Struct.Node → Array (Option Nat)
  | .leaf _ _ => out
  | .node kind kids =>
    match kind with
    | .note => out.push ((Struct.leaves kids)[0]?.map (·.1))
    | .document | .section | .title | .heading _ | .paragraph | .list _ | .item | .label
    | .body | .table | .row | .cell | .caption | .figure | .formula | .code | .quote
    | .aside | .nav | .bibEntry | .link _ | .span _ | .reference _ | .artifact =>
      noteStartsList out kids.toList

end

/-- The first leaf of every footnote in a block's content, in the order the
flatten meets them: the content's shape numbered from `k`, each `.note`
node's first leaf. Decoration the walk prepended to the content — a section
number, a caption prefix, a bibliography marker — is not in the tree, so the
ids shift back by the leaves the content carries beyond its `span`; a note
whose leaf then falls outside `[k, k + span)` has no node of its own (the
tree flattened its block: a bibliography entry, a listing caption) and gets
`none`. -/
private def noteLeafStarts (k span : Nat) (inlines : Array Inline) : Array (Option Nat) :=
  let shape := Struct.number k (Struct.inlinesRaw #[] inlines.toList)
  let extra := (Struct.leaves shape).size - span
  (noteStartsList #[] shape.toList).map fun s =>
    s.bind fun s => if k + extra ≤ s && s - extra < k + span then some (s - extra) else none

/-- A declared length with its rubber: `1.8ex plus 0.8ex minus 0.4ex` keeps
all three parts, so a page can take up the slack the author allowed. -/
private def Rd.resolve (r : Rd) (g : SymGlue) : Glue :=
  g.resolve r.geom.fontSize r.xHeight

private def Rd.parskip (r : Rd) : Glue := r.resolve r.geom.parskip

/-- The next line is a peer of the last: the default gap, unless something
is declared. -/
private def Acc.wantGap (a : Acc) : Acc := { a with wantDefault := true }

/-- `\vskip`: glue the document asked for, on top of whatever is owed. -/
private def Acc.vskip (a : Acc) (g : Glue) : Acc :=
  { a with owed := a.owed.push g }

/-- `\addvspace`: an element's own space. Against glue already owed it takes
the larger (by natural width, as LaTeX compares them), so two elements
meeting do not pay both their spaces. -/
private def Acc.addvspace (a : Acc) (g : Glue) : Acc :=
  match a.owed.back? with
  | some last => if last.width < g.width then { a with owed := a.owed.pop.push g } else a
  | none => { a with owed := #[g] }

/-- Emit the gap owed, just before a line is placed. -/
private def Acc.flushGap (a : Acc) (r : Rd) : Acc :=
  let a := if a.owed.isEmpty then
      (if a.wantDefault then { a with ops := a.ops.push (.skip r.parskip) } else a)
    else { a with ops := a.ops.push (.skip (a.owed.foldl Glue.add {})) }
  { a with wantDefault := false, owed := #[] }

/-- The gap the walk pays at an undeclared peer boundary is the declared
default and only it: one `.skip` of the page's parskip — the resolved
`Ir.parskipDefault`, one rhythm quantum, unless the document declared its
own — never two emissions on one boundary. With anything declared (`owed`
non-empty) the default stands aside entirely. -/
private theorem flushGap_default_exact (a : Acc) (r : Rd)
    (howed : a.owed.isEmpty = true) (hw : a.wantDefault = true) :
    (a.flushGap r).ops = a.ops.push (.skip r.parskip) := by
  simp [Acc.flushGap, howed, hw]

/-- The parskip-growth arm of the heading's undeclared space above
(`parskip.add parskip`, taken when the declared parskip exceeds the
heading token's half): exactly twice the peer gap — one full rhythm unit,
two quanta, by `Ir.default_rhythm_multiples`; the token arm is
`Ir.heading_space_above_ge_below`'s. -/
private theorem heading_default_before_exact (r : Rd) :
    ((r.parskip).add (r.parskip)).width = 2 * r.parskip.width := by
  simp [Glue.add, Int.two_mul]

/-- A page boundary. Whatever gap was owed dies with the old page, as TeX
discards glue at the top of a new one — except fil: infinite glue standing
before the break stretches on the page it ends (TeX discards only what
follows the break point), and dropping it would turn a centring sandwich
into a bottom-flush page. -/
private def Acc.pageBreak (a : Acc) : Acc :=
  let a := if a.owed.any (·.fil) then
      { a with ops := a.ops.push (.skip (a.owed.foldl Glue.add {})) }
    else a
  { a with ops := a.ops.push .brk, wantDefault := false, owed := #[] }

private def Acc.pushOp (a : Acc) (op : Op) : Acc :=
  { a with ops := a.ops.push op }

private def Rd.style (r : Rd) (element : String) : Ir.ElementStyle :=
  (r.styles.find? element).getD {}

/-- The default ink a palette implies: its `fg` when declared, else black —
`Design.ofDoc`'s own rule, applied here per epoch so the ink always follows
the palette in force. -/
private def fgOf (pal : Ir.Palette) : Ir.Color :=
  (pal.find? "fg").getD Ir.Color.black

/-- `.setPalette` on the accumulator: the palette in force, the default
ink, and the surface derived from it change; nothing else does. Named so
its no-emission is a theorem, not a review note. -/
private def Acc.setPalette (a : Acc) (p : Ir.Palette) : Acc :=
  { a with pal := p, fg := fgOf p, ground := p.find? "bg" }

/-- `.setTokens`, same door. -/
private def Acc.setTokens (a : Acc) (tk : Ir.Tokens) : Acc :=
  { a with tokens := tk }

/-- The checkable core of "a setting's effect is confined to its declared
extent", placement side: a stateful declaration emits nothing — the ops
stream every page is placed from, the glue owed, and the pending-gap flag
are untouched, so nothing placed before (or at) the block can differ from
the document without it. The walk-prefix form over `collectBlock` itself
is blocked by the collector's equation lemmas (the
`role_transparent_layout` blocker); its executable oracle lives in
Tests.lean (scopeChecks). -/
private theorem Acc.setPalette_emits_nothing (a : Acc) (p : Ir.Palette) :
    (a.setPalette p).ops = a.ops ∧ (a.setPalette p).owed = a.owed ∧
      (a.setPalette p).wantDefault = a.wantDefault ∧
      (a.setPalette p).diags = a.diags :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem Acc.setTokens_emits_nothing (a : Acc) (tk : Ir.Tokens) :
    (a.setTokens tk).ops = a.ops ∧ (a.setTokens tk).owed = a.owed ∧
      (a.setTokens tk).wantDefault = a.wantDefault ∧
      (a.setTokens tk).diags = a.diags :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The chrome footer a frame's pages carry: the one declared slot band
(`Ir.Chrome.footBand` — fixed sides, resolved content, declared priorities)
resolved to this frame's data. A frame the numbering skips carries no
footer (the caller already guards). `none` when nothing is declared. -/
private def Acc.chromeFoot (a : Acc) : Option (Array Ir.BandSlot) :=
  if a.chromeL.isNone && a.chromeR.isNone && a.frameFoot.isNone then none else
  match a.frameNum with
  | some n =>
    let chrome : Ir.Chrome := { footerLeft := a.chromeL, footerRight := a.chromeR }
    some (chrome.footBand a.frameFoot a.curSection n a.frameCount)
  | none =>
    some (Ir.bandSlotIf .left (a.frameFoot.getD #[]) Ir.notePriority
      "the \\framefoot note")

private def collectPara (r : Rd) (a : Acc)
    (inlines : Array Inline) (indent : Sp) (center : Bool) (size : Sp)
    (baseStyle : TextStyle := {})
    (marker : Option (Array Inline) := none)
    (markerIndent : Option Sp := none)
    (rule : Option HeadingRule := none)
    (display : Bool := false)
    (leaf : Option Nat := none) (span : Nat := 0) : Acc :=
  let a := a.flushGap r
  -- The measure the paragraph sets against — and what a fraction-of-
  -- `\textwidth` image size resolves against: inside a `column` the
  -- current measure, not the page's. A column is a minipage of its
  -- declared width, and a minipage sets `\textwidth` and `\columnwidth`
  -- to its own `\hsize` (latex.ltx, `\@iiiminipage`), so `.95\textwidth`
  -- inside a column names 95% of the column.
  let measure := (a.measure.getD r.geom.textWidth) - indent
  -- The page's text colour is the default: content that declared its own
  -- keeps it, so a themed page colours everything or nothing silently dies
  -- on a dark standout background.
  let baseStyle := if baseStyle.color == Ir.Color.black then
      { baseStyle with color := a.fg } else baseStyle
  let baseStyle := { baseStyle with ground := a.ground }
  let (items, ds, cache, extras, rawNotes) :=
    itemsOfInlines r.pats size r.xHeight r.fs baseStyle inlines a.hyphCache r.imgs
      measure r.geom.textHeight (noteOk := true) (ladder := r.geom.scale)
  let items :=
    if r.geom.justify then items
    else if display then
      displayItems measure items
    else raggedItems items
  -- Each footnote as its own pre-broken block: footnotesize on the FULL
  -- measure (a note belongs to the page, not to the paragraph's column or
  -- indent), the note's own mark leading its first line with no space
  -- after it (\@makefntext's box abuts the text, ltmiscen.dtx), a
  -- \footnotesep strut on the first line (classes.dtx: 6.65pt at the
  -- 10pt option, following the type as 0.665 of the body size).
  let (noteBlocks, ds, cache) : Array (Nat × NoteBlock) × Array Diag ×
      Std.HashMap String (Array Nat) := Id.run do
    if rawNotes.isEmpty then return (#[], ds, cache)
    let mut out : Array (Nat × NoteBlock) := #[]
    let mut ds := ds
    let mut cache := cache
    let noteSize := Ir.scaleStep r.geom.fontSize "footnotesize"
    let sep := r.geom.fontSize * 665 / 1000
    let bodyFont := r.fs.get (r.fs.lookup 0 400 false)
    let scaleB (v : Int) : Sp := v * r.geom.fontSize / bodyFont.unitsPerEm
    let target := r.geom.textWidth
    let noteLeaves := match leaf with
      | some k => noteLeafStarts k span inlines
      | none => #[]
    let mut i := 0
    for (markIdx, num, body) in rawNotes do
      let noteLeaf := (noteLeaves[i]?).getD none
      i := i + 1
      let (nitems0, nds, cache2, _, _) :=
        itemsOfInlines r.pats noteSize r.xHeight r.fs { color := a.fg, ground := a.ground } body
          cache r.imgs r.geom.textWidth r.geom.textHeight (ladder := r.geom.scale)
      ds := ds ++ nds
      cache := cache2
      let (mk, miss) := markBox r.fs { color := a.fg, ground := a.ground } noteSize num
      for (idx, c) in miss do
        ds := ds.push (Diag.of .E0405
          s!"'{(r.fs.get idx).family}' has no glyph for '{c}'; dropped")
      let nitems := #[mk] ++ nitems0
      let nitems := if r.geom.justify then nitems else raggedItems nitems
      let breaks := kpTwoPass nitems target
      let mut lines : Array LineOut := #[]
      let mut yPrev : Sp := 0
      let mut belowPrev : Sp := 0
      let mut hgt : Sp := 0
      let mut prev := 0
      let mut first := true
      for brk in breaks do
        let s := if first then lineStart nitems 0 else lineStart nitems (prev + 1)
        let (lsegs, lw, overfull, _, _) :=
          setLine nitems s brk target r.geom.justify false false
        if overfull then
          ds := ds.push (Diag.of .W0005 "overfull line; no feasible break")
        let box := lineExtent r.fs r.geom.fontSize (scaleB bodyFont.ascent)
          (scaleB bodyFont.capHeight) (scaleB (-bodyFont.descent))
          r.geom.leading noteSize lsegs
        let y := if first then max box.above sep else yPrev + belowPrev + box.above
        lines := lines.push { x := r.geom.hmargin, y := y, size := noteSize,
                              segs := lsegs, setWidth := lw, note := true, leaf := noteLeaf }
        hgt := y + box.inkBelow
        yPrev := y
        belowPrev := box.below
        prev := brk
        first := false
      out := out.push (markIdx, { lines := lines, height := hgt })
    return (out, ds, cache)
  -- A marker is content: set as a line of its own, unjustified, so it can
  -- carry any style the document gave it. Its diagnostics ride with the
  -- paragraph's — a marker glyph no face covers must warn, not vanish.
  let (markerSegs, ds, cache) := match marker with
    | some m =>
      let (mi, mds, cache, _, _) :=
        itemsOfInlines r.pats size r.xHeight r.fs { color := a.fg, ground := a.ground } m cache
          r.imgs measure r.geom.textHeight (ladder := r.geom.scale)
      let (segs, w, _, _) := setLine mi (lineStart mi 0) (mi.size - 1) r.geom.textWidth false
      (some (segs, w), ds ++ mds, cache)
    | none => (none, ds, cache)
  { a with
    hyphCache := cache
    ops := a.ops.push (.para {
      items := items, extras := extras, diags := ds
      target := measure
      indent := indent, center := center, size := size
      justify := r.geom.justify
      protrude := r.geom.protrude
      expand := r.geom.expand
      markerSegs := markerSegs, markerIndent := markerIndent, rule := rule
      notes := noteBlocks
      inFloat := r.inFloat
      leaf := leaf }) }

/-- The weight of a heading's declared rule: 0.06 em of the base — the
0.6 pt the engine shipped at the 10 pt base where it was picked, now
following the type. A rule's weight relates to the stroke weight of the
text it cuts (Hochuli, Detail in Typography, on rules and type), as the
booktabs weights already do em-relative; an absolute point value froze it
against the document's declared size. One spelling — it was once written
twice. -/
private def headingRuleWeight (base : Sp) : Sp := base * 6 / 100

/-- Heading display sizes from the type scale, never loose constants:
article.cls sets `\section` in `\Large`, `\subsection` in `\large`, and
`\subsubsection` in `\normalsize` (classes.dtx, §Sectioning), so the
hierarchy holds at every base size — the old 14/12-point constants
made a 12 pt subsection equal its body and a >14 pt body outgrow its own
sections. -/
def sectionSize (geom : Geom) : Nat → Sp
  | 1 => Ir.scaleStep geom.fontSize "Large"
  | 2 => Ir.scaleStep geom.fontSize "large"
  | _ => geom.fontSize

/-- The applied scale is strictly monotone at every base size of at least
one point: between each named step of `Ir.sizeScale` and the next, the
set size strictly grows — `Ir.sizeScale_monotone` (the bare factors)
carried through `Ir.scaleStep`'s integer division, quantified over the
table's own ladder so a new step enters the contract by being added. The
1 pt floor is what strictness costs under integer division — below 9 sp
(~0.00014 pt) adjacent steps round together, so the bound is the coarsest
honest one. (Each case is `Int` arithmetic with literal factors, which
`omega` reads directly.) -/
theorem scaleStep_monotone (base : Int)
    (hb : pt 1 ≤ base) : -- 1 pt floor: what strictness costs under integer division (docstring), not a design value
    ∀ q ∈ Ir.sizeScale.zip Ir.sizeScale.tail,
      Ir.scaleStep base q.1.1 < Ir.scaleStep base q.2.1 := by
  have hb' : (65536 : Int) ≤ base := hb
  intro q hq
  simp only [Ir.sizeScale, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h|h|h|h|h|h|h|h|h <;> subst h <;>
    first
    | (show base * 500 / 1000 < base * 700 / 1000; omega)
    | (show base * 700 / 1000 < base * 800 / 1000; omega)
    | (show base * 800 / 1000 < base * 900 / 1000; omega)
    | (show base * 900 / 1000 < base * 1000 / 1000; omega)
    | (show base * 1000 / 1000 < base * 1200 / 1000; omega)
    | (show base * 1200 / 1000 < base * 1440 / 1000; omega)
    | (show base * 1440 / 1000 < base * 1728 / 1000; omega)
    | (show base * 1728 / 1000 < base * 2074 / 1000; omega)
    | (show base * 2074 / 1000 < base * 2488 / 1000; omega)

/-- Heading hierarchy (arch-design I3), an instance of `scaleStep_monotone`
at the ladder's normalsize–large–Large run: at every base size of at least
one point, a section sets strictly larger than a subsection, and no
heading sets smaller than its body. The scale (`Ir.sizeScale`,
size10.clo's own values) carries the ordering. -/
theorem heading_hierarchy (g : Geom)
    (hfs : pt 1 ≤ g.fontSize) : -- 1 pt floor: what strictness costs under integer division (scaleStep_monotone)
    sectionSize g 1 > sectionSize g 2 ∧ sectionSize g 2 ≥ g.fontSize := by
  have h12 := scaleStep_monotone g.fontSize hfs
    (("large", 1200), ("Large", 1440)) (by decide)
  have h01 := scaleStep_monotone g.fontSize hfs
    (("normalsize", 1000), ("large", 1200)) (by decide)
  have e0 : Ir.scaleStep g.fontSize "normalsize" = g.fontSize := by
    show g.fontSize * 1000 / 1000 = g.fontSize
    exact Int.mul_ediv_cancel _ (by decide)
  rw [e0] at h01
  exact ⟨h12, Int.le_of_lt h01⟩

/-- Display type: headings, frame titles, section-page and standout text.
Display is not body text: it is never hyphenated (Butterick, Practical
Typography, "Hyphenation": suppress automatic hyphenation where lines are
short — headings foremost — because a break there costs more than it
saves), and therefore never justified either (Butterick, "Justified
text": justification without hyphenation leaves the breaker only word
spaces, and a two-word display line stretches across the whole measure;
moloch's own title and title-page templates are `\raggedright`). The
door hands the sub-walk a reader with no patterns and ragged setting, so
no heading path can do either by construction — the invariant is the
signature. -/
private def collectDisplay (r : Rd) (a : Acc)
    (inlines : Array Inline) (indent : Sp) (center : Bool) (size : Sp)
    (baseStyle : TextStyle := {})
    (rule : Option HeadingRule := none)
    (leaf : Option Nat := none) (span : Nat := 0) : Acc :=
  collectPara { r with pats := none, geom := { r.geom with justify := false } }
    a inlines indent center size (baseStyle := baseStyle) (rule := rule)
    (display := true) (leaf := leaf) (span := span)

/-- The natural (unstretched, unshrunk) width of a set of items: what the
cell takes when nothing bends. Penalties add nothing — a pen's width is
paid only at a break, and a natural cell never breaks. -/
private def itemsNaturalWidth (items : Array Item) : Sp :=
  items.foldl (fun w it => match it with
    | .box bw .. => w + bw
    | .glue g => w + g.width
    | .pen .. => w
    | .img _ bw _ => w + bw
    | .rule bw .. => w + bw) 0

/-- The one door the document title renders through, centred or not: a
declared `titlepage` font template wraps it — the same template the HTML
backend applies to its <h1>, so the two surfaces cannot diverge — and
undeclared it takes display type at the scale's LARGE step in the bold
face (classes.dtx's \@maketitle sets {\LARGE \@title \par}). -/
private def collectTitle (r : Rd) (a : Acc) (title : Array Inline)
    (indent : Sp) (center : Bool) : Acc :=
  let (a, leaf) := a.leafRange (leafCount title)
  match (r.style "titlepage").font with
  | some tpl =>
    collectDisplay r a (Ir.fillTemplate tpl title) indent center r.geom.fontSize
      (leaf := leaf) (span := leafCount title)
  | none =>
    collectDisplay r a title indent center
      (Ir.scaleStep r.geom.fontSize "LARGE")
      (baseStyle := { weight := .b }) (leaf := leaf) (span := leafCount title)

/-- Lay out a `.table`: booktabs' formal table. Columns take their declared
fraction of the measure (or their widest cell), separated by `2·tabcolsep`
(classes.dtx) with the outer pads under `@{}`'s control; each row places
its cells through the column machinery (`colOpen`/`colNext`/`colClose`), so
a row advances by its tallest cell; rules are set rows of rule segments at
booktabs' weights, padded by exactly their declared seps — `tableRule`
placement stacks flush, no leading. `center` centres the whole table box in
the measure (a table under `\centering` or inside a float). -/
private def collectTable (r : Rd) (a0 : Acc)
    (cols : Array Ir.ColSpec) (padL padR : Bool)
    (rows : Array (Array (Array Inline))) (rules : Array (Nat × Ir.TableRule))
    (indent : Sp) (center : Bool) : Acc := Id.run do
  if cols.isEmpty then
    return a0
  let mut a := a0.flushGap r
  let size := r.geom.fontSize
  let tok (name : String) (dflt : Dim.Length) : Sp :=
    match a.tokens.find? name with
    | some g => (r.resolve g).width
    | none => dflt.resolve size r.xHeight
  let colsep := tok "tabcolsep" Ir.tabColSep
  let total := (a.measure.getD r.geom.textWidth) - indent
  -- Natural widths, measured per cell (needed for `l`/`c`/`r` column
  -- widths and for right-aligned placement). The measuring pass drops its
  -- diagnostics: the setting pass below emits them once.
  let mut nats : Array (Array Sp) := #[]
  let mut cache := a.hyphCache
  for row in rows do
    let mut rowNats : Array Sp := #[]
    for cell in row do
      let (items, _, c, _) :=
        itemsOfInlines r.pats size r.xHeight r.fs { color := a.fg, ground := a.ground } cell cache
          r.imgs r.geom.textWidth r.geom.textHeight (ladder := r.geom.scale)
      cache := c
      rowNats := rowNats.push (itemsNaturalWidth items)
    nats := nats.push rowNats
  a := { a with hyphCache := cache }
  let mut widths : Array Sp := #[]
  for j in [0:cols.size] do
    let spec := cols[j]!
    let w : Sp := match spec.width with
      | .natural => nats.foldl (fun m r => max m ((r[j]?).getD 0)) 0
      | .frac f => total * f / 1000
      | .abs w => w
    widths := widths.push w
  let lead : Sp := if padL then colsep else 0
  let trail : Sp := if padR then colsep else 0
  let innerGaps : Sp := 2 * colsep * ((cols.size : Int) - 1)
  let tableW : Sp := lead + widths.foldl (· + ·) 0 + innerGaps + trail
  -- A table wider than the measure stays its declared width and is named,
  -- never squeezed to fit: `\tabcolsep` is a rigid kern (classes.dtx sets
  -- it as a dimen, no rubber), so TeX itself sets the same source overfull
  -- and says so — the deck's `p{0.31}p{0.57}p{0.07}` tables are 4.09 pt
  -- overfull under lualatex too. Shrinking the gaps would fit a box TeX
  -- does not fit and silently change every gap to hide an error in the
  -- declared column widths; the honest fix is the author's, and the help
  -- names it. (The KP breaker's own rule is the same: shrink is spent only
  -- where the glue declared some.)
  if tableW > total then
    a := { a with diags := a.diags.push (Diag.of .W0338
      (s!"the table is {(tableW - total).toPtString}pt wider than the measure")
      (help := "narrow the p{...} column widths, or widen the text block")) }
  let x0 : Sp := indent + (if center && tableW < total then (total - tableW) / 2 else 0)
  -- The left edge of column j's cell box.
  let colX (j : Nat) : Sp := Id.run do
    let mut x := x0 + lead
    for i in [0:j] do
      x := x + widths[i]! + 2 * colsep
    return x
  let fg := a.fg
  let heavy := tok "heavyrulewidth" Ir.heavyRuleWidth
  let light := tok "lightrulewidth" Ir.lightRuleWidth
  let cmidW := tok "cmidrulewidth" Ir.cmidRuleWidth
  let aboveSep := tok "aboverulesep" Ir.aboveRuleSep
  let belowSep := tok "belowrulesep" Ir.belowRuleSep
  let aboveTop := tok "abovetopsep" Ir.aboveTopSep
  let belowBottom := tok "belowbottomsep" Ir.belowBottomSep
  let kern := tok "cmidrulekern" Ir.cmidRuleKern
  let dbl := tok "doublerulesep" Ir.doubleRuleSep
  -- The extent of a `\cmidrule{a-b}`: the cells' span pads included, as
  -- LaTeX's `\multispan` draws it, each end kerned in when trimmed.
  let cmidSeg (ca cb : Nat) (tl tr : Bool) : Sp × Sp :=
    let ca := min (max ca 1) cols.size
    let cb := min (max cb ca) cols.size
    let left := colX (ca - 1) - (if ca == 1 then lead else colsep)
      + (if tl then kern else 0)
    let right := colX (cb - 1) + widths[cb - 1]!
      + (if cb == cols.size then trail else colsep) - (if tr then kern else 0)
    (left, max 0 (right - left))
  -- Emission: elements in document order. The seps are booktabs' rule
  -- classes: a rule after content takes its own sep above; a rule directly
  -- after another rule takes `doublerulesep` in place of both seps (drawn,
  -- since booktabs draws it); an `\addlinespace` (class 2) replaces the
  -- neighbouring rule seps by exactly its space. `pendBelow` is the sep
  -- the last rule owes below itself, paid before the next content row.
  let mut pendBelow : Option Sp := none
  -- 0 = content (or table start), 1 = a drawn rule, 2 = an \addlinespace
  let mut prev : Nat := 0
  for i in [0:rows.size + 1] do
    let mut here : Array Ir.TableRule := #[]
    for (k, tr) in rules do
      if k == i then here := here.push tr
    let mut hi := 0
    for _ in [0:here.size] do
      if h : hi < here.size then
        match here[hi] with
        | .gap g =>
          -- exactly this space: it replaces a neighbouring rule's sep
          pendBelow := none
          a := { a with ops := a.ops.push (.skip { width := (r.resolve g).width }) }
          prev := 2
          hi := hi + 1
        | .cmid _ _ _ _ =>
          -- a run of consecutive cmids is one rule row
          let mut segs : Array Seg := #[]
          let mut x : Sp := 0
          let mut lineX : Sp := 0
          let mut first := true
          for _ in [hi:here.size] do
            if h' : hi < here.size then
              match here[hi] with
              | .cmid ca cb tl tr =>
                let (l, w) := cmidSeg ca cb tl tr
                let l' := r.geom.hmargin + l
                if first then
                  lineX := l'
                  x := l'
                  first := false
                if l' > x then segs := segs.push (.gap (l' - x))
                segs := segs.push (.rule w cmidW 0 fg)
                x := max x (l' + w)
                hi := hi + 1
              | _ => break
          let sep := match prev with
            | 1 => dbl
            | 2 => 0
            | _ => aboveSep
          let ops := (a.ops.push (.skip { width := sep })).push
            (.tableRule cmidW lineX (x - lineX) segs)
          a := { a with ops := ops }
          pendBelow := some belowSep
          prev := 1
        | tr =>
          let (th, ab, be) := match tr with
            | .top => (heavy, aboveTop, belowSep)
            | .bottom => (heavy, aboveSep, belowBottom)
            | _ => (light, aboveSep, belowSep)
          let sep := match prev with
            | 1 => dbl
            | 2 => 0
            | _ => ab
          let ops := (a.ops.push (.skip { width := sep })).push
            (.tableRule th (r.geom.hmargin + x0) tableW #[.rule tableW th 0 fg])
          a := { a with ops := ops }
          pendBelow := some be
          prev := 1
          hi := hi + 1
    if h : i < rows.size then
      if let some pb := pendBelow then
        a := { a with ops := a.ops.push (.skip { width := pb }) }
        pendBelow := none
      prev := 0
      let row := rows[i]
      a := { a with ops := a.ops.push .colOpen }
      for j in [0:row.size] do
        let spec := cols[j]?.getD { width := .natural, align := .left }
        let wj := widths[j]?.getD 0
        let x := colX j
        let cell := row[j]!
        unless cell.isEmpty do
          let sub := { a with
            measure := some (x + wj)
            ops := #[]
            wantDefault := false
            owed := #[] }
          let (sub, leaf) := sub.leafRange (leafCount cell)
          let span := leafCount cell
          let sub := match spec.align with
            | .center => collectPara r sub cell x true size (leaf := leaf) (span := span)
            | .right =>
              let nat := ((nats[i]?).bind (·[j]?)).getD 0
              collectPara r sub cell (x + max 0 (wj - nat)) false size
                (leaf := leaf) (span := span)
            | .left => collectPara r sub cell x false size (leaf := leaf) (span := span)
          a := { a with
            ops := a.ops ++ sub.ops
            hyphCache := sub.hyphCache
            diags := sub.diags
            leafNext := sub.leafNext }
        let closer : Op := if j + 1 == row.size then .colClose else .colNext
        a := { a with ops := a.ops.push closer }
      if row.isEmpty then
        a := { a with ops := a.ops.push .colClose }
  -- A trailing sep below the last rule joins the gap after the table.
  if let some pb := pendBelow then
    if pb > 0 then
      a := a.vskip { width := pb }
  return a

-- Block walk. Mutual recursion through `List` so the nested calls are
-- structural: no `partial`, and the shape mirrors the IR.

/-- Stage one picture. The theorem side of the stays-in-its-box contract
bounds every shape by the picture's box (`Ir.Pic.Picture.box_in_bbox`);
this is the diagnostic side, bounding the box by the text area — a picture
that cannot fit is still placed (best effort, never a blank), and W0335
says the page may be overrun. `center` sets the box's left edge the way a
centred paragraph sets its lines. -/
private def collectPicture (r : Rd) (a : Acc) (pic : Ir.Pic.Picture)
    (indent : Sp) (center : Bool) : Acc :=
  let ((px0, _), (px1, py1)) := pic.bbox
  let w := px1 - px0
  let h := py1 - pic.bbox.1.2
  let avail := (a.measure.getD r.geom.textWidth) - indent
  let a := if w > avail || h > r.geom.textHeight then
      { a with diags := a.diags.push (Diag.of .W0335
        (s!"the picture is {w.toPtString}pt × {h.toPtString}pt against a text area " ++
          s!"of {avail.toPtString}pt × {r.geom.textHeight.toPtString}pt; it may overrun \
the page")
        (help := "shrink the picture ([scale=...]) or widen the text area \
(\\page{ margin = ... })")) }
    else a
  let x := if center then indent + max 0 ((avail - w) / 2) else indent
  let a := a.flushGap r
  -- The picture's one `.picture` leaf: its label lines name it.
  let (a, leaf) := a.leafRange 1
  { a with ops := a.ops.push (.picture (r.geom.hmargin + x) pic leaf) }

/-- What a captioned float stacks, top to bottom. Position decides where
the caption and the object stand, never which gaps are paid — that is the
conservation `floatPlan_gaps_conserved` states. -/
private inductive FloatSlot where
  | gap (g : Glue)
  | caption
  | object

/-- The float's vertical plan, in physical top-to-bottom order: a
text-side gap (`floatsep`), the caption and its object in source order
with the object-side gap (`captionsep`) between them, a text-side gap.
The gap is on the float side of the caption whichever side the caption
stands — LaTeX's `\abovecaptionskip`/`\belowcaptionskip` shape with the
caption package's `tableposition=top` swap (the sourcing note at
`Ir.captionSepDefault`). A bare float pays no caption gap. The float arm
folds over this plan, so the theorems below range over what runs. -/
private def floatPlan (capAbove hasCaption : Bool) (floatSep capSep : Glue) :
    List FloatSlot :=
  if !hasCaption then [.gap floatSep, .object, .gap floatSep]
  else if capAbove then
    [.gap floatSep, .caption, .gap capSep, .object, .gap floatSep]
  else
    [.gap floatSep, .object, .gap capSep, .caption, .gap floatSep]

/-- The gaps a plan pays, in order. -/
private def FloatSlot.gaps (plan : List FloatSlot) : List Glue :=
  plan.filterMap fun s => match s with
    | .gap g => some g
    | _ => none

/-- Caption-position conservation: a captioned float pays exactly the gap
sequence text-side, object-side, text-side whichever side its caption
stands — `capAbove` reorders the caption and the object, never the gaps.
So the total vertical space a captioned float consumes is
`floatsep + body + captionsep + caption + floatsep` regardless of caption
position: "above" and "below" are indistinguishable in rhythm terms. -/
private theorem floatPlan_gaps_conserved (capAbove : Bool) (floatSep capSep : Glue) :
    FloatSlot.gaps (floatPlan capAbove true floatSep capSep)
      = [floatSep, capSep, floatSep] := by
  cases capAbove <;> rfl

/-- A bare float pays the text-side gaps and nothing else. -/
private theorem floatPlan_bare_gaps (capAbove : Bool) (floatSep capSep : Glue) :
    FloatSlot.gaps (floatPlan capAbove false floatSep capSep)
      = [floatSep, floatSep] := by
  cases capAbove <;> rfl

/-- Blocks that are pure state changes: they stand between siblings without
being content — no line, no ink, no gap — so the walks neither pay a peer
gap before them nor count them as a scope's first content. Without this, a
declaration opening a scope would make the first paragraph pay a parskip
nothing else asked for. -/
private def statefulBlock : Block → Bool
  | .setPalette _ | .setTokens _ => true
  | _ => false

mutual

/-- Walk a block sequence, spacing peers by `parskip`. -/
private def collectBlocks (r : Rd) (a : Acc)
    (blocks : Array Block) (indent : Sp) : Acc :=
  collectBlockList r a blocks.toList indent true

private def collectBlockList (r : Rd) (a : Acc)
    (blocks : List Block) (indent : Sp) (first : Bool) : Acc :=
  match blocks with
  | [] => a
  | blk :: rest =>
    if statefulBlock blk then
      collectBlockList r (collectBlock r a blk indent) rest indent first
    else
    let a := if first then a else a.wantGap
    let a := collectBlock r a blk indent
    collectBlockList r a rest indent false

/-- One list item: its leading paragraph carries the marker. -/
private def collectItem (r : Rd) (a : Acc)
    (item : List Block) (indent : Sp) (first : Bool) (marker : Array Inline) : Acc :=
  match item with
  | [] => a
  | blk :: rest =>
    if statefulBlock blk then
      collectItem r (collectBlock r a blk indent) rest indent first marker
    else
    let a := if first then a else a.wantGap
    let a := match blk, first with
      | .para content, true =>
        -- A covered item (dim-not-hide, PLAN M5) is one anonymous colour
        -- wrapper around the whole paragraph, painted by the shade walk;
        -- the marker dims with its item, as beamer's transparent cover
        -- dims the bullet.
        let marker := match content with
          | #[.colored c none _] => #[Ir.Inline.colored c none marker]
          | _ => marker
        let (a, leaf) := a.leafRange (leafCount content)
        collectPara r a content indent false r.geom.fontSize
          (marker := some marker) (leaf := leaf) (span := leafCount content)
      | _, _ => collectBlock r a blk indent
    collectItem r a rest indent false marker

private def collectItems (r : Rd) (a : Acc)
    (items : List (Array Block)) (indent : Sp) (st : Ir.ElementStyle)
    (ordered : Bool) (level : Nat) (idx : Nat) : Acc :=
  match items with
  | [] => a
  | item :: rest =>
    -- Items are peers separated by the declared gap. The default is none,
    -- as it was: a list is one block, and its leading is its rhythm.
    let a := match idx == 1, st.gap with
      | false, some g => a.addvspace (r.resolve g)
      | _, _ => a
    -- The item's marker: the declared style, or the class default for the
    -- level and, for enumerate, this item's number. The class glyph is
    -- checked against the loaded faces so it degrades to its stand-in
    -- rather than to nothing.
    let covered := fun c =>
      (r.fs.body.gid c).isSome || (r.fs.fallbackFor c).isSome
    let marker := st.marker.getD (ListMark.marker ordered level idx covered)
    let a := collectItem r a item.toList indent true marker
    collectItems r a rest indent st ordered level (idx + 1)

/-- Centered content: paragraphs center, anything else nests unchanged. -/
private def collectCentered (r : Rd) (a : Acc)
    (body : List Block) (indent : Sp) : Acc :=
  match body with
  | [] => a
  | blk :: rest =>
    let a := match blk with
      | .para content =>
        let (a, leaf) := a.leafRange (leafCount content)
        collectPara r a content indent true r.geom.fontSize
          (leaf := leaf) (span := leafCount content)
      -- The centred title block: the level-0 heading centres with the
      -- furniture around it, through the same title door as the uncentred
      -- path.
      | .section 0 _ _ title => collectTitle r a title indent true
      -- A centred picture: its box centres in the measure, as the lines of
      -- a centred paragraph do.
      | .picture pic => collectPicture r a pic indent true
      -- A table under \centering (or in a float's centred body) centres
      -- as one box in the measure; its cells keep their own alignment.
      | .table cols pl pr rows rules =>
        collectTable r a cols pl pr rows rules indent true
      | _ => collectBlock r a blk indent
    collectCentered r (if rest.isEmpty || statefulBlock blk then a else a.wantGap)
      rest indent

/-- One column after another: each collects against its own measure at its
own offset, a `colNext` marker between two so placement rewinds the
vertical position. The hyphenation cache threads through; the outer
measure and gap state are restored per column. -/
private def collectColumns (r : Rd) (a : Acc)
    (cols : List (Option Nat × Array Block)) (x0 shareW gutter total : Sp) : Acc :=
  match cols with
  | [] => a
  | (w, body) :: rest =>
    let wi := match w with
      | some f => total * f / 1000
      | none => shareW
    let sub := { a with
      measure := some (x0 + wi)
      ops := #[]
      wantDefault := false
      owed := #[] }
    let sub := collectBlocks r sub body x0
    let a := { a with
      ops := a.ops ++ sub.ops ++ (if rest.isEmpty then #[] else #[Op.colNext])
      hyphCache := sub.hyphCache
      leafNext := sub.leafNext }
    collectColumns r a rest (x0 + wi + gutter) shareW gutter total

/-- A standout frame's content: paragraphs centre and set Large bold, in
the page's (inverted) text colour; anything else nests through the normal
walk and still inherits the colour. -/
private def collectStandout (r : Rd) (a : Acc)
    (body : List Block) (indent : Sp) : Acc :=
  match body with
  | [] => a
  | blk :: rest =>
    let a := match blk with
      | .para content =>
        let (a, leaf) := a.leafRange (leafCount content)
        match (r.style "standout").font with
        | some tpl =>
          collectDisplay r a (Ir.fillTemplate tpl content) indent true r.geom.fontSize
            (leaf := leaf) (span := leafCount content)
        | none =>
          collectDisplay r a content indent true (r.geom.fontSize * 1440 / 1000)
            (baseStyle := { weight := .b }) (leaf := leaf) (span := leafCount content)
      | _ => collectBlock r a blk indent
    collectStandout r (if rest.isEmpty || statefulBlock blk then a else a.wantGap)
      rest indent

private def collectBlock (r : Rd) (a : Acc)
    (blk : Block) (indent : Sp) : Acc :=
  match blk with
  | .para content =>
    -- A paragraph holding only label anchors ships no ink: no line and no
    -- gap, or a \label on its own source line would open a blank line.
    if !content.isEmpty && content.all (fun x => x matches .label _) then a
    else
      let (a, leaf) := a.leafRange (leafCount content)
      collectPara r a content indent false r.geom.fontSize
        (leaf := leaf) (span := leafCount content)
  | .equation num content => Id.run do
    -- A numbered display: the formula centred on the measure, the tag
    -- right-aligned on its baseline (amsmath's equation shape). The line
    -- is [mirror box, fil, formula, fil, tag]: a glyphless box as wide as
    -- the tag on the left makes the two fils centre the formula on the
    -- full measure exactly, and when formula and tag cannot share the
    -- line the fil between them is the legal break, so the tag drops to
    -- its own right-aligned line rather than overprinting (TeX moves the
    -- number down in the same overlap). Justified whatever the page
    -- declares: the fils are the alignment.
    let a := a.flushGap r
    -- The formula's leaves, then the number's `.label` leaf (`Struct`'s shape).
    let (a, leaf) := a.leafRange (leafCount content + 1)
    let baseStyle : TextStyle := { color := a.fg, ground := a.ground }
    -- Image fractions resolve against the current measure, as collectPara's.
    let target := (a.measure.getD r.geom.textWidth) - indent
    let (citems, ds1, cache1, extras, _) :=
      itemsOfInlines r.pats r.geom.fontSize r.xHeight r.fs baseStyle content
        a.hyphCache r.imgs target r.geom.textHeight (ladder := r.geom.scale)
    let (nitems, ds2, cache2, _, _) :=
      itemsOfInlines r.pats r.geom.fontSize r.xHeight r.fs baseStyle #[.text num]
        cache1 r.imgs target r.geom.textHeight (ladder := r.geom.scale)
    -- both walks close with parfill glue and a forced pen; the assembled
    -- line supplies its own ending
    let strip (xs : Array Item) : Array Item :=
      if xs.size ≥ 2 then xs.extract 0 (xs.size - 2) else xs
    let citems := strip citems
    let nitems := strip nitems
    let numW := (measure nitems 0 nitems.size).natural
    let mut items : Array Item :=
      #[.box numW 0 a.fg none #[] r.geom.fontSize false 0 a.ground, .glue { fil := true }]
    items := items ++ citems
    items := items.push (.glue { fil := true })
    items := items ++ nitems
    items := items.push (.pen 0 forcedCost false 0 Ir.Color.black #[])
    return { a with
      hyphCache := cache2
      ops := a.ops.push (.para {
        items := items, extras := extras, diags := ds1 ++ ds2
        target := target
        indent := indent, center := false, size := r.geom.fontSize
        justify := true
        markerSegs := none, rule := none
        leaf := leaf }) }
  | .section level _ num title =>
    if level == 0 then
      -- The document title, a heading at level 0, through the one title
      -- door (`collectTitle`). Never a divider: it stands inside the
      -- furniture \maketitle built (the title frame, the centred block),
      -- so it opens no page of its own even in slides.
      collectTitle r a title indent false
    else
    -- The section in force, for the footer's \sectiontitle slot — and its
    -- anchor: a level-1 heading is addressable (`Ir.slug`, the id the HTML
    -- page assigns), so the outline's in-document targets can resolve to
    -- the page the heading lands on.
    let a := if level == 1 then
        { a with curSection := title
                 ops := a.ops.push (.anchor (Ir.slug title)) }
      else a
    -- The heading's leaves are the title's alone: the number the walk sets
    -- before it is generated ink (`Struct`'s `.section` arm reads no number).
    let span := leafCount title
    let (a, leaf) := a.leafRange span
    if r.slides && level == 1 && (a.pal.find? "progressfg").isSome then
      -- The themed section page: its own page, vertically centred, the
      -- title ragged-left in a centred measure with the deck position
      -- drawn under it as a progress bar.
      let a := a.pageBreak
      -- A divider carries no footer; the break above closed the previous
      -- page with its own.
      let a := if a.footAllowed then { a with ops := a.ops.push (.foot none none) } else a
      let a := { a with ops := a.ops.push (.pageStyle none VDist.center) }
      -- The centred measure the title and the bar share: moloch's own
      -- 0.7875 of the line width (beamerinnerthememoloch.dtx, section page
      -- progressbar template: \begin{minipage}{0.7875\linewidth}).
      let mp : Sp := r.geom.textWidth * 7875 / 10000
      let indent : Sp := (r.geom.textWidth - mp) / 2
      let st := r.style "sectionpage"
      let a := match st.font with
        | some tpl =>
          collectDisplay r a (Ir.fillTemplate tpl title) indent false r.geom.fontSize
            (leaf := leaf) (span := span)
        | none =>
          collectDisplay r a title indent false (r.geom.fontSize * 1440 / 1000)
            (baseStyle := { weight := .b }) (leaf := leaf) (span := span)
      let fgC := (a.pal.find? "progressfg").getD a.fg
      let bgC := (a.pal.find? "progressbg").getD ((a.pal.find? "bg").getD Ir.Color.white)
      -- The fallback is moloch's own default, `progressbar linewidth=1pt`
      -- (beamerouterthememoloch.dtx, \moloch@outer@setdefaults) — the same
      -- value the bundles declare through the token.
      let thick := ((a.tokens.find? "progressheight").map
        fun g => (r.resolve g).width).getD (pt 1) -- moloch's own default: progressbar linewidth=1pt (beamerouterthememoloch.dtx, \moloch@outer@setdefaults)
      -- No clamp: every threaded position is a some of `Ir.frameNumbers`,
      -- ≤ the denominator by theorem (`frameNumbers_le_count`) — moloch
      -- clamps (beamerouterthememoloch.dtx:290) only because its total
      -- comes from a lagging aux file, and this engine has no aux file to
      -- lag. A deck with no countable frame has no position to show, so
      -- it draws no bar at all rather than a fraction over a fake 1.
      let a := if a.frameCount == 0 then a else
        { a with ops := a.ops.push (.progress
          a.framesDone a.frameCount fgC bgC thick
          (r.geom.hmargin + indent) mp) }
      a.pageBreak
    else
    -- In slides, a section is a divider: its own page between frames rather
    -- than a heading dropped onto the bottom of the previous slide.
    let a := if r.slides then a.pageBreak else a
    let a := if a.footAllowed then
        { a with ops := a.ops.push (.foot none none) } else a
    let element := match level with
      | 1 => "section" | 2 => "subsection" | _ => "subsubsection"
    let st := r.style element
    -- The resolved number stands before the title with a \quad between
    -- (classes.dtx \@seccntformat: `\csname the#1\endcsname\quad`),
    -- carried as the em-quad kern so no face is asked for a glyph.
    let title := match num with
      | some n => #[Ir.Inline.text (n ++ "\u2003")] ++ title
      | none => title
    -- Undeclared, a heading stands one full rhythm unit above its body
    -- and half below (`Ir.heading_space_above_ge_below` holds the shape:
    -- more above than below) — its own tokens, so a class that zeroes
    -- \parskip keeps its heading space; a document with a larger parskip
    -- keeps the walk's 2-quanta growth.
    let hb := r.resolve (Ir.headingBeforeDefault r.geom.fontSize)
    let two := r.parskip.add r.parskip
    let a := a.addvspace ((st.before.map r.resolve).getD
      (if two.width > hb.width then two else hb))
    -- A declared font template wraps the title; without one, headings set in
    -- the bold face of the body family at the level's size.
    -- The rule's weight is the declared thickness, else the engine's
    -- em-relative default; its position is the declared one, else the
    -- x-height raise — both facts travel to the line as one record.
    let rule : Option HeadingRule := st.rule.map fun (rc : Ir.Color × Option String) =>
      { thickness := (st.ruleThickness.map fun g => (r.resolve g).width).getD
          (headingRuleWeight r.geom.fontSize)
        position := st.rulePosition.getD .xHeight
        color := rc.1 }
    let a := match st.font with
      | some tpl =>
        collectDisplay r a (Ir.fillTemplate tpl title) indent false r.geom.fontSize
          (rule := rule) (leaf := leaf) (span := span)
      | none =>
        collectDisplay r a title indent false (sectionSize r.geom level)
          (baseStyle := { weight := .b }) (rule := rule)
          (leaf := leaf) (span := span)
    let ha := r.resolve (Ir.headingAfterDefault r.geom.fontSize)
    let a := a.vskip ((st.after.map r.resolve).getD
      (if r.parskip.width > ha.width then r.parskip else ha))
    if r.slides then a.pageBreak else a
  | .list ordered items =>
    -- Depth is per list kind, as LaTeX counts it. The class defines four
    -- levels; where LaTeX errors ("Too deeply nested"), leantex warns and
    -- reuses the fourth level's marking — best effort, never a blank page.
    let depth := (if ordered then a.enumDepth else a.itemDepth) + 1
    let level := min depth 4
    let a := if depth > 4 then { a with diags := a.diags.push (
        Diag.of .W0010
          s!"lists nest four levels; level {depth} reuses the fourth's marker"
          (help := "LaTeX errors here ('Too deeply nested'); flatten the nesting")) }
      else a
    -- The level's own style, falling back to the kind's base style — so a
    -- bare `\style{itemize}{...}` keeps styling every level, as it did.
    let element := if ordered then "enumerate" else "itemize"
    let st := if level == 1 then r.style element
      else (r.styles.find? s!"{element}{level}").getD (r.style element)
    -- LaTeX's `topsep`: the declared space stands above the list and below it.
    let a := match st.before with
      | some g => a.addvspace (r.resolve g)
      | none => a
    let indent := indent + (st.indent.map fun g => (r.resolve g).width).getD r.geom.listIndent
    let a := if ordered then { a with enumDepth := depth } else { a with itemDepth := depth }
    let a := collectItems r a items.toList indent st ordered level 1
    let a := if ordered then { a with enumDepth := depth - 1 }
      else { a with itemDepth := depth - 1 }
    match st.before with
    | some g => a.addvspace (r.resolve g)
    | none => a
  | .center body =>
    collectCentered r a body.toList indent
  -- Ragged-left setting for the scope: the sub-walk reads the same
  -- geometry with justification off (raggedItems' free-fil line ends,
  -- TeXbook ch. 14), the reader flip the ragged title door already uses.
  -- Lines keep the left origin, so `.ragged` needs no placement change.
  | .ragged body =>
    collectBlocks { r with geom := { r.geom with justify := false } } a body indent
  -- A role is a name for the class hook; undeclared, the body collects
  -- exactly as it would unwrapped (roleLayoutChecks pins the zero-byte
  -- claim). A declared `\style{<role>}` gives the role its own rhythm —
  -- the space stands above and below where the role stands, as a list's
  -- topsep does, so the value lives once, upstream, never at use sites.
  | .role n body =>
    let st := r.style n
    let a := match st.before with
      | some g => a.addvspace (r.resolve g)
      | none => a
    let a := collectBlocks r a body indent
    match st.after with
    | some g => a.addvspace (r.resolve g)
    | none => a
  | .quote body =>
    -- A quotation is set off by indenting both margins by the list indent:
    -- classes.dtx defines quote and quotation as `\list{}{\rightmargin
    -- \leftmargin}`, and a top-level list's \leftmargin is \leftmargini —
    -- the same indent the engine's lists take. The right edge moves in by
    -- narrowing the measure the body collects against; the outer measure
    -- is restored after, exactly as a column restores it.
    let saved := a.measure
    let sub := { a with
      measure := some ((a.measure.getD r.geom.textWidth) - r.geom.listIndent) }
    let sub := collectBlocks r sub body (indent + r.geom.listIndent)
    { sub with measure := saved }
  | .titled kind title body =>
    -- beamer's titled block: the title line in the kind's role pair
    -- (`Ir.titledLook`, the one resolving site — read with the palette in
    -- force at the block, as the frame title is), bold at the body size,
    -- with a colour bar behind it when the palette declares one — the
    -- frame-title rule. The bar's pad is half the body size, the frame
    -- bar's own derivation; the title-to-body gap is the default rhythm.
    let look := Ir.titledLook a.pal kind
    let a := if title.isEmpty then a else
      let saved := (a.fg, a.ground)
      let a := { a with fg := look.fg
                        ground := look.bar.orElse fun _ => a.ground }
      let (a, leaf) := a.leafRange (leafCount title)
      let a := collectDisplay r a title indent false r.geom.fontSize
        (baseStyle := { weight := .b }) (leaf := leaf) (span := leafCount title)
      let a := match look.bar with
        | some barBg =>
          { a with ops := a.ops.push (.blockBar barBg (r.geom.fontSize / 2)
              (r.geom.hmargin + indent)
              ((a.measure.getD r.geom.textWidth) - indent)) }
        | none => a
      { a with fg := saved.1, ground := saved.2 }.wantGap
    collectBlocks r a body indent
  | .abstract body =>
    -- article.cls §abstract: `\small`, a centred `{\bfseries\abstractname}`
    -- heading, then the body on quotation margins. The heading word is
    -- class furniture, generated here exactly as the HTML backend
    -- generates its <h2>, and its style is the section heading's, centred
    -- (`Ir.abstractHeadingStyle`) — restyle sections and the abstract
    -- follows; undeclared, the class's own small bold line. The body takes
    -- the scale's own \small, the quotation margins are the quote arm's,
    -- and the outer state is restored the way a quote restores its measure.
    let small := Ir.scaleStep r.geom.fontSize "small"
    let hst := Ir.abstractHeadingStyle r.styles
    let hcenter := hst.align != some "left"
    let a := match hst.font with
      | some tpl =>
        collectDisplay r a (Ir.fillTemplate tpl #[.text r.locale.abstract]) indent
          hcenter r.geom.fontSize
      | none =>
        collectDisplay r a #[.text r.locale.abstract] indent hcenter small
          (baseStyle := { weight := .b })
    let a := a.wantGap
    let saved := a.measure
    let sub := { a with
      measure := some ((a.measure.getD r.geom.textWidth) - r.geom.listIndent) }
    let sub := collectBlocks { r with geom := { r.geom with fontSize := small } }
      sub body (indent + r.geom.listIndent)
    { sub with measure := saved }
  | .columns cols =>
    -- Declared widths are per mille of the full measure. The leftover goes
    -- to the widthless columns in equal shares when there are any, and into
    -- equal gutters between the columns otherwise.
    let a := a.flushGap r
    let total := (a.measure.getD r.geom.textWidth) - indent
    let declared := cols.foldl (fun s (c : Option Nat × Array Block) =>
      s + ((c.1.map fun f => total * f / 1000).getD 0)) 0
    let unspecified := cols.foldl (fun c (col : Option Nat × Array Block) =>
      if col.1.isNone then c + 1 else c) 0
    let rem := max 0 (total - declared)
    let shareW := if unspecified > 0 then rem / unspecified else 0
    let gutter := if unspecified == 0 && cols.size > 1 then rem / (cols.size - 1) else 0
    let a := { a with ops := a.ops.push .colOpen }
    let a := collectColumns r a cols.toList indent shareW gutter total
    { a with ops := a.ops.push .colClose }
  | .bibliography _ _ items =>
    -- The reference list: each resolved entry is one paragraph led by its
    -- style's marker, separated by the paragraph gap — thebibliography's
    -- hanging label set flat. An unfilled marker ships nothing; the
    -- diagnostic that left it empty already said why.
    items.foldl (init := a) fun a item =>
      let content := match item.marker with
        | some m => #[Ir.Inline.text s!"[{m}] "] ++ item.content
        | none => item.content
      -- one leaf per entry, its whole text (`Struct.bibRaw`), the marker generated
      let (a, leaf) := a.leafRange 1
      let a := collectPara r a content indent false r.geom.fontSize (leaf := leaf) (span := 1)
      a.wantGap
  | .spaced before body =>
    -- Declared space above the block, resolved against the body font: the
    -- gap in place of the default, added to any other declared glue — a
    -- bare `\vspace` after a list adds to the list's `topsep`, as in LaTeX.
    let a := a.vskip (r.resolve before)
    collectBlocks r a body indent
  | .step _ _ body =>
    -- Pure grouping: any dimming was painted into colours before layout.
    collectBlocks r a body indent
  | .only _ body =>
    -- `run` already kept this node for the PDF (`Ir.keepFor "pdf"`), so by
    -- here it is pure grouping, exactly as a resolved step is.
    collectBlocks r a body indent
  | .nav spec body =>
    -- A nav is furniture, and each medium has its own answer. The paged
    -- surface renders an unpinned nav as the document outline — print's
    -- own navigation (ISO 32000-2 §12.3.3): its links become entries and
    -- its body ships no ink. A pinned nav is viewport furniture with no
    -- page analogue, dropped exactly as `.note` is not handout content.
    -- HTML keeps the `<nav>` landmark element.
    -- Its leaves are numbered whether or not the page sets them: the
    -- counter steps over them so what follows keeps its index.
    let a := (a.leafRange (blockLeafCount body)).1
    if spec.pin.isSome then a
    else { a with navEntries := a.navEntries ++ Ir.navLinks body }
  | .note body =>
    -- A speaker note is not handout content: no lines, no gap. Its leaves
    -- (an `.aside` in the tree) are stepped over, never attributed.
    (a.leafRange (blockLeafCount body)).1
  | .pagebreak =>
    -- The declared boundary: the builder closes only pages holding
    -- something, so adjacent breaks never make a blank page.
    a.pageBreak
  | .logo content =>
    -- A stateful declaration: the pages from here on carry this content at
    -- their corner. No lines, no gap; placement reads the spans. Its
    -- `.artifact` leaves are stepped over: the furniture pass lays them
    -- flagged, never attributed.
    let a := (a.leafRange (leafCount content)).1
    { a with ops := a.ops.push (.setLogo content) }
  | .verbatim covered s spec =>
    -- Code lines, kept literally, at the scale's own \footnotesize (the
    -- code-frame convention) — derived from the table, not a loose decimal.
    -- No hyphenation patterns: the engine must never invent a hyphen inside
    -- an identifier. A pending overlay's shade rides in `covered`: code
    -- must read as covered like any other text.
    -- A declared caption sets above the code (listings.sty:
    -- `\lst@Key{captionpos}{t}` — above is the default), in the
    -- figure-caption shape: numbered from the one site both backends read
    -- (`Ir.listingCaption`), centred when it fits one line
    -- (classes.dtx §\@makecaption), bound `captionsep` from the code.
    let a := match spec.caption with
      | some (n, cap) =>
        let caption := Ir.listingCaption r.locale n cap
        let avail := (a.measure.getD r.geom.textWidth) - indent
        let (items, _, cache, _) :=
          itemsOfInlines r.pats r.geom.fontSize r.xHeight r.fs
            { color := a.fg, ground := a.ground } caption
            a.hyphCache r.imgs avail r.geom.textHeight (ladder := r.geom.scale)
        let a := { a with hyphCache := cache }
        let fits := itemsNaturalWidth items ≤ avail
        -- one flat caption leaf (`Struct`'s listing shape), the prefix generated
        let (a, leaf) := a.leafRange 1
        let a := collectPara r a caption indent fits r.geom.fontSize (leaf := leaf) (span := 1)
        a.addvspace (r.resolve ((a.tokens.find? "captionsep").getD
          (Ir.captionSepDefault r.geom.fontSize)))
      | none => a
    -- Declared line numbers are furniture beside each line — generated
    -- ink, like a list's markers: right-aligned digits in the mono face,
    -- held to their line by no-break spaces.
    let inner : Array Ir.Inline :=
      if spec.numbers then Id.run do
        let lines := Ir.verbatimLines s
        let w := (toString lines.size).length
        let mut out : Array Ir.Inline := #[]
        let mut i := 0
        for line in lines do
          i := i + 1
          unless out.isEmpty do
            out := out.push (.linebreak {})
          let numStr := toString i
          let pad := String.ofList (List.replicate (w - numStr.length) '\u00a0')
          let kept := line.foldl
            (fun acc c => acc.push (if c == ' ' then '\u00a0' else c)) ""
          out := out.push (.text (pad ++ numStr ++ "\u00a0\u00a0" ++ kept))
        pure #[.styled .mono out]
      else #[.styled .mono (Ir.verbatimInlines s)]
    let inner := match covered with
      | some c => #[.colored c none inner]
      | none => inner
    -- the code is one leaf, its whole content; line numbers are generated
    let (a, leaf) := a.leafRange 1
    collectPara { r with pats := none } a inner indent false
      (Ir.scaleStep r.geom.fontSize "footnotesize") (leaf := leaf) (span := 1)
  | .algorithm numbered semis lines =>
    -- Pseudocode: each line one display-type paragraph at the body size —
    -- never hyphenated (the engine must not invent a hyphen inside an
    -- identifier), never justified (a short pseudocode line stretched
    -- across the measure is the two-word display line) — indented one
    -- `algindent` step per depth. The step's default is algorithm2e's own
    -- indent, `\SetInd{0.5em}{1em}` plus its 0.4pt rule allowance
    -- (algorithm2e.sty:1604,1622), ≈1.5em, following the type; the token
    -- overrides it. Keywords, io labels, semicolons and the muted comment
    -- come generated from `Ir.AlgLine.rendered` — the one site both
    -- backends read (`algorithm_lines_agree`). A line number is a marker
    -- in the muted role: the list-marker furniture shape, so numbers
    -- right-align against the text edge as bullets do.
    let words := Ir.algWords r.locale.tag
    let muted := Ir.mutedOf a.pal
    let stepInd := (r.resolve ((a.tokens.find? "algindent").getD
      { width := { em := 1500 } })).width
    let rAlg := { r with pats := none, geom := { r.geom with justify := false } }
    -- One `.code` node holds every line's leaves (`Struct.algRaw`): a line
    -- names its own first leaf; a keyword-only line (`end`, `else`) is
    -- generated ink that rides the block's first leaf.
    let codeLeaf : Option Nat :=
      if lines.any (fun l => leafCount l.content + leafCount (l.comment.getD #[]) > 0)
      then some a.leafNext else none
    (lines.foldl (fun (ai : Acc × Nat) l =>
      let (a, i) := ai
      let content := Ir.AlgLine.rendered words semis muted l
      let marker : Option (Array Ir.Inline) := if numbered then
          some #[Ir.Inline.colored muted (some "muted") #[.text s!"{i}"]]
        else none
      -- the line's leaves: its content's, then its comment's (`Struct.algRaw`)
      let span := leafCount l.content + leafCount (l.comment.getD #[])
      let (a, leaf) := a.leafRange span
      (collectPara rAlg a content (indent + stepInd * (l.depth : Int)) false
        r.geom.fontSize (marker := marker) (markerIndent := some indent)
        (leaf := leaf <|> codeLeaf) (span := span),
        i + 1)) (a, 1)).1
  | .framefoot content =>
    -- Not a line, a state change: the note the following frames' footers
    -- carry. Empty clears back to the chrome default. Its `.artifact`
    -- leaves are stepped over, as the logo's are.
    let a := (a.leafRange (leafCount content)).1
    { a with frameFoot := if content.isEmpty then none else some content }
  | .setPalette p =>
    -- A stateful declaration, like `.logo`: the palette in force from here
    -- on, in flow order — the accumulator threads it past the enclosing
    -- block's end (flow scope, no brace revert). The default ink follows
    -- the palette it derives from. No line, no gap, no op: the node ships
    -- no ink of its own (`Acc.setPalette_emits_nothing`).
    a.setPalette p

  | .setTokens tk =>
    -- Same door for the token state: `tabcolsep`, `floatsep`,
    -- `progressheight` and friends resolve against the tokens in force
    -- where the element stands, not the document's final state.
    a.setTokens tk
  | .rule color _ thickness =>
    -- The title page's separator: colour and thickness were declared
    -- (palette `separator`, token `separatorheight`); the measure is the
    -- text width, as moloch draws it.
    let a := a.flushGap r
    { a with ops := a.ops.push (.hrule color (r.resolve thickness).width) }
  | .picture pic =>
    -- Left on the current indent, as LaTeX places the box where it stands;
    -- a `{center}` around it goes through `collectCentered`'s arm.
    collectPicture r a pic indent false
  | .table cols padL padR rows rules =>
    collectTable r a cols padL padR rows rules indent false
  | .float kind num capAbove body caption =>
    -- Set off from the text by `floatsep` on both sides, the caption bound
    -- `captionsep` from the content on its object side (the sourced side
    -- rule lives at `Ir.caption_gaps_rhythm`); the body centres, the
    -- figure convention the old center-wrapping gave. Both gaps are
    -- `\addvspace`-style: an element's own space, never stacked onto a
    -- neighbour's. The caption sets with its number in front —
    -- `Ir.numberedCaption`, the one site both backends spell a float's
    -- number from. Everything between `floatOpen` and `floatClose` ships
    -- on one page (`runFloat`): a float is unbreakable, as LaTeX's are.
    -- The tree numbers the caption's leaves first whatever `capAbove` says
    -- (`Struct.blockRaw`'s float arm: census order is `blocksText`'s); the
    -- page places it where `capAbove` says. So the caption's range is
    -- claimed here, before the plan runs, and the body's begins past it.
    -- Counted on the declared caption: the number prefix is generated.
    let capSpan := leafCount caption
    let (a, capLeaf) := a.leafRange capSpan
    let caption := Ir.numberedCaption r.locale kind num caption
    let floatSep := r.resolve ((a.tokens.find? "floatsep").getD
      (Ir.floatSepDefault r.geom.fontSize))
    let capSep := r.resolve ((a.tokens.find? "captionsep").getD
      (Ir.captionSepDefault r.geom.fontSize))
    let a := a.pushOp .floatOpen
    -- The float's caption and body are box content, not galley lines: the
    -- sub-walk runs under a marked reader so no line of them is counted
    -- by the line-number census (`Rd.inFloat`).
    let rf := { r with inFloat := true }
    -- classes.dtx `\@makecaption`: a caption that fits one line centres; a
    -- longer one sets as an ordinary paragraph.
    let setCaption (a : Acc) : Acc :=
      if caption.isEmpty then a else
      -- A declared caption margin (caption manual §2.4, \captionsetup{
      -- margin = ... }) moves both caption edges in, the abstract's
      -- narrower-measure shape; undeclared, the full measure as before.
      let cmargin := ((a.tokens.find? "captionmargin").map
        (fun g => (r.resolve g).width)).getD 0
      let avail := (a.measure.getD r.geom.textWidth) - indent - 2 * cmargin
      let (items, _, cache, _) :=
        itemsOfInlines r.pats r.geom.fontSize r.xHeight r.fs { color := a.fg, ground := a.ground } caption
          a.hyphCache r.imgs avail r.geom.textHeight (ladder := r.geom.scale)
      let a := { a with hyphCache := cache }
      let fits := itemsNaturalWidth items ≤ avail
      let saved := a.measure
      let a := { a with measure := some ((a.measure.getD r.geom.textWidth) - cmargin) }
      let a := collectPara rf a caption (indent + cmargin) fits r.geom.fontSize
        (leaf := capLeaf) (span := capSpan)
      { a with measure := saved }
    let a := (floatPlan capAbove (!caption.isEmpty) floatSep capSep).foldl
      (fun a slot => match slot with
        | .gap g => a.addvspace g
        | .caption => setCaption a
        | .object => collectCentered rf a body.toList indent) a
    a.pushOp .floatClose
  | .frame title standout valign body =>
    -- A frame is a page boundary, not an article paragraph. Content past
    -- the page bottom spills to a continuation page — best effort, never
    -- clipped. The frame's number rides in from `run`'s top-level driver,
    -- read off `Ir.frameNumbers`, once per logical frame, so a stepped
    -- frame's pages share it.
    let a := a.pageBreak
    -- The footer belongs to the frame: its pages, spill pages included,
    -- carry the frame's own number. A frame the numbering skips — the
    -- title page, a standout — carries no footer at all: moloch renders
    -- both plain (beamerinnerthememoloch.dtx:314-320, 777-778), and a
    -- number slot with no number has nothing true to show.
    let a := if a.footAllowed then
        { a with ops := a.ops.push (.foot (if a.frameNum.isNone then none else a.chromeFoot) a.frameNum) }
      else a
    -- Every frame declares its distribution (beamer's default is centring,
    -- user guide §8.1); only the article page and a continuation page keep
    -- the builder's top-flush default.
    -- The frame's `.title` node stands first in the tree whether or not the
    -- page sets it: a standout frame shows its body alone, so its title's
    -- leaves are stepped over.
    let titleSpan := leafCount title
    let (a, titleLeaf) := a.leafRange titleSpan
    if standout then
      -- Inverted, centred, Large bold. The palette's standout keys
      -- override; without them the frame inverts the page's own colours.
      let bg := (a.pal.find? "standoutbg").getD ((a.pal.find? "fg").getD Ir.Color.black)
      let fg := (a.pal.find? "standoutfg").getD ((a.pal.find? "bg").getD Ir.Color.white)
      let a := { a with ops := a.ops.push (.pageStyle (some bg) (VDist.of valign)) }
      let a := collectStandout r { a with fg := fg, ground := some bg } body.toList indent
      -- Restore by recomputing from the palette in force: a `.setPalette`
      -- inside the frame must reach what follows it (flow scope), so a
      -- saved copy would restore a stale epoch's ink.
      let a := { a with fg := fgOf a.pal, ground := a.pal.find? "bg" }
      a.pageBreak
    else
    let a := { a with ops := a.ops.push (.pageStyle none (VDist.of valign)) }
    -- The headline band: a headline class's `\title` family as page-top
    -- furniture (the gemini lineage's headline template), in the
    -- `frametitle` roles the deck bar resolves — the one resolving site —
    -- with the sizes the lineage's own font templates declare
    -- (beamerthemegemini.sty: headline title \Huge bold, author \Large,
    -- institute \normalsize — scale steps, never point literals). The
    -- alignment is the `titlepage` style's declared token (gemini
    -- declares centred; undeclared centres, `\@maketitle`'s own rule),
    -- and a declared `titlepage` font template wraps the title as it
    -- wraps `\maketitle`'s. The `.pin` makes the band page-top chrome:
    -- the frame's distribution moves the body below it, never the band.
    let a := match r.headline with
      | some hl =>
        let bar := a.pal.find? "frametitlebg"
        let saved := (a.fg, a.ground)
        let a := match bar with
          | some barBg =>
            { a with fg := (a.pal.find? "frametitlefg").getD
                       ((a.pal.find? "bg").getD Ir.Color.white)
                     ground := some barBg }
          | none => a
        let tps := r.style "titlepage"
        let center := tps.align != some "left"
        let a := match tps.font with
          | some tpl =>
            collectDisplay r a (Ir.fillTemplate tpl hl.title) 0 center r.geom.fontSize
          | none =>
            collectDisplay r a hl.title 0 center
              (Ir.scaleStep r.geom.fontSize "Huge") (baseStyle := { weight := .b })
        let a := if hl.author.isEmpty then a else
          collectDisplay r a hl.author 0 center (Ir.scaleStep r.geom.fontSize "Large")
        let a := if hl.institute.isEmpty then a else
          collectDisplay r a hl.institute 0 center r.geom.fontSize
        let a := match bar with
          | some barBg =>
            { a with fg := saved.1, ground := saved.2
                     ops := a.ops.push (.titleBar barBg (r.geom.fontSize / 2)) }
          | none => a
        -- The band-to-body gap is the frame title's own (`wantDefault`):
        -- without it the first block's title bar pad reaches into the
        -- band's fill.
        { a with ops := a.ops.push .pin, wantDefault := true }
      | none => a
    let a := if title.isEmpty then a else
      match a.pal.find? "frametitlebg" with
      | some barBg =>
        -- The themed frame title is a colour bar across the whole page,
        -- its text in frametitlefg on it.
        let ftFg := (a.pal.find? "frametitlefg").getD
          ((a.pal.find? "bg").getD Ir.Color.white)
        let saved := (a.fg, a.ground)
        let a := { a with fg := ftFg, ground := some barBg }
        let st := r.style "frametitle"
        let a := match st.font with
          | some tpl =>
            collectDisplay r a (Ir.fillTemplate tpl title) 0 false r.geom.fontSize
              (leaf := titleLeaf) (span := titleSpan)
          | none =>
            collectDisplay r a title 0 false (sectionSize r.geom 1)
              (baseStyle := { weight := .b }) (leaf := titleLeaf) (span := titleSpan)
        -- The title itself is inline content: no `.setPalette` can stand
        -- in it, so the saved ink is the epoch's own.
        let a := { a with fg := saved.1
                          ground := saved.2
                          ops := a.ops.push (.titleBar barBg (r.geom.fontSize / 2)) }
        { a with wantDefault := true }
      | none =>
        let a := collectDisplay r a title 0 false (sectionSize r.geom 1)
          (baseStyle := { weight := .b }) (leaf := titleLeaf) (span := titleSpan)
        { a with wantDefault := true }
    -- The title just placed is page-top chrome: the frame's distribution
    -- moves the body below it, never the title (beamer's frametitle).
    let a := if title.isEmpty then a else { a with ops := a.ops.push .pin }
    -- A golden frame is the title page (only \maketitle declares golden),
    -- and everything on it is display furniture: titles never hyphenate
    -- and never justify (collectDisplay's rule, through the declaration).
    let a := if valign matches .golden then
        collectBlocks { r with pats := none, geom := { r.geom with justify := false } }
          a body indent
      else collectBlocks r a body indent
    a.pageBreak

end

-- The block half of `role_transparent_layout` — `collectBlock` on an
-- unstyled `.role` delegates to `collectBlocks` unchanged — is pinned
-- executably over `Layout.run`'s shipped pages in Tests.lean
-- (roleLayoutChecks): an oracle, not a theorem. The statement's
-- `rw [collectBlock]` needs the collector's equation lemmas, whose
-- generation for this (very large) match exhausts `whnf` whatever the
-- heartbeat budget; the arm is reviewed where it stands (the `.role` arm
-- above — with no declared style both rhythm matches are `none` and the
-- body collects unwrapped).

/-- Pass 1's merge postcondition, the shape pass 2's subtraction needs to
be provably correct: intervals sorted, pairwise disjoint (half-open
reading), each nonempty. -/
def Chained : List (Int × Int) → Prop
  | [] => True
  | (lo, hi) :: rest => lo ≤ hi ∧ (∀ o ∈ rest, hi ≤ o.1) ∧ Chained rest

/-- The sub-intervals of `[cur, hi)` not covered by the chained
obstruction list: pass 2's interval walk, pure — closed-form geometry the
underline theorems range over. The clearance is already dilated into the
obstructions (pass 1). -/
def subtract (cur hi : Int) : List (Int × Int) → List (Int × Int)
  | [] => if cur < hi then [(cur, hi)] else []
  | (olo, ohi) :: rest =>
    if cur < min olo hi then (cur, min olo hi) :: subtract (max cur ohi) hi rest
    else subtract (max cur ohi) hi rest

/-- Every emitted interval is nonempty and inside `[cur, hi)`. -/
theorem subtract_bounds (obs : List (Int × Int)) (cur hi : Int) :
    ∀ s ∈ subtract cur hi obs, cur ≤ s.1 ∧ s.1 < s.2 ∧ s.2 ≤ hi := by
  induction obs generalizing cur with
  | nil =>
    intro s hs
    simp only [subtract] at hs
    split at hs <;> simp_all <;> omega
  | cons o rest ih =>
    intro s hs
    simp only [subtract] at hs
    split at hs
    · rcases List.mem_cons.mp hs with rfl | hs'
      · dsimp only
        omega
      · have := ih (max cur o.2) s hs'
        omega
    · have := ih (max cur o.2) s hs
      omega

/-- `underline_skips_ink`, the geometric core of the skip-ink underline
(CSS Text Decoration 4 §2.10.5): no emitted rule interval meets any
obstruction — the drawn rule crosses no glyph ink dilated by its
clearance. -/
theorem underline_skips_ink (obs : List (Int × Int)) (cur hi : Int)
    (hch : Chained obs) :
    ∀ s ∈ subtract cur hi obs, ∀ o ∈ obs, s.2 ≤ o.1 ∨ o.2 ≤ s.1 := by
  induction obs generalizing cur with
  | nil => intro s _ o ho; cases ho
  | cons a rest ih =>
    obtain ⟨hne, hsep, hrest⟩ := hch
    intro s hs o ho
    simp only [subtract] at hs
    split at hs
    · rcases List.mem_cons.mp hs with rfl | hs'
      · rcases List.mem_cons.mp ho with rfl | ho'
        · left
          dsimp only
          omega
        · have := hsep o ho'
          left
          dsimp only
          omega
      · have hb := subtract_bounds rest (max cur a.2) hi s hs'
        rcases List.mem_cons.mp ho with rfl | ho'
        · right
          omega
        · exact ih (max cur a.2) hrest s hs' o ho'
    · have hb := subtract_bounds rest (max cur a.2) hi s hs
      rcases List.mem_cons.mp ho with rfl | ho'
      · right
        omega
      · exact ih (max cur a.2) hrest s hs o ho'

/-- `underline_covers_gaps`, the other half: every uncovered x in
`[cur, hi)` lies under an emitted rule interval — the underline is
interrupted only at ink, never silently dropped. -/
theorem underline_covers_gaps (obs : List (Int × Int)) (cur hi x : Int)
    (hch : Chained obs) (hx : cur ≤ x ∧ x < hi)
    (hout : ∀ o ∈ obs, x < o.1 ∨ o.2 ≤ x) :
    ∃ s ∈ subtract cur hi obs, s.1 ≤ x ∧ x < s.2 := by
  induction obs generalizing cur with
  | nil =>
    refine ⟨(cur, hi), ?_, by omega⟩
    simp only [subtract]
    split
    · simp
    · exfalso
      omega
  | cons a rest ih =>
    obtain ⟨hne, hsep, hrest⟩ := hch
    rcases hout a (List.mem_cons_self ..) with hlt | hge
    · refine ⟨(cur, min a.1 hi), ?_, by dsimp only; omega⟩
      simp only [subtract]
      split
      · exact List.mem_cons_self ..
      · exact absurd (by omega : cur < min a.1 hi) ‹¬_›
    · obtain ⟨s, hs, hcov⟩ := ih (max cur a.2) hrest ⟨by omega, hx.2⟩
        (fun o ho => hout o (List.mem_cons_of_mem _ ho))
      refine ⟨s, ?_, hcov⟩
      simp only [subtract]
      split
      · exact List.mem_cons_of_mem _ hs
      · exact hs

/-- Merge a sorted run of intervals into a chained list: `cur` is the
interval being grown; an input that reaches back into it fuses (the fold
never needs `min` — sorted input keeps `cur.1` least), and one that
stands clear emits `cur` and starts the next. Pass 1's merge, pure. -/
def mergeChained (cur : Int × Int) : List (Int × Int) → List (Int × Int)
  | [] => [cur]
  | (lo, hi) :: rest =>
    if lo ≤ cur.2 then mergeChained (cur.1, max cur.2 hi) rest
    else cur :: mergeChained (lo, hi) rest

/-- Every merged interval starts at or after the growing interval's own
start, given sorted input at or after it. -/
theorem mergeChained_lb (cur : Int × Int) (l : List (Int × Int))
    (hs : l.Pairwise (fun a b => a.1 ≤ b.1)) (hcl : ∀ o ∈ l, cur.1 ≤ o.1) :
    ∀ s ∈ mergeChained cur l, cur.1 ≤ s.1 := by
  induction l generalizing cur with
  | nil =>
    intro s hs'
    simp only [mergeChained, List.mem_singleton] at hs'
    subst hs'
    omega
  | cons a rest ih =>
    obtain ⟨hhd, hrest⟩ := List.pairwise_cons.mp hs
    intro s hmem
    simp only [mergeChained] at hmem
    split at hmem
    · exact ih (cur.1, max cur.2 a.2) hrest
        (fun o ho => by have := hcl o (List.mem_cons_of_mem _ ho); exact this) s hmem
    · rcases List.mem_cons.mp hmem with rfl | hmem'
      · omega
      · have ha := hcl a (List.mem_cons_self ..)
        have := ih a hrest (fun o ho => hhd o ho) s hmem'
        omega

/-- The merge postcondition, proved: sorted nonempty input in, `Chained`
out — what `underline_skips_ink` and `underline_covers_gaps` consume. -/
theorem mergeChained_chained (cur : Int × Int) (l : List (Int × Int))
    (hc : cur.1 ≤ cur.2) (hne : ∀ o ∈ l, o.1 ≤ o.2)
    (hs : l.Pairwise (fun a b => a.1 ≤ b.1)) (hcl : ∀ o ∈ l, cur.1 ≤ o.1) :
    Chained (mergeChained cur l) := by
  induction l generalizing cur with
  | nil =>
    simp [mergeChained, Chained, hc]
  | cons a rest ih =>
    obtain ⟨hhd, hrest⟩ := List.pairwise_cons.mp hs
    simp only [mergeChained]
    split
    · exact ih (cur.1, max cur.2 a.2) (by dsimp only; omega)
        (fun o ho => hne o (List.mem_cons_of_mem _ ho)) hrest
        (fun o ho => hcl o (List.mem_cons_of_mem _ ho))
    · refine ⟨hc, fun o ho => ?_, ?_⟩
      · have := mergeChained_lb a rest hrest (fun o ho => hhd o ho) o ho
        omega
      · exact ih a (hne a (List.mem_cons_self ..))
          (fun o ho => hne o (List.mem_cons_of_mem _ ho)) hrest
          (fun o ho => hhd o ho)

/-- Pass 1's merge over the collected obstructions: sort by the low
bound, then fuse overlapping and touching intervals. The result is
`Chained` (`mergeIntervals_chained`), which is exactly what makes the
subtraction's skip and cover theorems apply to the drawn rules. -/
def mergeIntervals (obs : Array (Int × Int)) : List (Int × Int) :=
  match (obs.mergeSort fun a b => decide (a.1 ≤ b.1)).toList with
  | [] => []
  | x :: rest => mergeChained x rest

/-- Obstructions with nonempty extents merge into a chained list. -/
theorem mergeIntervals_chained (obs : Array (Int × Int))
    (hne : ∀ o ∈ obs, o.1 ≤ o.2) : Chained (mergeIntervals obs) := by
  unfold mergeIntervals
  split
  · trivial
  · rename_i x rest heq
    have hp : ((obs.mergeSort fun a b => decide (a.1 ≤ b.1)).toList).Pairwise
        (fun a b => a.1 ≤ b.1) := by
      have := Array.pairwise_mergeSort (le := fun a b => decide (a.1 ≤ b.1))
        (xs := obs) (fun a b c hab hbc => by
          simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      exact this.imp (by simp)
    have hmem : ∀ o ∈ (obs.mergeSort fun a b => decide (a.1 ≤ b.1)).toList,
        o.1 ≤ o.2 := by
      intro o ho
      exact hne o (by simpa [Array.mem_mergeSort] using ho)
    rw [heq] at hp hmem
    obtain ⟨hhd, hrest⟩ := List.pairwise_cons.mp hp
    exact mergeChained_chained x rest (hmem x (List.mem_cons_self ..))
      (fun o ho => hmem o (List.mem_cons_of_mem _ ho)) hrest
      (fun o ho => hhd o ho)

/-- Underline rules for one set line: a second walk over its segs, aligned by
gaps, so it can ride as its own `LineOut` at the same baseline — the PDF
writer's x-tracking stays linear and link rectangles see no extra runs. Each
rule sits at its run's own normalized `post` metrics (`Font.band`) and is
interrupted where glyph ink crosses the band — `Font.inkAt`, from the
outline — with a gap of twice the owning run's rule thickness on each side:
CSS Text Decoration 4 §2.10.5 requires skipping "a small distance to either
side of the glyph outline" and leaves the distance UA-defined, so twice the
thickness is this engine's stated choice — it scales with the rule (Hochuli,
Detail in Typography: a rule's weight relates to the stroke it meets) and
absorbs the small band differences between adjacent faces.
Obstructions are collected in line coordinates across the whole line first,
every glyph run contributing whether or not it is underlined, so ink that
reaches over a run boundary — a negative-sidebearing italic descender, or a
descender's clearance spilling past its own advance — clears the
neighbouring rule too. An obstruction is judged against the band of the run
that owns the glyph. The merged obstructions are `Chained`
(`mergeIntervals_chained`) and each run's rules are `subtract` of its span,
so `underline_skips_ink` and `underline_covers_gaps` hold of what ships.
Empty when the line has no underlined run, so the common case allocates
nothing. -/
private def underlineSegs (fs : FontSet) (lineSize : Sp) (segs : Array Seg) :
    Array Seg := Id.run do
  unless segs.any (fun s => match s with
      | .run _ _ _ _ _ _ true _ _ => true
      | _ => false) do
    return #[]
  -- Pass 1: obstruction intervals in line coordinates, each glyph's
  -- ink-in-band intervals scaled to its run's size plus the clearance.
  let mut obs : Array (Sp × Sp) := #[]
  let mut x : Sp := 0
  for seg in segs do
    match seg with
    | .gap w => x := x + w
    | .rule w _ _ _ => x := x + w
    | .image _ w _ => x := x + w
    | .run fontIdx _ _ w glyphs size _ _ _ =>
      let font := fs.get fontIdx
      let sz := if size == 0 then lineSize else size
      let upem : Int := font.unitsPerEm
      let thick := (font.band).2 * sz / upem
      let mut gx : Sp := x
      for (g, _) in glyphs do
        for (ilo, ihi) in font.inkAt g do
          obs := obs.push (gx + ilo * sz / upem - 2 * thick,
            gx + ihi * sz / upem + 2 * thick)
        gx := gx + scaledAt sz font (font.widths[g]?.getD 0)
      x := x + w
  -- Merge into the chained obstruction list the theorems consume.
  let merged := mergeIntervals obs
  -- Pass 2: rules under the underlined runs, minus the obstructions.
  let mut out : Array Seg := #[]
  x := 0
  for seg in segs do
    match seg with
    | .gap w =>
      out := out.push (.gap w)
      x := x + w
    | .rule w _ _ _ =>
      out := out.push (.gap w)
      x := x + w
    | .image _ w _ =>
      out := out.push (.gap w)
      x := x + w
    | .run fontIdx color _ w _ size underline _ _ =>
      if !underline then
        out := out.push (.gap w)
      else
        let font := fs.get fontIdx
        let sz := if size == 0 then lineSize else size
        let upem : Int := font.unitsPerEm
        let (bandPos, bandThick) := font.band
        let top := bandPos * sz / upem
        let thick := bandThick * sz / upem
        let raise := top - thick
        let mut cur : Sp := x
        for (plo, phi) in subtract x (x + w) merged do
          if plo > cur then
            out := out.push (.gap (plo - cur))
          out := out.push (.rule (phi - plo) thick raise color)
          cur := phi
        if x + w > cur then
          out := out.push (.gap (x + w - cur))
      x := x + w
  return out

/-- The geometry of one paragraph line: its segs, x, set width, whether
the break was overfull, the protrusion hang its x was shifted left by,
and its expansion factor. Pure in the builder — it reads only the page
geometry — so the placement pipeline below is the only part of a
paragraph line that touches pages. -/
private def paraLineGeom (fs : FontSet) (j : ParaJob) (b : B) (first : Bool)
    (prev brk : Nat) : Array Seg × Sp × Sp × Bool × Sp × Int :=
  let width := j.target
  let a := if first then lineStart j.items 0 else lineStart j.items (prev + 1)
  let (segs0, w0, overfull, hang, exf) :=
    setLine j.items a brk width (!j.center && j.justify) j.protrude j.expand
  let x0 := if j.center then b.geom.hmargin + j.indent + (width - w0) / 2
    else b.geom.hmargin + j.indent - hang
  -- The marker stands `\labelsep` left of the item: half an em, LaTeX's
  -- own separation (classes.dtx: \setlength\labelsep{.5em}).
  let sep := b.geom.fontSize / 2
  let (segs1, x1, w1) :=
    if first then
      match j.markerSegs with
      | some (ms, mw) =>
        match j.markerIndent with
        | some mi =>
          -- One marker column for the whole block: the gap absorbs the
          -- line's own depth indent on top of `\labelsep`.
          let base := b.geom.hmargin + mi
          let x1 := base - mw - sep
          (ms ++ #[Seg.gap (x0 - base + sep)] ++ segs0, x1, w0 + (x0 - x1))
        | none => (ms ++ #[Seg.gap sep] ++ segs0, x0 - mw - sep, w0 + mw + sep)
      | none => (segs0, x0, w0)
    else (segs0, x0, w0)
  -- The rule fills what the heading left of its line, a word-space away
  -- from the text, where its declared position puts it against the
  -- heading's own face at its own size (`Ir.RulePosition.raise`): half
  -- the x-height up, like a dash — Hochuli, Detail in Typography: a rule
  -- relates to the type it cuts — or on the baseline, as TeX's `\hrule`.
  -- The x-height is the measured ink 'x' (`xHeightOptical`) because OS/2
  -- sxHeight lies in some fonts — the trust order the math size match
  -- already uses.
  let (segs2, w2) :=
    if first then
      match j.rule with
      | some rule =>
        let gap := j.size / 2
        let ruleW := width - w1 - gap
        if ruleW > 0 then
          let xHeight := match segs1.find? (fun s => match s with
            | .run .. => true
            | _ => false) with
            | some (.run idx _ _ _ _ sz _ _ _) =>
              let font := fs.get idx
              let sz := if sz == 0 then j.size else sz
              scaledAt sz font font.xHeightOptical
            | _ => b.xHeight
          let raise := rule.position.raise xHeight
          (segs1 ++ #[Seg.gap gap, Seg.rule ruleW rule.thickness raise rule.color], width)
        else (segs1, w1)
      | none => (segs1, w1)
    else (segs1, w1)
  (segs2, x1, w2, overfull, hang, exf)

/-- What follows a placed paragraph line: its underline siblings (pushed
after `placeLine`, so a page break has already decided where the text
landed; the rules land beside it, adding no vertical space) and the
extra skip a break owes. Neither ships a page. -/
private def placeParaTrailer (fs : FontSet) (j : ParaJob) (brk : Nat)
    (segs : Array Seg) (b : B) : B :=
  let uSegs := underlineSegs fs j.size segs
  let b3 :=
    if uSegs.isEmpty then b
    else match b.cur.lines.back? with
      | some last => b.pushSibling (some
          { x := last.x, y := last.y, size := last.size, segs := uSegs, setWidth := 0 })
      | none => b
  match j.extras[brk]? with
  | some extra => { b3 with skip := { b3.skip with width := b3.skip.width + extra } }
  | none => b3

@[simp] private theorem placeParaTrailer_pages (fs : FontSet) (j : ParaJob)
    (brk : Nat) (segs : Array Seg) (b : B) :
    (placeParaTrailer fs j brk segs b).pages = b.pages := by
  simp only [placeParaTrailer]
  repeat' split
  all_goals first | rfl | simp

@[simp] private theorem placeParaTrailer_noBreak (fs : FontSet) (j : ParaJob)
    (brk : Nat) (segs : Array Seg) (b : B) :
    (placeParaTrailer fs j brk segs b).noBreak = b.noBreak := by
  simp only [placeParaTrailer]
  repeat' split
  all_goals first | rfl | simp

/-- `underline_no_growth`: the underline rules ride a sibling line at the
same baseline and feed nothing back into placement — the trailer leaves
the builder's vertical state (baseline, ink depth, leaded below, page
need) exactly what the text line's own extent set, so an underline can
never move a baseline or grow a line box. Its rules stay inside the
descent band the box already reserves (`Font.underlineBand`). -/
private theorem underline_no_growth (fs : FontSet) (j : ParaJob)
    (brk : Nat) (segs : Array Seg) (b : B) :
    (placeParaTrailer fs j brk segs b).y = b.y ∧
      (placeParaTrailer fs j brk segs b).prevDepth = b.prevDepth ∧
      (placeParaTrailer fs j brk segs b).prevBelow = b.prevBelow ∧
      (placeParaTrailer fs j brk segs b).needed = b.needed := by
  simp only [placeParaTrailer]
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- One break of a paragraph placed: the fold step `placePara` runs over
`breaks`. The threaded state is (builder, previous break, first line).
A named step so `runFloat_whole` can state page preservation by fold
induction — the pipeline's shape is the proof's. -/
private def placeParaLine (fs : FontSet) (j : ParaJob)
    (st : B × Nat × Bool) (brk : Nat) : B × Nat × Bool :=
  let b0 := st.1
  let g := paraLineGeom fs j b0 st.2.2 st.2.1 brk
  let b1 := if g.2.2.2.1 then b0.warnOverfull else b0
  -- The notes whose marks this line carries: mark boxes strictly between
  -- the previous break and this one ride with the line, so the note
  -- follows its mark through fit and spill alike.
  let ns := if j.notes.isEmpty then #[] else
    (j.notes.filter fun n => (st.2.2 || st.2.1 < n.1) && n.1 < brk).map (·.2)
  (placeParaTrailer fs j brk g.1
    (b1.placeLine fs g.2.1 j.size g.1 g.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 ns
      (counted := !j.inFloat) (leaf := j.leaf)), brk, false)

private def placePara (fs : FontSet) (b : B) (j : ParaJob) (breaks : Array Nat) : B :=
  (breaks.foldl (placeParaLine fs j)
    ({ b with diags := b.diags ++ j.diags }, 0, true)).1

/-- The one rewrite of the physical pass: `\pagenumber` / `\pagecount`
become literal text. Running content is laid out after the body, so both
numbers are known by then — no second pass over the document and no aux
file. -/
private def substPageLeaf (n total : Nat)
    (x : Ir.Inline) : Ir.Inline :=
  match x with
  | .pageNumber => .text (toString n)
  | .pageCount => .text (toString total)
  | _ => x

/-- Replace `\pagenumber` / `\pagecount` with literal text, over the
generic map — the descent is `Ir.mapInline`'s, declared once.
`substPage_id` below is its census statement. -/
def substPage (n total : Nat) (xs : Array Ir.Inline) : Array Ir.Inline :=
  Ir.mapInlines (substPageLeaf n total) xs

/-- Content with no physical placeholder survives the physical pass whole:
the substitution half of "the two sequences stay distinct" —
`Ir.frame_sequence_carries_no_physical` is the rendering half. One
instance of the map's conditional-identity schema, with
`Ir.hasPhysicalPage` as the trigger census. -/
theorem substPage_id (n total : Nat) (xs : Array Ir.Inline)
    (h : Ir.hasPhysicalPage xs = false) : substPage n total xs = xs :=
  Ir.mapInlines_id (substPageLeaf n total) Ir.isPhysicalPage
    (fun x hx => by cases x <;> simp_all [Ir.isPhysicalPage, substPageLeaf]) xs h

/-- The two sequences cannot quietly fuse: the physical pass leaves a frame
slot's rendering exactly as the frame numbering rendered it, on every page —
so the frame number in a footer can never be rewritten by, or derived from,
the physical page counter. -/
theorem substPage_leaves_frame_slot (n total k tot : Nat) (s : Ir.ChromeSlot)
    (sec : Array Inline) (hs : s.isFrameSequence = true) :
    substPage n total (s.render sec k tot) = s.render sec k tot :=
  substPage_id n total _ (Ir.frame_sequence_carries_no_physical s sec k tot hs)

/-- One op staged for placement: paragraphs carry their breaking task. -/
private inductive StagedOp where
  | skip (g : Glue)
  | brk
  | pageStyle (bg : Option Ir.Color) (vdist : VDist)
  | titleBar (color : Ir.Color) (pad : Sp)
  | blockBar (color : Ir.Color) (pad x w : Sp)
  | hrule (color : Ir.Color) (thickness : Sp)
  | tableRule (thickness : Sp) (x w : Sp) (segs : Array Seg)
  | pin
  | progress (num den : Nat) (fg bg : Ir.Color) (thick x w : Sp)
  | foot (content : Option (Array Ir.BandSlot)) (frame : Option Nat)
  | para (j : ParaJob) (t : Task (Array Nat))
  | colOpen
  | colNext
  | colClose
  | setLogo (content : Array Ir.Inline)
  | picture (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat)
  | floatOpen
  | floatClose
  | anchor (slug : String)

/-- Placement state saved at a `colOpen`, restored per column: where the
columns start, and the lowest bottom any column reached so far. -/
private structure ColSave where
  y : Sp
  prevDepth : Sp
  prevBelow : Sp
  prevRule : Bool
  skip : Glue
  fresh : Bool
  bottomY : Sp
  bottomDepth : Sp
  bottomBelow : Sp
  bottomRule : Bool

/-- The placement walk's whole state: the page builder, the column-save
stack, the logo spans keyed to page indexes, and the running prose-line
count the measure band reads. One structure so a float group can be
replayed whole (`runFloat`) through the same step every other op takes. -/
private structure StepSt where
  b : B
  colSaves : Array ColSave := #[]
  logoSpans : Array (Nat × Array Ir.Inline) := #[]
  prose : Nat := 0

/-- Fit and place one picture: `placeLine`'s fit-or-spill for a box of
the picture's height, then every shape through one affine transform —
fills and paths as riders, label lines riding the picture's own shrink
(`pushSibling`, `pushLabels`). Its own definition so the placement-step
case analysis stays inside the elaboration budget and the page facts
(`placePicture_extends`, `bgStep_placePicture`) cost one unfold each. -/
private def placePicture (fs : FontSet) (imgs : Image.Store) (b0 : B)
    (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) : B := Id.run do
  let mut b := b0
  -- Fit the picture's box the way `placeLine` fits a line of height
  -- `h` and no depth: at the top of a fresh page, else below the last
  -- line's depth, breaking to a new page when even the shrink above
  -- cannot absorb the overflow.
  let ((px0, py0), (_px1, py1)) := pic.bbox
  let h := py1 - py0
  let bottom := b.geom.bodyBottom
  let mut yTop := b.geom.vmargin
  let mut above : Sp := 0
  let mut overflow : Sp := 0
  if !(b.cur.lines.isEmpty || b.freshStart) then
    let y := b.y + b.prevDepth + b.skip.width + inkClearance
    overflow := y + h - bottom
    above := b.pageShrink + b.skip.shrink
    if overflow ≤ above ∨ b.noBreak then
      yTop := y
      overflow := min overflow above
    else
      b := b.spillPage
      if !b.cur.lines.isEmpty then
        yTop := b.y + b.prevDepth + inkClearance
      overflow := 0
      above := 0
  -- One transform for everything the picture ships: `Pic.Place` is the
  -- affine map the invertibility and containment theorems range over.
  let place : Ir.Pic.Place := { x0 := x, yTop := yTop, xmin := px0, ymax := py1 }
  let mut fills : Array Fill := #[]
  let mut lines : Array LineOut := #[]
  let mut paths : Array PathOut := #[]
  for shape in pic.shapes do
    match shape with
    | .rect rx ry rw rh color =>
      -- The fill's top-left corner is the rect's (min x, max y) corner
      -- through the transform; a negative extent keeps its sorted box.
      let (fx, fy) := place.toPage (min rx (rx + rw), max ry (ry + rh))
      fills := fills.push { x := fx, y := fy,
                            w := max rw (-rw), h := max rh (-rh), color := color }
    | .circle sx sy r st fl =>
      let (pcx, pcy) := place.toPage (sx, sy)
      paths := paths.push { path := .circle pcx pcy (max r (-r))
                            stroke := st, fill := fl }
    | .frame fx fy fw fh st fl =>
      let (qx, qy) := place.toPage (min fx (fx + fw), max fy (fy + fh))
      paths := paths.push { path := .rect qx qy (max fw (-fw)) (max fh (-fh))
                            stroke := st, fill := fl }
    | .edge segs st tip =>
      let pt := place.toPage
      let mapped := segs.map fun sg => match sg with
        | .line x1 y1 x2 y2 =>
          let (a1, b1) := pt (x1, y1)
          let (a2, b2) := pt (x2, y2)
          Ir.Pic.PathSeg.line a1 b1 a2 b2
        | .cubic x1 y1 c1x c1y c2x c2y x2 y2 =>
          let (a1, b1) := pt (x1, y1)
          let (u1, v1) := pt (c1x, c1y)
          let (u2, v2) := pt (c2x, c2y)
          let (a2, b2) := pt (x2, y2)
          Ir.Pic.PathSeg.cubic a1 b1 u1 v1 u2 v2 a2 b2
      paths := paths.push { path := .segs mapped, stroke := some st }
      if let some t := tip then
        let (a1, b1) := pt (t.x1, t.y1)
        let (a2, b2) := pt (t.x2, t.y2)
        let (a3, b3) := pt (t.x3, t.y3)
        paths := paths.push { path := .tri a1 b1 a2 b2 a3 b3
                              fill := some st.color }
    | .label lx ly content color scale align =>
      let size := b.geom.fontSize * (scale : Int) / 1000
      let (items, _, _, _) := itemsOfInlines none size b.xHeight fs {}
        #[.colored color none content] {} imgs b.geom.textWidth b.geom.textHeight
        (ladder := b.geom.scale)
      let breaks := kp items b.geom.textWidth
      if let some brk := breaks[0]? then
        let (segs, w, _, _) := setLine items (lineStart items 0) brk b.geom.textWidth false
        -- The node's box centres on its anchor, as TikZ anchors a node:
        -- the baseline sits below the centre by half the ink height
        -- less half the depth.
        let (hgt, dep) := segs.foldl (fun (acc : Sp × Sp) seg => match seg with
          | .run idx _ _ _ _ sz _ raise _ =>
            let font := fs.get idx
            let sz := if sz == 0 then size else sz
            (max acc.1 (scaledAt sz font font.capHeight.toNat + max 0 raise),
             max acc.2 (scaledAt sz font (-font.descent).toNat + max 0 (-raise)))
          | _ => acc) (0, 0)
        let (cx, cy) := place.toPage (lx, ly)
        -- The anchor decides which point of the label's box sits on
        -- (cx, cy): the centre by default, an edge under a placement
        -- option (pgf §17.5.2).
        let x := match align with
          | .center => cx - w / 2
          | .west => cx
          | .east => cx - w
          | .south | .north => cx - w / 2
        let y := match align with
          | .center | .west | .east => cy + (hgt - dep) / 2
          | .south => cy - dep
          | .north => cy + hgt
        -- Label lines ride with the picture: they share the shrink
        -- above it, so a page set short moves the diagram as one
        -- (pushed below through `pushLabels`, the rider door).
        lines := lines.push { x := x, y := y,
                              size := size, segs := segs, setWidth := w, leaf := leaf }
  b := (b.pushSibling (fills := fills) (paths := paths)).pushLabels lines above
  b := { b with
    pageShrink := above
    needed := max b.needed overflow
    y := yTop + h
    prevDepth := 0
    prevBelow := 0
    prevRuleOnly := false
    skip := {}
    freshStart := false }
  return b

/-- Place one staged op. `floatOpen`/`floatClose` are inert here: the
driver loop consumes the outermost pair (`runFloat`), and an inner pair —
a subfigure inside its parent — is already kept whole by the enclosing
group. -/
private def stepStaged (fs : FontSet) (imgs : Image.Store) (st : StepSt)
    (s : StagedOp) : StepSt := Id.run do
  let mut b := st.b
  let mut colSaves := st.colSaves
  let mut logoSpans := st.logoSpans
  let mut prose := st.prose
  match s with
  | .floatOpen | .floatClose => pure ()
  | .setLogo c =>
    -- The page being built (index `pages.size`) and everything after
    -- carry this content; a later span overrides.
    logoSpans := logoSpans.push (b.pages.size, c)
  | .skip g => b := { b with skip := b.skip.add g }
  | .anchor sl => b := { b with pendingAnchors := b.pendingAnchors.push sl }
  | .brk =>
    -- A boundary closes a page only when the page holds something: two
    -- adjacent frames share one boundary, not an empty page. A style set
    -- for a page that never got content dies with the boundary. Fills
    -- are content too: a picture of fills alone is a page.
    if !b.cur.lines.isEmpty || !b.cur.fills.isEmpty then
      b := { b.finishPage with chrome := none }
    else
      b := { b with pageBg := none, vdist := .top, pageFils := 0, filsAbove := #[],
                    pinnedLines := 0, pinnedFills := 0, chrome := none }
  | .pageStyle bg d => b := { b with pageBg := bg, vdist := d }
  | .foot c fr => b := { b with curFoot := c, curFrame := fr }
  | .pin =>
    -- The resume depth clears the chrome's ink: the title bar (the last
    -- pinned fill) reaches `pad` below the title's depth, and a spill
    -- page's first line spaces off the bar's bottom, not the bare
    -- baseline — without this the resumed line's ascent clipped into the
    -- repeated bar.
    let barBottom := (b.cur.fills.back?.map fun f => f.y + f.h).getD 0
    b := { b with pinnedLines := b.cur.lines.size, pinnedFills := b.cur.fills.size
                  chrome := some (b.cur.lines, b.cur.fills, b.y,
                    max b.prevDepth (barBottom - b.y),
                    max b.prevBelow (barBottom - b.y)) }
  | .colOpen =>
    colSaves := colSaves.push {
      y := b.y, prevDepth := b.prevDepth, prevBelow := b.prevBelow
      prevRule := b.prevRuleOnly, skip := b.skip
      fresh := b.cur.lines.isEmpty || b.freshStart
      bottomY := b.y, bottomDepth := b.prevDepth, bottomBelow := b.prevBelow
      bottomRule := b.prevRuleOnly }
  | .colNext =>
    if let some save := colSaves.back? then
      let save := if b.y > save.bottomY
        then { save with bottomY := b.y, bottomDepth := b.prevDepth
                         bottomBelow := b.prevBelow, bottomRule := b.prevRuleOnly }
        else save
      colSaves := colSaves.pop.push save
      b := { b with y := save.y, prevDepth := save.prevDepth
                    prevBelow := save.prevBelow, prevRuleOnly := save.prevRule
                    skip := save.skip
                    freshStart := save.fresh }
  | .colClose =>
    if let some save := colSaves.back? then
      colSaves := colSaves.pop
      let (bottomY, bottomDepth, bottomBelow, bottomRule) := if b.y > save.bottomY
        then (b.y, b.prevDepth, b.prevBelow, b.prevRuleOnly)
        else (save.bottomY, save.bottomDepth, save.bottomBelow, save.bottomRule)
      b := { b with y := bottomY, prevDepth := bottomDepth
                    prevBelow := bottomBelow, prevRuleOnly := bottomRule
                    skip := {}
                    freshStart := false }
  | .titleBar color pad =>
    -- The bar sits behind the line just placed: full page width, page
    -- top to `pad` below the line's depth. Its bottom edge rides onto
    -- the page (`PageOut.band`) for the corner-logo furniture.
    b := match b.cur.lines.back? with
      | some l =>
        let h := l.y + b.prevDepth + pad
        { b.pushSibling (fills := #[{ x := 0, y := 0, w := b.geom.pageW,
                                      h := h, color := color }]) with
          curBand := some (max h (b.curBand.getD 0)) }
      | none => b
  | .blockBar color pad x w =>
    -- The bar sits behind the line just placed: the measure across, one
    -- `pad` above the line's ink top (the body ascent at the line's own
    -- size) to one below its depth. Fills paint before every glyph run,
    -- so the title's ink stays on top.
    b := match b.cur.lines.back? with
      | some l =>
        let asc := b.ascent * l.size / b.geom.fontSize
        b.pushSibling (fills := #[{ x := x, y := l.y - asc - pad, w := w,
                                    h := asc + b.prevDepth + 2 * pad, color := color }])
      | none => b
  | .hrule color th =>
    -- A line whose only seg is the rule: the full line machinery decides
    -- its place, so skips, page breaks, and the vertical distribution
    -- treat it as they treat text.
    b := b.placeLine fs b.geom.hmargin 0 #[.rule b.geom.textWidth th 0 color]
      b.geom.textWidth
  | .tableRule th x w segs =>
    -- Exactly the pending sep below the previous ink, never a text
    -- leading: the rule's padding is booktabs' declared seps and nothing
    -- else. The seg's ink stands `th` above its baseline, so the
    -- baseline is the band's bottom; `commit` then owes zero depth, and
    -- the interline convention makes the next line stack flush, as TeX
    -- ignores `\prevdepth` after an `\hrule`.
    let mk (y : Sp) : LineOut := { x := x, y := y, size := 0, segs := segs, setWidth := w }
    b := b.fitCommit mk
      (fun b => b.geom.vmargin + th)
      (fun b => b.y + b.prevDepth + b.skip.width + th)
      (fun b => b.y + b.prevDepth + th)
      0 0 true 0 b.geom.bodyBottom
  | .progress num den fg bg thick x w =>
    -- Half a line under the last baseline: the track, then the elapsed
    -- share over it. The bar joins the page's depth so following content
    -- spaces below it.
    let gap := b.geom.fontSize / 2
    let y := b.y + b.prevDepth + gap
    let track : Fill := { x := x, y := y, w := w, h := thick, color := bg }
    let fills := if num == 0 then #[track] else
      #[track, { x := x, y := y, w := w * (num : Int) / (den : Int), h := thick,
                 color := fg }]
    b := { b.pushSibling (fills := fills) with
                  prevDepth := b.prevDepth + gap + thick
                  prevBelow := b.prevBelow + gap + thick }
  | .para j t =>
    let breaks := t.get
    -- A plain full-measure text paragraph is the continuous reading the
    -- measure band is about; headings, items, code, and columns are not.
    if j.target == b.geom.textWidth && !j.center && j.size == b.geom.fontSize &&
        j.markerSegs.isNone && j.rule.isNone then
      prose := max prose breaks.size
    b := placePara fs b j breaks
  | .picture x pic leaf =>
    b := placePicture fs imgs b x pic leaf
  return { b := b, colSaves := colSaves, logoSpans := logoSpans, prose := prose }

/-- Place a float group whole: a float is unbreakable, as LaTeX's floats
are (a float body is a `\vbox` — placed on one page or deferred, never
split across two). The group is tried where it stands; if placing it
broke a page, the try is discarded and the whole group replays on a
fresh page under `noBreak`, so no line of it can split off. A group
taller than the text block itself still ships whole — placed alone, its
overrun named (W0358), never split. -/
private def runFloat (fs : FontSet) (imgs : Image.Store) (st : StepSt)
    (group : Array StagedOp) : StepSt :=
  let attempt := group.foldl (stepStaged fs imgs) st
  if attempt.b.pages.size == st.b.pages.size then attempt
  else
    -- The float and the page bottom met: close the page and give the
    -- group the next one whole. The glue pending before the float dies
    -- with the boundary, as TeX discards glue at the top of a page.
    let b := if st.b.cur.lines.isEmpty && st.b.cur.fills.isEmpty then st.b
      else st.b.finishPage
    let st2 := group.foldl (stepStaged fs imgs)
      { st with b := { b with noBreak := true } }
    let b2 := st2.b
    let overrun := b2.y + b2.prevDepth - noteFloor b2.geom b2.footins b2.notesH
    let b2 := if overrun > b2.pageShrink then
        { b2 with diags := b2.diags.push (Diag.of .W0358
          (s!"a figure or table is {(overrun - b2.pageShrink).toPtString}pt taller " ++
            "than the text block; it overruns its page")
          (help := "shrink the float's content, or raise the text height \
(\\page{ vmargin = ... })")) }
      else b2
    { st2 with b := { b2 with noBreak := false } }

/-! ## `float_whole` — the theorem over the builder

STEER3's statement: every glyph of a float's body and caption in `Out`
shares a page index. The four census tests over `Layout.Out` are the
realisation check; the theorems here are about `runFloat`, the function
that ships the pages. Two facts per placement step carry the result: a
step only ever *extends* the shipped pages (page close appends; nothing
edits or removes a shipped page), and under `noBreak` — a float group
replaying on its own page — a step that is not a page boundary ships
nothing at all. Sourced as the behaviour is: LaTeX's float body is a box
(`ltfloat.dtx`; TeXbook ch. 15's insertions), placed whole or deferred
whole, never split. -/

/-- The shipped pages only grow from `b` to `b'`: nothing edits or
removes a page once it shipped. -/
private def PagesExtend (b b' : B) : Prop := ∃ s, b'.pages = b.pages ++ s

private theorem pagesExtend_refl (b : B) : PagesExtend b b :=
  ⟨#[], by simp⟩

private theorem pagesExtend_of_eq {b c : B} (h : c.pages = b.pages) :
    PagesExtend b c := ⟨#[], by simp [h]⟩

private theorem pagesExtend_trans {a b c : B} :
    PagesExtend a b → PagesExtend b c → PagesExtend a c
  | ⟨s1, h1⟩, ⟨s2, h2⟩ => ⟨s1 ++ s2, by rw [h2, h1, Array.append_assoc]⟩

/-- Transport along "same shipped pages": page-preserving wrappers
(diagnostics, `cur`, skips) around a page-extending step. -/
private theorem pagesExtend_congr {b b' c : B} (h : c.pages = b'.pages)
    (he : PagesExtend b b') : PagesExtend b c :=
  he.imp fun _ hs => h ▸ hs

@[simp] private theorem commit_pages (b : B) (l : LineOut) (d bl : Sp)
    (r c : Bool) (o : Sp) :
    (b.commit l d bl r c o).pages = b.pages := rfl
@[simp] private theorem commit_noBreak (b : B) (l : LineOut) (d bl : Sp)
    (r c : Bool) (o : Sp) :
    (b.commit l d bl r c o).noBreak = b.noBreak := rfl
@[simp] private theorem warnOverfull_pages (b : B) :
    b.warnOverfull.pages = b.pages := rfl
@[simp] private theorem warnOverfull_noBreak (b : B) :
    b.warnOverfull.noBreak = b.noBreak := rfl
@[simp] private theorem pushSibling_pages (b : B) (l? : Option LineOut)
    (fills : Array Fill) (paths : Array PathOut) (shrink : Option Sp) :
    (b.pushSibling l? fills paths shrink).pages = b.pages := by
  cases l? <;> simp only [B.pushSibling] <;> split <;> rfl
@[simp] private theorem pushSibling_noBreak (b : B) (l? : Option LineOut)
    (fills : Array Fill) (paths : Array PathOut) (shrink : Option Sp) :
    (b.pushSibling l? fills paths shrink).noBreak = b.noBreak := by
  cases l? <;> simp only [B.pushSibling] <;> split <;> rfl
@[simp] private theorem pushLabels_pages (b : B) (ls : Array LineOut) (sh : Sp) :
    (b.pushLabels ls sh).pages = b.pages := by
  unfold B.pushLabels
  exact Array.foldl_induction (motive := fun _ (acc : B) => acc.pages = b.pages)
    rfl (fun _ acc h => by rw [pushSibling_pages]; exact h)
@[simp] private theorem pushLabels_noBreak (b : B) (ls : Array LineOut) (sh : Sp) :
    (b.pushLabels ls sh).noBreak = b.noBreak := by
  unfold B.pushLabels
  exact Array.foldl_induction (motive := fun _ (acc : B) => acc.noBreak = b.noBreak)
    rfl (fun _ acc h => by rw [pushSibling_noBreak]; exact h)

@[simp] private theorem commit_geom (b : B) (l : LineOut) (d bl : Sp)
    (r c : Bool) (o : Sp) : (b.commit l d bl r c o).geom = b.geom := rfl
@[simp] private theorem commit_docBg (b : B) (l : LineOut) (d bl : Sp)
    (r c : Bool) (o : Sp) : (b.commit l d bl r c o).docBg = b.docBg := rfl
@[simp] private theorem pushSibling_geom (b : B) (l? : Option LineOut)
    (fills : Array Fill) (paths : Array PathOut) (shrink : Option Sp) :
    (b.pushSibling l? fills paths shrink).geom = b.geom := by
  cases l? <;> simp only [B.pushSibling] <;> split <;> rfl
@[simp] private theorem pushSibling_docBg (b : B) (l? : Option LineOut)
    (fills : Array Fill) (paths : Array PathOut) (shrink : Option Sp) :
    (b.pushSibling l? fills paths shrink).docBg = b.docBg := by
  cases l? <;> simp only [B.pushSibling] <;> split <;> rfl
@[simp] private theorem pushLabels_geom (b : B) (ls : Array LineOut) (sh : Sp) :
    (b.pushLabels ls sh).geom = b.geom := by
  unfold B.pushLabels
  exact Array.foldl_induction (motive := fun _ (acc : B) => acc.geom = b.geom)
    rfl (fun _ acc h => by rw [pushSibling_geom]; exact h)
@[simp] private theorem pushLabels_docBg (b : B) (ls : Array LineOut) (sh : Sp) :
    (b.pushLabels ls sh).docBg = b.docBg := by
  unfold B.pushLabels
  exact Array.foldl_induction (motive := fun _ (acc : B) => acc.docBg = b.docBg)
    rfl (fun _ acc h => by rw [pushSibling_docBg]; exact h)
@[simp] private theorem attachNotes_geom (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).geom = b.geom := by
  unfold B.attachNotes
  split
  · rfl
  · exact Array.foldl_induction (motive := fun _ (acc : B) => acc.geom = b.geom)
      rfl (fun _ _ h => h)
@[simp] private theorem attachNotes_docBg (b : B) (ns : Array NoteBlock) :
    (b.attachNotes ns).docBg = b.docBg := by
  unfold B.attachNotes
  split
  · rfl
  · exact Array.foldl_induction (motive := fun _ (acc : B) => acc.docBg = b.docBg)
      rfl (fun _ _ h => h)
@[simp] private theorem warnNoteOverrun_geom (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).geom = b.geom := by
  simp only [B.warnNoteOverrun]; split <;> rfl
@[simp] private theorem warnNoteOverrun_docBg (b : B) (y d : Sp) :
    (b.warnNoteOverrun y d).docBg = b.docBg := by
  simp only [B.warnNoteOverrun]; split <;> rfl
@[simp] private theorem warnOverfull_geom (b : B) : b.warnOverfull.geom = b.geom := rfl
@[simp] private theorem warnOverfull_docBg (b : B) :
    b.warnOverfull.docBg = b.docBg := rfl
@[simp] private theorem finishPage_geom (b : B) : b.finishPage.geom = b.geom := rfl
@[simp] private theorem finishPage_docBg (b : B) :
    b.finishPage.docBg = b.docBg := rfl
@[simp] private theorem reopenChrome_geom (b : B) : b.reopenChrome.geom = b.geom := by
  unfold B.reopenChrome; split <;> rfl
@[simp] private theorem reopenChrome_docBg (b : B) :
    b.reopenChrome.docBg = b.docBg := by
  unfold B.reopenChrome; split <;> rfl
@[simp] private theorem spillPage_geom (b : B) : b.spillPage.geom = b.geom := by
  simp [B.spillPage]
@[simp] private theorem spillPage_docBg (b : B) : b.spillPage.docBg = b.docBg := by
  simp [B.spillPage]
@[simp] private theorem placeParaTrailer_geom (fs : FontSet) (j : ParaJob)
    (brk : Nat) (segs : Array Seg) (b : B) :
    (placeParaTrailer fs j brk segs b).geom = b.geom := by
  simp only [placeParaTrailer]
  repeat' split
  all_goals first | rfl | simp
@[simp] private theorem placeParaTrailer_docBg (fs : FontSet) (j : ParaJob)
    (brk : Nat) (segs : Array Seg) (b : B) :
    (placeParaTrailer fs j brk segs b).docBg = b.docBg := by
  simp only [placeParaTrailer]
  repeat' split
  all_goals first | rfl | simp

private theorem finishPage_extends (b : B) : PagesExtend b b.finishPage :=
  ⟨#[_], rfl⟩

private theorem fitCommit_extends (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (ns : Array NoteBlock) :
    PagesExtend b
      (b.fitCommit mk firstY stepY retryY depth below rl inkBelow bottom ns) := by
  simp only [B.fitCommit]
  repeat' split
  all_goals first
    | (refine pagesExtend_of_eq ?_; simp; done)
    | (refine pagesExtend_trans (finishPage_extends b) (pagesExtend_of_eq ?_);
       simp; done)

/-- Under `noBreak` a committed band never closes a page and never clears
the flag: the group's one legal position has already been decided. -/
private theorem fitCommit_pages_noBreak (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (ns : Array NoteBlock) (h : b.noBreak = true) :
    (b.fitCommit mk firstY stepY retryY depth below rl inkBelow bottom ns).pages
      = b.pages := by
  simp only [B.fitCommit]
  repeat' split
  all_goals first
    | (simp; done)
    | (exfalso; exact ‹¬(_ ∨ _ = true)› (Or.inr h))

private theorem fitCommit_keeps_noBreak (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (ns : Array NoteBlock) (h : b.noBreak = true) :
    (b.fitCommit mk firstY stepY retryY depth below rl inkBelow bottom ns).noBreak
      = true := by
  simp only [B.fitCommit]
  repeat' split
  all_goals first
    | (simp [h]; done)
    | (exfalso; exact ‹¬(_ ∨ _ = true)› (Or.inr h))

/-- Whatever branch `fitCommit` takes, every line of every note handed in
stands in `pendingNotes` of the SAME builder that holds the committed
band — mark and notes enter together, and spill together (the spill
closes the page before the retry commit, so an earlier line's notes ship
with the earlier page and this line's follow their mark onto the fresh
one). -/
private theorem fitCommit_note_with_mark (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (ns : Array NoteBlock)
    (nb : NoteBlock) (hnb : nb ∈ ns) (l : LineOut) (hl : l ∈ nb.lines) :
    ∃ l' ∈ (b.fitCommit mk firstY stepY retryY depth below rl inkBelow
        bottom ns).pendingNotes,
      l'.segs = l.segs := by
  simp only [B.fitCommit]
  repeat' split
  all_goals
    first
    | (rw [warnNoteOverrun_pendingNotes]
       exact attachNotes_mem _ ns nb hnb l hl)
    | exact attachNotes_mem _ ns nb hnb l hl

private theorem placePicture_extends (fs : FontSet) (imgs : Image.Store)
    (b : B) (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) :
    PagesExtend b (placePicture fs imgs b x pic leaf) := by
  simp only [placePicture, Id.run, Id, pure, bind]
  repeat' split
  all_goals first
    | (refine pagesExtend_of_eq ?_
       simp
       done)
    | (refine pagesExtend_trans
        (pagesExtend_congr (spillPage_pages b) (finishPage_extends b))
        (pagesExtend_of_eq ?_)
       simp
       done)

private theorem placePicture_noBreak (fs : FontSet) (imgs : Image.Store)
    (b : B) (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) (h : b.noBreak = true) :
    (placePicture fs imgs b x pic leaf).pages = b.pages ∧
      (placePicture fs imgs b x pic leaf).noBreak = true := by
  simp only [placePicture, Id.run, Id, pure, bind]
  repeat' split
  all_goals first
    | (exfalso; exact ‹¬(_ ∨ _ = true)› (Or.inr h))
    | (constructor <;> simp [h]
       done)

private theorem placeLine_extends (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) :
    PagesExtend b (b.placeLine fs x size segs w hang ex ns c lf) := by
  simp only [B.placeLine]
  exact fitCommit_extends ..

/-- Under `noBreak` a placed line never closes a page and never clears
the flag: the group's one legal position has already been decided. -/
private theorem placeLine_pages_noBreak (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (h : b.noBreak = true) :
    (b.placeLine fs x size segs w hang ex ns c lf).pages = b.pages := by
  simp only [B.placeLine]
  exact fitCommit_pages_noBreak (h := h) ..

private theorem placeLine_keeps_noBreak (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (h : b.noBreak = true) :
    (b.placeLine fs x size segs w hang ex ns c lf).noBreak = true := by
  simp only [B.placeLine]
  exact fitCommit_keeps_noBreak (h := h) ..

/-- `footnote_with_mark`'s attach half: `fitCommit_note_with_mark` at
`placeLine`'s band. -/
private theorem placeLine_note_with_mark (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) (nb : NoteBlock) (hnb : nb ∈ ns) (l : LineOut) (hl : l ∈ nb.lines) :
    ∃ l' ∈ (b.placeLine fs x size segs w hang ex ns c lf).pendingNotes,
      l'.segs = l.segs := by
  simp only [B.placeLine]
  exact fitCommit_note_with_mark (hnb := hnb) (hl := hl) ..

/-- `placeLine` from a pages-preserving wrapper of `b0` still only
extends `b0`'s shipped pages. -/
private theorem placeLine_extends' (fs : FontSet) (b0 b1 : B)
    (hp : b1.pages = b0.pages) (x size : Sp) (segs : Array Seg) (w hang : Sp)
    (ex : Int) (ns : Array NoteBlock) (c : Bool) (lf : Option Nat) :
    PagesExtend b0 (b1.placeLine fs x size segs w hang ex ns c lf) :=
  pagesExtend_trans (pagesExtend_of_eq hp) (placeLine_extends ..)

private theorem placeParaLine_extends (fs : FontSet) (j : ParaJob)
    (st : B × Nat × Bool) (brk : Nat) :
    PagesExtend st.1 (placeParaLine fs j st brk).1 := by
  simp only [placeParaLine]
  exact pagesExtend_congr (placeParaTrailer_pages ..)
    (placeLine_extends' fs st.1 _ (by split <;> simp) ..)

private theorem placeParaLine_noBreak (fs : FontSet) (j : ParaJob)
    (st : B × Nat × Bool) (brk : Nat) (h : st.1.noBreak = true) :
    (placeParaLine fs j st brk).1.pages = st.1.pages ∧
    (placeParaLine fs j st brk).1.noBreak = true := by
  simp only [placeParaLine]
  constructor
  · rw [placeParaTrailer_pages]
    split <;> rw [placeLine_pages_noBreak] <;> simp [h]
  · rw [placeParaTrailer_noBreak]
    split <;> rw [placeLine_keeps_noBreak] <;> simp [h]

private theorem placePara_extends (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) : PagesExtend b (placePara fs b j breaks) := by
  unfold placePara
  exact Array.foldl_induction
    (motive := fun _ (acc : B × Nat × Bool) => PagesExtend b acc.1)
    (pagesExtend_of_eq (by simp))
    (fun _ acc hacc => pagesExtend_trans hacc (placeParaLine_extends ..))

private theorem placePara_noBreak (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) (h : b.noBreak = true) :
    (placePara fs b j breaks).pages = b.pages ∧
    (placePara fs b j breaks).noBreak = true := by
  unfold placePara
  exact Array.foldl_induction
    (motive := fun _ (acc : B × Nat × Bool) =>
      acc.1.pages = b.pages ∧ acc.1.noBreak = true)
    ⟨rfl, h⟩
    (fun _ acc hacc =>
      have step := placeParaLine_noBreak fs j acc _ hacc.2
      ⟨step.1.trans hacc.1, step.2⟩)

/-- Every placement step extends the shipped pages: nothing pops,
reorders, or rewrites a page that already shipped. With the size check
in `runFloat`, this is what makes "no page was closed" mean "the shipped
pages are exactly what they were". -/
private theorem stepStaged_extends (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (s : StagedOp) : PagesExtend st.b (stepStaged fs imgs st s).b := by
  cases s <;> simp only [stepStaged, Id.run, Id, pure] <;> repeat' split
  all_goals first
    | (refine pagesExtend_of_eq ?_; simp; done)
    | exact fitCommit_extends ..
    | exact placeLine_extends ..
    | exact placePara_extends ..
    | exact placePicture_extends ..
    | (refine pagesExtend_congr ?_ (finishPage_extends _); simp; done)
    | (refine pagesExtend_congr ?_
        (pagesExtend_trans (finishPage_extends _) (pagesExtend_of_eq ?_)) <;> simp <;> done)

/-- Under `noBreak`, a step that is not a page boundary ships nothing
and keeps the flag: the whole group lands on the page being built. -/
private theorem stepStaged_noBreak (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (s : StagedOp) (h : st.b.noBreak = true) (hs : s ≠ .brk) :
    (stepStaged fs imgs st s).b.pages = st.b.pages ∧
    (stepStaged fs imgs st s).b.noBreak = true := by
  cases s <;> simp only [stepStaged, Id.run, Id, pure] <;> repeat' split
  all_goals first
    | exact absurd rfl hs
    | (exfalso; exact ‹¬(_ ∨ _ = true)› (Or.inr h))
    | exact ⟨fitCommit_pages_noBreak (h := h) ..,
        fitCommit_keeps_noBreak (h := h) ..⟩
    | exact ⟨placeLine_pages_noBreak _ _ _ _ _ _ _ _ _ _ h,
        placeLine_keeps_noBreak _ _ _ _ _ _ _ _ _ _ h⟩
    | exact placePara_noBreak _ _ _ _ h
    | exact placePicture_noBreak _ _ _ _ _ _ h
    | (refine ⟨?_, ?_⟩ <;> simp [h]; done)

private theorem foldSteps_extends (fs : FontSet) (imgs : Image.Store)
    (group : Array StagedOp) (st : StepSt) :
    PagesExtend st.b (group.foldl (stepStaged fs imgs) st).b :=
  Array.foldl_induction
    (motive := fun _ (acc : StepSt) => PagesExtend st.b acc.b)
    (pagesExtend_refl st.b)
    (fun _ _acc hacc => pagesExtend_trans hacc (stepStaged_extends ..))

private theorem foldSteps_noBreak (fs : FontSet) (imgs : Image.Store)
    (group : Array StagedOp) (st : StepSt) (h : st.b.noBreak = true)
    (hg : ∀ s ∈ group, s ≠ StagedOp.brk) :
    (group.foldl (stepStaged fs imgs) st).b.pages = st.b.pages ∧
    (group.foldl (stepStaged fs imgs) st).b.noBreak = true :=
  Array.foldl_induction
    (motive := fun _ (acc : StepSt) => acc.b.pages = st.b.pages ∧ acc.b.noBreak = true)
    ⟨rfl, h⟩
    (fun i acc hacc =>
      have step := stepStaged_noBreak fs imgs acc group[i] hacc.2
        (hg group[i] (Array.getElem_mem i.2))
      ⟨step.1.trans hacc.1, step.2⟩)

/-- The full-page background fill `page_background_survives` looks for:
what `finishPage` prepends when the page (or the document) declared a
background. -/
private def bgFilled (g : Geom) (p : PageOut) : Prop :=
  ∃ f ∈ p.fills.toList, f.x = 0 ∧ f.y = 0 ∧ f.w = g.pageW ∧ f.h = g.pageH

/-- One placement step, seen by the background invariant: geometry and
the declared document background ride through untouched, and — when a
background is declared — every page the step ships beyond its input's
is `bgFilled`. Composes (`BgStep.trans`); `finishPage` is the one step
that ships, and it ships filled (`finishPage_bg`). -/
private def BgStep (b b' : B) : Prop :=
  b'.geom = b.geom ∧ b'.docBg = b.docBg ∧
    (b.docBg.isSome = true → ∀ p ∈ b'.pages, p ∈ b.pages ∨ bgFilled b.geom p)

private theorem BgStep.refl (b : B) : BgStep b b :=
  ⟨rfl, rfl, fun _ _p hp => Or.inl hp⟩

private theorem BgStep.of_eq {b c : B} (hg : c.geom = b.geom)
    (hd : c.docBg = b.docBg) (hp : c.pages = b.pages) : BgStep b c :=
  ⟨hg, hd, fun _ _p hpp => Or.inl (hp ▸ hpp)⟩

private theorem BgStep.trans {a b c : B} (h1 : BgStep a b) (h2 : BgStep b c) :
    BgStep a c := by
  obtain ⟨hg1, hd1, hp1⟩ := h1
  obtain ⟨hg2, hd2, hp2⟩ := h2
  refine ⟨hg2.trans hg1, hd2.trans hd1, fun hs p hp => ?_⟩
  rcases hp2 (hd1 ▸ hs) p hp with h | h
  · exact hp1 hs p h
  · exact Or.inr (hg1 ▸ h)

/-- The one shipping step ships filled: the page `finishPage` pushes
carries the full-page background fill whenever the document declared
one — `pageBg.orElse docBg` is some either way, and the fill it selects
is prepended whole, before anything can shift it. -/
private theorem finishPage_bg (b : B) :
    b.docBg.isSome = true → ∀ p ∈ b.finishPage.pages,
      p ∈ b.pages ∨ bgFilled b.geom p := by
  intro hd p hp
  simp only [B.finishPage, Array.mem_push] at hp
  rcases hp with hp | rfl
  · exact Or.inl hp
  · right
    unfold bgFilled
    dsimp only
    rcases hpb : b.pageBg with _ | c
    · rcases hdb : b.docBg with _ | c'
      · rw [hdb] at hd; simp at hd
      · refine ⟨{ x := 0, y := 0, w := b.geom.pageW, h := b.geom.pageH,
                  color := c' }, ?_, rfl, rfl, rfl, rfl⟩
        simp [Option.orElse]
    · refine ⟨{ x := 0, y := 0, w := b.geom.pageW, h := b.geom.pageH,
                color := c }, ?_, rfl, rfl, rfl, rfl⟩
      simp

private theorem bgStep_finishPage (b : B) : BgStep b b.finishPage :=
  ⟨rfl, rfl, finishPage_bg b⟩

private theorem bgStep_spillPage (b : B) : BgStep b b.spillPage :=
  (bgStep_finishPage b).trans
    (BgStep.of_eq (reopenChrome_geom _) (reopenChrome_docBg _) (reopenChrome_pages _))

private theorem bgStep_fitCommit (b : B) (mk : Sp → LineOut)
    (firstY stepY retryY : B → Sp) (depth below : Sp) (rl : Bool)
    (inkBelow bottom : Sp) (ns : Array NoteBlock) :
    BgStep b (b.fitCommit mk firstY stepY retryY depth below rl inkBelow bottom ns) := by
  simp only [B.fitCommit]
  repeat' split
  all_goals first
    | (refine BgStep.of_eq ?_ ?_ ?_ <;> simp
       done)
    | (refine (bgStep_spillPage b).trans (BgStep.of_eq ?_ ?_ ?_) <;> simp
       done)

private theorem bgStep_placeLine (fs : FontSet) (b : B) (x size : Sp)
    (segs : Array Seg) (w hang : Sp) (ex : Int) (ns : Array NoteBlock) (c : Bool)
    (lf : Option Nat) :
    BgStep b (b.placeLine fs x size segs w hang ex ns c lf) := by
  simp only [B.placeLine]
  exact bgStep_fitCommit ..

private theorem bgStep_placePicture (fs : FontSet) (imgs : Image.Store)
    (b : B) (x : Sp) (pic : Ir.Pic.Picture) (leaf : Option Nat) :
    BgStep b (placePicture fs imgs b x pic leaf) := by
  simp only [placePicture, Id.run, Id, pure, bind]
  repeat' split
  all_goals first
    | (refine BgStep.of_eq ?_ ?_ ?_ <;> simp
       done)
    | (refine (bgStep_spillPage b).trans (BgStep.of_eq ?_ ?_ ?_) <;> simp
       done)

private theorem bgStep_placeParaLine (fs : FontSet) (j : ParaJob)
    (st : B × Nat × Bool) (brk : Nat) :
    BgStep st.1 (placeParaLine fs j st brk).1 := by
  simp only [placeParaLine]
  refine BgStep.trans (BgStep.trans ?_ (bgStep_placeLine ..))
    (BgStep.of_eq (placeParaTrailer_geom ..) (placeParaTrailer_docBg ..)
      (placeParaTrailer_pages ..))
  split <;> exact BgStep.of_eq (by simp) (by simp) (by simp)

private theorem bgStep_placePara (fs : FontSet) (b : B) (j : ParaJob)
    (breaks : Array Nat) : BgStep b (placePara fs b j breaks) := by
  unfold placePara
  exact Array.foldl_induction
    (motive := fun _ (acc : B × Nat × Bool) => BgStep b acc.1)
    (BgStep.of_eq rfl rfl (by simp))
    (fun _ acc hacc => hacc.trans (bgStep_placeParaLine ..))

private theorem bgStep_stepStaged (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (op : StagedOp) : BgStep st.b (stepStaged fs imgs st op).b := by
  cases op <;> simp only [stepStaged, Id.run, Id, pure] <;> repeat' split
  all_goals first
    | (refine BgStep.of_eq ?_ ?_ ?_ <;> simp
       done)
    | exact bgStep_fitCommit ..
    | exact bgStep_placeLine ..
    | exact bgStep_placePara ..
    | exact bgStep_placePicture ..
    | (refine (bgStep_finishPage _).trans (BgStep.of_eq ?_ ?_ ?_) <;> simp
       done)

private theorem bgStep_foldSteps (fs : FontSet) (imgs : Image.Store)
    (group : Array StagedOp) (st : StepSt) :
    BgStep st.b (group.foldl (stepStaged fs imgs) st).b :=
  Array.foldl_induction
    (motive := fun _ (acc : StepSt) => BgStep st.b acc.b)
    (BgStep.refl st.b)
    (fun _ _acc hacc => hacc.trans (bgStep_stepStaged ..))

private theorem bgStep_runFloat (fs : FontSet) (imgs : Image.Store)
    (st : StepSt) (group : Array StagedOp) :
    BgStep st.b (runFloat fs imgs st group).b := by
  simp only [LeanTex.Core.Layout.runFloat]
  split
  · exact bgStep_foldSteps ..
  · have h1 : BgStep st.b (if st.b.cur.lines.isEmpty && st.b.cur.fills.isEmpty
        then st.b else st.b.finishPage) := by
      split
      · exact BgStep.refl _
      · exact bgStep_finishPage _
    have h2 := bgStep_foldSteps fs imgs group
      { st with b :=
        { (if st.b.cur.lines.isEmpty && st.b.cur.fills.isEmpty then st.b
           else st.b.finishPage) with noBreak := true } }
    refine (h1.trans ((BgStep.of_eq rfl rfl rfl).trans
      (h2.trans (BgStep.of_eq ?_ ?_ ?_))))
    all_goals repeat' split
    all_goals simp

/-- The index just past the ops of the float group opening before `j`:
the position of the close that returns the nesting `depth` to zero, or
`staged.size` when no close stands (the group then runs to the end).
Never below `j`, which is the driver's termination measure
(`matchingClose_ge`). -/
private def matchingClose (staged : Array StagedOp) (j : Nat) (depth : Nat) : Nat :=
  if h : j < staged.size then
    match staged[j] with
    | .floatOpen => matchingClose staged (j + 1) (depth + 1)
    | .floatClose =>
      if depth == 1 then j else matchingClose staged (j + 1) (depth - 1)
    | _ => matchingClose staged (j + 1) depth
  else j
termination_by staged.size - j

private theorem matchingClose_ge (staged : Array StagedOp) (j depth : Nat) :
    j ≤ matchingClose staged j depth := by
  induction j, depth using matchingClose.induct staged with
  | _ =>
    unfold matchingClose
    simp_all only [dite_true, dite_false, ite_true]
    try split
    all_goals omega

/-- Placement, one op at a time (`stepStaged`) — except a float's ops,
which travel as one unbreakable group between `floatOpen` and its
matching close (`runFloat`). Explicit index recursion (the elabBlocks
knot), so page invariants fold over three named calls: `runFloat`,
`stepStaged`, and the recursion itself. -/
private def placeFrom (fs : FontSet) (imgs : Image.Store)
    (staged : Array StagedOp) (st : StepSt) (si : Nat) : StepSt :=
  if h : si < staged.size then
    match staged[si] with
    | .floatOpen =>
      let j := matchingClose staged (si + 1) 1
      have hj : si + 1 ≤ j := matchingClose_ge staged (si + 1) 1
      placeFrom fs imgs staged (runFloat fs imgs st (staged.extract (si + 1) j))
        (j + 1)
    | s => placeFrom fs imgs staged (stepStaged fs imgs st s) (si + 1)
  else st
termination_by staged.size - si
decreasing_by all_goals omega

private theorem bgStep_placeFrom (fs : FontSet) (imgs : Image.Store)
    (staged : Array StagedOp) (st : StepSt) (si : Nat) :
    BgStep st.b (placeFrom fs imgs staged st si).b := by
  rw [placeFrom]
  split
  · rename_i h
    have hj : si + 1 ≤ matchingClose staged (si + 1) 1 :=
      matchingClose_ge staged (si + 1) 1
    split
    · exact (bgStep_runFloat ..).trans (bgStep_placeFrom ..)
    · exact (bgStep_stepStaged ..).trans (bgStep_placeFrom ..)
  · exact BgStep.refl _
termination_by staged.size - si
decreasing_by all_goals omega

theorem runFloat_whole (fs : FontSet) (imgs : Image.Store) (st : StepSt)
    (group : Array StagedOp) (hg : ∀ s ∈ group, s ≠ StagedOp.brk) :
    (runFloat fs imgs st group).b.pages = st.b.pages ∨
    (runFloat fs imgs st group).b.pages = st.b.finishPage.pages := by
  simp only [runFloat]
  split
  · -- The group fit where it stood: no page closed, and a step only
    -- extends, so the shipped pages are exactly the input's.
    next hsize =>
    left
    obtain ⟨s, hs⟩ := foldSteps_extends fs imgs group st
    have hlen : (group.foldl (stepStaged fs imgs) st).b.pages.size
        = st.b.pages.size := by simpa using hsize
    rw [hs] at hlen ⊢
    simp only [Array.size_append] at hlen
    have hz : s = #[] := by
      rw [← Array.size_eq_zero_iff]; omega
    simp [hz]
  · -- Replay on a fresh page: the only page that can ship is the
    -- pre-float flush; under `noBreak` the group closes nothing.
    have hfold := foldSteps_noBreak fs imgs group
      { st with b :=
        { (if st.b.cur.lines.isEmpty && st.b.cur.fills.isEmpty then st.b
           else st.b.finishPage) with noBreak := true } } rfl hg
    split at hfold
    · left
      repeat' split
      all_goals simp_all
    · right
      repeat' split
      all_goals simp_all

/-- What placement ships, with everything the postlude (furniture,
diagnostic dedup, the outline) still needs: the seam that lets a page
fact proved over the builder cross into `Out` without a proof ever
opening the driver — `runPost_pages` is the crossing. -/
private structure Shipped where
  b : B
  /-- The diagnostics as of shipping — the builder's own plus the
  measure-band check's, carried beside `b` so the builder the page
  facts range over is the bare final close. -/
  diags : Array Diag
  doc : Doc
  geom : Geom
  xHeight : Sp
  pats : Option Hyphen.Patterns
  fs : FontSet
  imgs : Image.Store
  hyphCache : Std.HashMap String (Array Nat)
  navEntries : Array (String × String)
  logoSpans : Array (Nat × Array Ir.Inline)
  plainFoot : Bool
  footSize : Sp
  headY : Sp
  footY : Sp
  chromeFootY : Sp
  muted : Ir.Color

/-- The furniture pass's spine: page `i` gains the running lines its
step computes — and only lines. Everything else on the page (fills,
paths, the foot band, the frame attribution) rides through untouched,
which is what lets a page fact proved at `finishPage` survive to `Out`
(`furnishFrom_keeps`). Explicit index recursion, the elabBlocks knot;
`σ` threads the diagnostics and the hyphenation cache. -/
private def furnishFrom {σ : Type}
    (f : Nat → PageOut → σ → Array LineOut × σ)
    (pages : Array PageOut) (s : σ) (i : Nat) : Array PageOut × σ :=
  if h : i < pages.size then
    let (ls, s') := f i pages[i] s
    furnishFrom f (pages.set i { pages[i] with lines := ls }) s' (i + 1)
  else (pages, s)
termination_by pages.size - i
decreasing_by simp only [Array.size_set]; omega

/-- What the furniture pass cannot do: change anything on a page but its
lines. Every page of the result carries the fills, paths, foot band, and
frame attribution of a page of the input, so a page fact about any of
those proved over the builder's shipped pages survives to `Out`. -/
private theorem furnishFrom_keeps {σ : Type}
    (f : Nat → PageOut → σ → Array LineOut × σ)
    (pages : Array PageOut) (s : σ) (i : Nat) :
    ∀ p ∈ (furnishFrom f pages s i).1, ∃ q ∈ pages,
      p.fills = q.fills ∧ p.paths = q.paths ∧ p.foot = q.foot ∧
        p.frame = q.frame := by
  induction pages, s, i using furnishFrom.induct f with
  | case1 pages s i h ls s' heq ih =>
    intro p hp
    rw [furnishFrom] at hp
    simp only [h, reduceDIte, heq] at hp
    obtain ⟨q, hq, hf⟩ := ih p hp
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hq
    have hj' : j < pages.size := by simpa using hj
    by_cases hij : i = j
    · subst hij
      exact ⟨pages[i], Array.getElem_mem hj', by
        simp only [Array.getElem_set_self] at hf
        exact hf⟩
    · exact ⟨pages[j], Array.getElem_mem hj', by
        simp only [Array.getElem_set, hij, reduceIte] at hf
        exact hf⟩
  | case2 pages s i h =>
    intro p hp
    rw [furnishFrom] at hp
    simp only [h, reduceDIte] at hp
    exact ⟨p, hp, rfl, rfl, rfl, rfl⟩

/-- The postlude: running furniture per page (through `furnishFrom`, so
it can only add lines — `furnishFrom_keeps`), one report per problem,
and the resolved outline. Everything it reads arrives in `Shipped`; the
pages of its result are the builder's pages with furniture lines added
and nothing else touched (`runPost_pages`). -/
private def runPost (sh : Shipped) : Out := Id.run do
  let doc := sh.doc
  let geom := sh.geom
  let xHeight := sh.xHeight
  let pats := sh.pats
  let fs := sh.fs
  let imgs := sh.imgs
  let footSize := sh.footSize
  let plainFoot := sh.plainFoot
  let logoSpans := sh.logoSpans
  let headY := sh.headY
  let footY := sh.footY
  let chromeFootY := sh.chromeFootY
  let mutedC := sh.muted
  let b := sh.b
  let pages := b.pages
  -- Running content is laid out per page once the count is known, into the
  -- margin, so it never disturbs the body it annotates.
  let total := pages.size
  let furnGround := doc.palette.find? "bg"
  -- Margin line numbers (`\page{ linenumbers = on }`): furniture in the
  -- muted role at the footnotesize step, laid here where the head and
  -- foot are — engine-placed margin ink, never body flow. The column
  -- right-aligns left of the measure: a declared `furnituregap` is exact
  -- — the gap from the number's ink to the measure edge — and the
  -- undeclared column hangs from half the margin, `furnEdge`'s own
  -- default convention turned sideways.
  let lineNumbersOn := doc.lineNumbersOn
  let lineModulo := doc.lineModulo
  let numSize := Ir.scaleStep geom.fontSize "footnotesize"
  let numRight := match doc.page.furnitureGap with
    | some g => geom.hmargin - g
    | none => geom.hmargin / 2
  let runLine (content : Array Inline) (n : Nat) (y size : Sp) (baseStyle : TextStyle)
      (cache : _) :
      Option LineOut × Array Diag × _ :=
    let sub := substPage n total content
    let (items, ds, cache, _) :=
      itemsOfInlines pats size xHeight fs { baseStyle with ground := furnGround } sub cache
        imgs geom.textWidth geom.textHeight (ladder := geom.scale)
    let target := geom.textWidth
    let breaks := kp items target
    -- A running line is one line by construction — the band reserves one
    -- line's ink (`furnitureBand`). Content that wraps would silently lose
    -- every line but its first, so losing it is a named diagnostic instead.
    let ds := if breaks.size > 1 then ds.push (Diag.of .W0328
        "running content wraps at the text width; only its first line is kept"
        (help := "the head, foot, and chrome bands hold one line each: shorten the content"))
      else ds
    match breaks[0]? with
    | none => (none, ds, cache)
    | some brk =>
      -- A running line is not a broken-off paragraph line: its leading glue
      -- is content, not break residue. `lineStart` would discard a leading
      -- fill — `\runningfoot{\hfill right}` says the content stands at the
      -- right edge — and the line would collapse to the left margin. Only
      -- leading interword space is skipped; a fill stays and takes the
      -- line's slack.
      let start := Id.run do
        let mut k := 0
        for _ in [0:items.size] do
          match items[k]? with
          | some (Item.glue g) => if g.fil then break else k := k + 1
          | _ => break
        return k
      let (segs, w, _) := setLine items start brk target true
      (some { x := geom.hmargin, y := y, size := size, segs := segs,
              setWidth := w }, ds, cache)
  -- A band slot is a line of its own at natural width, positioned by its
  -- declared side and the geometry alone (`bandSlotX`): nothing another
  -- slot contains enters its box.
  let slotLine (side : Ir.BandSide) (content : Array Inline) (n : Nat)
      (y size : Sp) (baseStyle : TextStyle) (cache : _) :
      Option LineOut × Array Diag × _ :=
    let sub := substPage n total content
    let (items, ds, cache, _) :=
      itemsOfInlines pats size xHeight fs { baseStyle with ground := furnGround } sub cache
        imgs geom.textWidth geom.textHeight (ladder := geom.scale)
    let breaks := kp items geom.textWidth
    -- The band holds one line, as the running bands do: a slot that wraps
    -- loses every line but its first, named, never silent.
    let ds := if breaks.size > 1 then ds.push (Diag.of .W0328
        "running content wraps at the text width; only its first line is kept"
        (help := "the head, foot, and chrome bands hold one line each: shorten the content"))
      else ds
    match breaks[0]? with
    | none => (none, ds, cache)
    | some brk =>
      let (segs, w, _) := setLine items (lineStart items 0) brk geom.textWidth false
      (some { x := bandSlotX geom side w, y := y, size := size, segs := segs,
              setWidth := w }, ds, cache)
  -- The logo: the preamble `\logo` is the initial state, and a `\logo`
  -- block in the body changes it for the pages from that point on — an
  -- empty one clears it, which is how a deck scopes a logo to one frame
  -- (`\logo{...}` before it, `\logo{}` after). One line per state, laid
  -- out once — a logo names no page number — and placed in the furniture
  -- band at the page bottom, at the declared alignment (`Ir.logoAlign`:
  -- right, beamer's default corner, unless the document styles it), its
  -- box standing on the bottom margin line.
  let mkLogoLine (content : Array Inline) (cache0 : Std.HashMap String (Array Nat)) :
      Option LineOut × Array Diag × Std.HashMap String (Array Nat) :=
    let (items, ds, c, _) :=
      itemsOfInlines pats geom.fontSize xHeight fs { ground := furnGround } content cache0
        imgs geom.textWidth geom.textHeight (ladder := geom.scale)
    let breaks := kp items geom.textWidth
    match breaks[0]? with
    | none => (none, ds, c)
    | some brk =>
      let (segs, w, _) := setLine items (lineStart items 0) brk geom.textWidth false
      let x := match Ir.logoAlign doc.styles with
        | "left" => geom.hmargin
        | "center" => (geom.pageW - w) / 2
        | _ => geom.pageW - geom.hmargin - w
      (some { x := x
              y := geom.pageH - geom.vmargin
              size := geom.fontSize, segs := segs, setWidth := w }, ds, c)
  let furnishPage (i : Nat) (page : PageOut)
      (st0 : Array Diag × Std.HashMap String (Array Nat) × Nat) :
      Array LineOut × Array Diag × Std.HashMap String (Array Nat) × Nat := Id.run do
    let mut diags := st0.1
    let mut cache := st0.2.1
    let mut count := st0.2.2
    let mut lines := page.lines
    -- The margin line numbers, one per counted body line at its own
    -- baseline, counting consecutively across pages from 1 — the count
    -- advances on every counted line, and the modulus only filters what
    -- prints (lineno's \modulolinenumbers, the user-commands section).
    if lineNumbersOn then
      for l in page.lines do
        if l.counted then
          count := count + 1
          if count % lineModulo == 0 then
            let (items, ds, c, _) :=
              itemsOfInlines pats numSize xHeight fs
                { color := mutedC, ground := furnGround }
                #[.text (toString count)] cache imgs geom.textWidth geom.textHeight
                (ladder := geom.scale)
            diags := diags ++ ds
            cache := c
            let breaks := kp items geom.textWidth
            if let some brk := breaks[0]? then
              let (segs, w, _) := setLine items (lineStart items 0) brk
                geom.textWidth false
              lines := lines.push { x := numRight - w, y := l.y, size := numSize
                                    segs := segs, setWidth := w, furniture := true }
    -- Pages before a declaration's own `from` carry none of it: an opening
    -- page reads as a title page, not as page one of a run. Each gate is
    -- the physical-page model's and each declaration's own
    -- (`\runninghead[from = 2]` gates the head, never its sibling foot), so
    -- it governs only the physical furniture — head, foot, and the logo,
    -- which rides the running band and waits for the later of the two. The
    -- chrome footer is frame furniture on the frame model: whether a page
    -- carries it is decided by its frame's number, and a physical
    -- declaration must not silently gate it.
    let headOn := doc.headFrom ≤ i + 1
    let footOn := doc.footFrom ≤ i + 1
    if headOn then
      if let some content := doc.head then
        let (l?, ds, c) := runLine content (i + 1) headY geom.fontSize {} cache
        diags := diags ++ ds
        cache := c
        if let some l := l? then lines := #[{ l with furniture := true }] ++ lines
    if footOn then
      if let some content := doc.foot then
        let (l?, ds, c) := runLine content (i + 1) footY geom.fontSize {} cache
        diags := diags ++ ds
        cache := c
        if let some l := l? then lines := lines.push { l with furniture := true }
      else if plainFoot then
        -- plain's foot, by content: the page number between two fills is
        -- the engine's spelling of `\hfil\thepage\hfil` (ltpage.dtx,
        -- `\ps@plain`), centred by the same setter every declared foot
        -- runs through.
        let (l?, ds, c) := runLine #[.fill, .pageNumber, .fill] (i + 1) footY
          geom.fontSize {} cache
        diags := diags ++ ds
        cache := c
        if let some l := l? then lines := lines.push { l with furniture := true }
    -- The headline band's corner logos (`\logoleft`/`\logoright`): laid
    -- once per page carrying a page-top bar (`PageOut.band`), the `\logo`
    -- machinery's shape — one set line of inline content, x pinned to the
    -- safe margin on the declared side, the ink centred in the band's
    -- fill (the lineage's own vertical centring). Content wider than the
    -- band's corner is the document's to judge; the logo is furniture and
    -- stands outside the body-ink census.
    if let some bandB := page.band then
      for (content?, left) in [(doc.logoLeft, true), (doc.logoRight, false)] do
        if let some content := content? then
          let (items, lds, c, _) :=
            itemsOfInlines pats geom.fontSize xHeight fs { ground := furnGround }
              content cache imgs geom.textWidth geom.textHeight
          diags := diags ++ lds
          cache := c
          let breaks := kp items geom.textWidth
          if let some brk := breaks[0]? then
            let (segs, w, _) := setLine items (lineStart items 0) brk geom.textWidth false
            -- Ink above the baseline: an image's declared height; a glyph
            -- run's size stands in for its ascent (the band centring's
            -- only consumer of the estimate).
            let inkH := segs.foldl (init := (0 : Sp)) fun m sg => match sg with
              | .image _ _ h => max m h
              | .run _ _ _ _ _ size _ raise _ => max m (size + raise)
              | _ => m
            let x := if left then geom.hmargin else geom.pageW - geom.hmargin - w
            lines := lines.push { x := x, y := (bandB + inkH) / 2,
                                  size := geom.fontSize, segs := segs,
                                  setWidth := w, furniture := true }
    -- The chrome footer the page's frame gave it, slot by slot: the muted
    -- key at the scale's small step, both from declarations. Positions are
    -- fixed (`bandSlotX`); when two boxes collide the lower-rank slot
    -- yields — painted first, so every higher slot paints over it — and the
    -- yield is reported by name (W0333). No box moves: yielding is by ink,
    -- never by position.
    if let some band := page.foot then
      let mut placed : Array (Ir.BandSlot × LineOut) := #[]
      for slot in band do
        let (l?, ds, c) := slotLine slot.side slot.content (i + 1) chromeFootY
          footSize { color := mutedC } cache
        diags := diags ++ ds
        cache := c
        if let some l := l? then placed := placed.push (slot, { l with furniture := true })
      let slots := placed
      for hj : j in [0:slots.size] do
        for hk : k in [j+1:slots.size] do
          let (a, la) := slots[j]
          let (bs, lb) := slots[k]
          if la.x < lb.x + lb.setWidth && lb.x < la.x + la.setWidth then
            let (lo, hi) := if a.rank < bs.rank then (a, bs) else (bs, a)
            diags := diags.push (Diag.of .W0333
              s!"the footer's slots collide on page {i + 1}: {lo.label} \
yields, painted over by {hi.label}"
              (help := "slot positions are fixed and the lower-priority \
slot yields in place: shorten the content or drop a slot"))
      for p in slots.qsort (fun a b => a.1.rank < b.1.rank) do
        lines := lines.push p.2
    let logoContent := Ir.logoInForce doc.logo logoSpans i
    if headOn && footOn then
      if let some content := logoContent then
        unless content.isEmpty do
          let (l?, ds, c) := mkLogoLine content cache
          diags := diags ++ ds
          cache := c
          if let some l := l? then lines := lines.push { l with furniture := true }
    return (lines, diags, cache, count)
  let fout := furnishFrom furnishPage pages (sh.diags, sh.hyphCache, 0) 0
  let out := fout.1
  let diags := fout.2.1
  -- One report per problem: the same missing glyph or overfull shape in
  -- thirty code blocks is one thing to fix, not thirty lines of console.
  -- W0005 is spanless and always the same words, so its collapse keeps the
  -- count: the number is the only signal of scale the warning has.
  let mut seen : Std.HashSet (String × String) := {}
  let mut unique : Array Diag := #[]
  let overfull := diags.foldl (fun n d => if d.code == "W0005" then n + 1 else n) 0
  for d in diags do
    let key := (d.code, d.message)
    unless seen.contains key do
      seen := seen.insert key
      if d.code == "W0005" && overfull > 1 then
        unique := unique.push
          { d with message := s!"{overfull} overfull lines (no feasible break)" }
      else
        unique := unique.push d
  -- The document outline, resolved: an in-document target (`#anchor`)
  -- resolves against the level-1 heading anchors the builder recorded —
  -- the first declaration wins, exactly the section an in-page `#anchor`
  -- link reaches — and any other target rides as its URL.
  let outline := sh.navEntries.map fun (title, target) =>
    if target.startsWith "#" then
      { title := title
        page := (b.anchors.find? (·.1 == (target.drop 1).toString)).map (·.2) }
    else ({ title := title, url := some target } : OutlineEntry)
  return { pages := out, diags := unique, outline := outline }

/-- The postlude only adds furniture lines: every page of `runPost`'s
output carries the fills, paths, foot band, and frame attribution of a
page the builder shipped — `furnishFrom_keeps` lifted over the whole
postlude, the seam a builder invariant crosses into `Out` through. -/
private theorem runPost_pages (sh : Shipped) :
    ∀ p ∈ (runPost sh).pages, ∃ q ∈ sh.b.pages,
      p.fills = q.fills ∧ p.paths = q.paths ∧ p.foot = q.foot ∧
        p.frame = q.frame := by
  intro p hp
  unfold runPost at hp
  dsimp only [Id.run, bind, pure, Id] at hp
  exact furnishFrom_keeps _ _ _ _ p hp

/-- The marks step, the one seam after the furniture pass: every shipped
page takes the derived cut-mark fills, appended after its own fills so
the marks paint over any background. -/
def addMarks (out : Out) (m : Array Fill) : Out :=
  { out with pages := out.pages.map fun p => { p with fills := p.fills ++ m } }

/-- What the marks step does to a shipped page, read backwards: every
page of `addMarks` is a pre-marks page with the mark fills appended —
the seam `page_background_survives` crosses. -/
theorem addMarks_mem (out : Out) (m : Array Fill) (p : PageOut)
    (hp : p ∈ (addMarks out m).pages) :
    ∃ q ∈ out.pages, p.fills = q.fills ++ m := by
  obtain ⟨q, hq, rfl⟩ := Array.mem_map.mp hp
  exact ⟨q, hq, rfl⟩

/-- The mark fills a document's pages take: the derived eight when marks
are declared and the declared gap fits inside the bleed (`cutMarks`),
nothing otherwise. Painted in the registration reading
(`Ir.Color.registration`): CMYK 1,1,1,1 when the document declares print
colours, black otherwise. -/
private def markFillsOf (geom : Geom) (doc : Doc) : Array Fill :=
  if geom.marks && geom.markGap < geom.bleed && 0 < geom.markThick then
    cutMarks geom.pageW geom.pageH geom.bleed geom.markGap geom.markThick
      (Ir.Color.registration (doc.palette.entries.any (·.2.cmyk.isSome)))
  else #[]

/-- The document as the paged backend reads it: backend conditionals
resolved at the entry (`Ir.keepFor_covers` is why dropping here cannot
lose content). The structure tree the attribution channel indexes is
`Struct.ofDoc (pdfView doc)` — the tree of exactly the content the pages
set. -/
def pdfView (doc : Doc) : Doc := { doc with body := Ir.keepFor "pdf" doc.body }

/-- The whole pipeline up to the marks seam: placement, the close, and
the furniture pass. `run` is this plus `addMarks`; the split keeps each
half's proof (`runCore_bg`, `addMarks_mem`) inside its own elaboration
budget — the giant term is crossed once per theorem, not twice in one. -/
private def runCore (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Doc) (imgs : Image.Store := {}) :
    Out := Id.run do
  -- The PDF's view of the document: backend conditionals resolve here, at
  -- the backend's entry, so no later pass can see content another backend
  -- owns.
  let doc := pdfView doc
  -- The geometry decides whether patterns apply at all: a card never
  -- hyphenates, whoever loaded the patterns.
  let pats := if geom.hyphenate then pats else none
  let font := fs.body
  let scale (u : Int) : Sp := u * geom.fontSize / font.unitsPerEm
  -- The chrome footer draws when the document (usually through its theme)
  -- declared one — `\chrome` slots or a `\framefoot` note — and no
  -- \runningfoot overrides it, and only on slides: chrome is deck
  -- furniture. `\framefoot` wraps frames, so the scan is over top-level
  -- blocks, where elaboration puts it.
  let footAllowed := doc.docClass.record.chrome && doc.foot.isNone
  let hasFrameFoot := doc.body.any fun blk => match blk with
    | .framefoot xs => !xs.isEmpty
    | _ => false
  let chromeActive := footAllowed && (doc.chrome.hasFooter || hasFrameFoot)
  -- The flow default article carries: plain's centred page number in the
  -- foot (`ClassRecord.pageNumbers`; article.cls initialises
  -- `\pagestyle{plain}`, classes.dtx), unless a `\runningfoot` already
  -- owns the band or the document declared `numbers = off`. The number
  -- rides the same furniture emitter every declared foot does — `runLine`
  -- over `substPage` — so it is one more content in an existing path,
  -- never a second footer model.
  let plainFoot := doc.foot.isNone && doc.pageNumbersOn
  -- The footer's size is a step of the scale and its colour a palette key,
  -- never a literal: the theme declares both.
  let footSize := Ir.scaleStep geom.fontSize "small"
  -- The running line's ink extents: the body face at the page size for a
  -- declared head or foot and the plain number, the small step for chrome
  -- slots. One `furnitureBand` per side from the same ink and gap is what
  -- makes the two edges one number (`furniture_symmetric`); the declared
  -- gap is read here — the native ink key directly, the LaTeX spellings
  -- through the one baseline-to-ink correction (`furnGapOfSep`).
  let runInk := scale font.ascent + scale (-font.descent)
  let chromeScale (u : Int) : Sp := u * footSize / (font.unitsPerEm : Int)
  let chromeInk := chromeScale font.ascent + chromeScale (-font.descent)
  let corr := scale (-font.descent)
  let gapTop := doc.page.furnitureGap <|> doc.page.headsep.map (furnGapOfSep · corr)
  let gapBot := doc.page.furnitureGap <|> doc.page.footskip.map (furnGapOfSep · corr)
  let headFurn := furnitureBand geom.vmargin runInk gapTop
  let footFurn := furnitureBand geom.vmargin runInk gapBot
  let chromeFurn := furnitureBand geom.vmargin chromeInk
    (doc.page.furnitureGap <|>
      doc.page.footskip.map (furnGapOfSep · (chromeScale (-font.descent))))
  -- A footer reserves its band before anything is placed, so no body line
  -- can land in it (`bodyBottom_clears_footer` is the sufficiency proof).
  -- With the default margins the half margin holds the foot line whole and
  -- the band is zero: an undeclared page is unchanged.
  let geom := if doc.foot.isSome || plainFoot then
      { geom with footBand := footFurn.band }
    else if chromeActive then
      { geom with footBand := chromeFurn.band }
    else geom
  -- The running head reserves its band the same way, before anything is
  -- placed (`bodyTop_clears_head` is the sufficiency proof). With the
  -- default margins the half margin holds the head line whole and the
  -- band is zero: an undeclared page is unchanged.
  let geom := if doc.head.isSome then
      { geom with headBand := headFurn.band }
    else geom
  let xHeight := scale font.xHeight
  -- The resolved design is the one resolving site for the document-level
  -- colours (`Design.ofDoc`): the ink here is the ink `Contrast.docDiags`
  -- judges (`judged_pair_is_shipped`), never a second `getD` chain.
  let design := Ir.Design.ofDoc doc
  let cover := design.cover
  let rd : Rd := { geom := geom, xHeight := xHeight, pats := pats, fs := fs
                   styles := doc.styles
                   locale := doc.info.locale
                   slides := doc.docClass.record.model == .frame
                   imgs := imgs
                   headline := doc.headline }
  let acc0 : Acc := { pal := doc.palette
                      tokens := doc.tokens
                      frameCount := doc.frameCount
                      chromeL := if footAllowed then doc.chrome.footerLeft else none
                      chromeR := if footAllowed then doc.chrome.footerRight else none
                      footAllowed := footAllowed
                      fg := design.fg
                      ground := doc.palette.find? "bg" }
  -- One handout page per overlay step, driven here at the top level: a
  -- multi-step frame collects once per step with pending content dimmed
  -- (`Ir.dimBlocks`), under ONE frame number — the furniture belongs to the
  -- frame, not the step, so a stepped frame's pages share their progress
  -- position and their frame count. Steps and standout are orthogonal: the
  -- flag rides onto every step page unchanged. The number itself is read
  -- off `Ir.frameNumbers`, the one numbering (its T2–T4 are the contract);
  -- nothing below this loop counts.
  let nums := doc.frameNumbers
  let mut acc := acc0
  let mut firstBlk := true
  for h : i in [0:doc.body.size] do
    let blk := doc.body[i]
    -- A stateful declaration is not content: no gap before it, and the
    -- scope's first real block stays first.
    acc := if firstBlk || statefulBlock blk then acc else acc.wantGap
    firstBlk := firstBlk && statefulBlock blk
    match blk with
    | .frame title standout valign body =>
      let num := nums[i]?.getD none
      acc := { acc with frameNum := num, framesDone := num.getD acc.framesDone }
      let steps := Ir.maxStepBlocks body
      if steps ≤ 1 then
        acc := collectBlock rd acc
          (.frame title standout valign (Ir.unwrapItemSteps body)) 0
      else
        -- The tree numbers the frame once; every step's pages name the same
        -- leaves, so the counter rewinds to the frame's start per step
        -- (dimming recolours and unwrapping splices: neither moves a leaf).
        let leafStart := acc.leafNext
        for k in [1:steps + 1] do
          acc := collectBlock rd { acc with leafNext := leafStart }
            (.frame title standout valign (Ir.unwrapItemSteps (Ir.dimBlocks cover k body))) 0
    | other => acc := collectBlock rd acc (Ir.unwrapItemStep other) 0
  -- Trailing fil glue stretches on the page it ends (a \vfill nothing
  -- follows is how a page bottom-flushes its leftover), so it must reach
  -- placement; trailing finite glue stays invisible and stays dropped.
  let accF := if acc.owed.any (·.fil) then
      { acc with ops := acc.ops.push (.skip (acc.owed.foldl Glue.add {})) }
    else acc
  -- Break every paragraph in parallel: `kp` is pure and each job independent,
  -- so the tasks race on nothing; joining in document order below keeps the
  -- output independent of scheduling.
  let staged : Array StagedOp := accF.ops.map fun op =>
    match op with
    | .skip g => .skip g
    | .brk => .brk
    | .pageStyle bg c => .pageStyle bg c
    | .titleBar color pad => .titleBar color pad
    | .blockBar color pad x w => .blockBar color pad x w
    | .hrule color th => .hrule color th
    | .tableRule th x w segs => .tableRule th x w segs
    | .pin => .pin
    | .progress num den fg bg thick x w => .progress num den fg bg thick x w
    | .foot c fr => .foot c fr
    | .para j => .para j (Task.spawn fun _ =>
        kpTwoPass j.items j.target (j.protrude && j.justify && !j.center)
          (j.expand && j.justify && !j.center))
    | .colOpen => .colOpen
    | .colNext => .colNext
    | .colClose => .colClose
    | .setLogo c => .setLogo c
    | .picture x pic leaf => .picture x pic leaf
    | .floatOpen => .floatOpen
    | .floatClose => .floatClose
    | .anchor sl => .anchor sl
  -- A declared asymmetry that survives the reading is named: equal gaps
  -- are the default, and a difference is exactly what the document asked
  -- for — the hand-struck footskip patch made visible instead of doubled.
  let preDiags := if let (some gt, some gb) := (gapTop, gapBot) then
      if gt != gb then
        acc.diags.push (Diag.of .N0021
          (s!"header and footer gaps differ by " ++
            s!"{(if gt > gb then gt - gb else gb - gt).toPtString}pt as declared; " ++
            "equal gaps are the default"))
      else acc.diags
    else acc.diags
  -- A heading binds to the text it introduces, so its space above must not
  -- be the smaller of the two (the standard rule; Butterick, "space above
  -- and below": the space below should be smaller so the heading sits
  -- visually closer to what follows). Checked only when the document
  -- declared both sides — the defaults satisfy it by theorem.
  let preDiags := ["section", "subsection", "subsubsection"].foldl (fun ds element =>
    match doc.styles.find? element with
    | some st =>
      match st.before, st.after with
      | some before, some after =>
        let up := (before.resolve geom.fontSize xHeight).width
        let down := (after.resolve geom.fontSize xHeight).width
        if down > up then
          ds.push (Diag.of .W0202
            (s!"'{element}' sets more space below the heading " ++
              s!"({down.toPtString}pt) than above it ({up.toPtString}pt)")
            (help := s!"a heading binds to the text it introduces: in " ++
              s!"\\style\{{element}}\{...} keep 'after' at most 'before'"))
        else ds
      | _, _ => ds
    | none => ds) preDiags
  let b0 : B := {
    geom := geom
    ascent := scale font.ascent
    descent := scale (-font.descent)
    capHeight := scale font.capHeight
    xHeight := xHeight
    docBg := if design.bgDeclared then some design.bg else none
    footins := ((doc.tokens.find? "footins").getD
      (Ir.footinsDefault geom.fontSize)).resolve geom.fontSize xHeight |>.width
    noteInk := design.fg
    diags := preDiags
  }
  -- Placement, one op at a time (`stepStaged`) — except a float's ops,
  -- which travel as one unbreakable group between `floatOpen` and its
  -- matching close (`runFloat`).
  let st : StepSt := placeFrom fs imgs staged { b := b0 } 0
  let logoSpans := st.logoSpans
  let prose := st.prose
  -- The trailing boundary of a final frame has already closed its page; a
  -- document is never given an empty page for it.
  let b := if !st.b.cur.lines.isEmpty || !st.b.cur.fills.isEmpty
      || st.b.pages.isEmpty then
      st.b.finishPage
    else st.b
  -- The measure, checked against the readable band once the document has
  -- shown continuous text (a paragraph of four or more full-measure lines).
  -- Bringhurst: 45–75 characters is satisfactory for a single column of
  -- text-size prose and 66 is the ideal (Elements §2.1.2); Butterick allows
  -- 45–90. The character count comes from the body face's own lowercase
  -- alphabet length through the copy-fitting table's fitted lines
  -- (memoir manual eqs. 2.1–2.2: L₆₅ = 2.042α + 33.41 pt,
  -- L₄₅ = 1.415α + 23.03 pt). Slides are display text, not continuous
  -- reading, and are out of the rule's own scope; `\page{ measure = free }`
  -- declares the document takes responsibility.
  let shipDiags :=
    if doc.docClass.record.measureBand && doc.page.measureChecked
        && prose ≥ 4 then
      let alphabet := (List.range 26).foldl (fun acc k =>
        acc + scaledAt geom.fontSize font (font.advance (Char.ofNat ('a'.toNat + k)))) 0
      if alphabet > 0 then
        let l45 := 1415 * alphabet / 1000 + 2303 * spPerPt / 100
        let l65 := 2042 * alphabet / 1000 + 3341 * spPerPt / 100
        let cpl10 := 450 + 200 * (geom.textWidth - l45) / (l65 - l45)
        if cpl10 < 450 || cpl10 > 900 then
          let dir := if cpl10 > 900 then "narrow" else "widen"
          b.diags.push (Diag.of .W0201
            (s!"the measure holds about {(cpl10 + 5) / 10} characters " ++
              "per line, outside the readable 45\u201390 band")
            (help := s!"{dir} the text block (\\page\{ hmargin = ... }; 66 characters " ++
              "is the ideal) or declare \\page{ measure = free }"))
        else b.diags
      else b.diags
    else b.diags
  runPost {
    b := b
    diags := shipDiags
    doc := doc
    geom := geom
    xHeight := xHeight
    pats := pats
    fs := fs
    imgs := imgs
    hyphCache := acc.hyphCache
    navEntries := acc.navEntries
    logoSpans := logoSpans
    plainFoot := plainFoot
    footSize := footSize
    headY := furnHeadY headFurn (scale font.ascent)
    footY := furnFootY footFurn geom.pageH (scale (-font.descent))
    chromeFootY := furnFootY chromeFurn geom.pageH
      (chromeScale (-font.descent))
    muted := design.muted }

/-- Typeset a document body into positioned pages. Geometry is resolved by
the caller via `Geom.ofPage`, so layout has one source of truth. Printer's
cut marks, when declared, join every shipped face here — the marks seam
(`addMarks`) after the furniture pass, so spilled, stepped, and chrome
pages alike carry the same eight, painted over any background. -/
def run (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns) (doc : Doc)
    (imgs : Image.Store := {}) : Out :=
  addMarks (runCore geom fs pats doc imgs) (markFillsOf geom doc)

/-- The background fact over the pre-marks pipeline: every page `runCore`
ships under a declared `bg` carries the full-page fill. The proof is
three seams: `finishPage_bg` (the one shipping door prepends the fill
whole), `bgStep_placeFrom` (every placement step preserves the
invariant), and `runPost_pages` (the furniture pass cannot touch
fills). -/
private theorem runCore_bg
    (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store)
    (hbg : (doc.palette.find? "bg").isSome = true) :
    ∀ p ∈ (runCore geom fs pats doc imgs).pages,
      ∃ f ∈ p.fills.toList,
        f.x = 0 ∧ f.y = 0 ∧ f.w = geom.pageW ∧ f.h = geom.pageH := by
  have key : ∀ (b0 c : B), BgStep b0 c →
      b0.docBg.isSome = true → b0.pages = #[] →
      ∀ x ∈ c.pages, bgFilled b0.geom x := by
    intro b0 c hc hd hemp x hx
    rcases hc.2.2 hd x hx with h | h
    · rw [hemp] at h
      simp at h
    · exact h
  intro p hp
  unfold runCore at hp
  dsimp only [Id.run, bind, pure, Id] at hp
  obtain ⟨q, hq, hfills, -, -, -⟩ := runPost_pages _ p hp
  have fin : ∀ (b0 : B), bgFilled b0.geom q →
      b0.geom.pageW = geom.pageW → b0.geom.pageH = geom.pageH →
      ∃ f ∈ p.fills.toList,
        f.x = 0 ∧ f.y = 0 ∧ f.w = geom.pageW ∧ f.h = geom.pageH := by
    intro b0 h hW hH
    obtain ⟨f, hf, hx, hy, hw, hh⟩ := h
    exact ⟨f, hfills ▸ hf, hx, hy, hW ▸ hw, hH ▸ hh⟩
  -- the final close, taken abstractly: splitting the giant term is the
  -- wall, so the ite is covered by a lemma over an opaque condition
  have bgStep_close : ∀ (c : Prop) [inst : Decidable c] (b0 X : B),
      BgStep b0 X → BgStep b0 (if c then X.finishPage else X) := by
    intro c inst b0 X h
    split
    · exact h.trans (bgStep_finishPage _)
    · exact h
  refine fin _ (key _ _ (bgStep_close _ _ _ (bgStep_placeFrom ..)) ?_ rfl q hq)
    ?_ ?_
  all_goals first
    | (simp [Ir.Design.ofDoc, pdfView, hbg]
       done)
    | (try dsimp only
       repeat' split
       all_goals rfl)

/-- Every page of a document that declares a `bg` palette entry ships a
full-page fill: what the walk attaches to a page survives to that page's
output, observed at the page background. Discharged from `Obligations`
(arch-provable I5; the fill-vanishing bug — `B.commit` once rebuilt the
page with only its lines, PLAN 2026-09-16 — is its counterexample).
`runCore_bg` carries the pipeline's three seams; the marks step is the
fourth and only appends (`addMarks_mem`), so the fill rides through. -/
theorem page_background_survives
    (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (imgs : Image.Store)
    (hbg : (doc.palette.find? "bg").isSome = true) :
    ∀ p ∈ (run geom fs pats doc imgs).pages,
      ∃ f ∈ p.fills.toList,
        f.x = 0 ∧ f.y = 0 ∧ f.w = geom.pageW ∧ f.h = geom.pageH := by
  intro p hp
  unfold run at hp
  obtain ⟨p0, hp0, hpf⟩ := addMarks_mem _ _ _ hp
  obtain ⟨f, hf, hx, hy, hw, hh⟩ := runCore_bg geom fs pats doc imgs hbg p0 hp0
  have hf0 : f ∈ p0.fills := Array.mem_toList_iff.mp hf
  have hfp : f ∈ p.fills.toList := by
    rw [hpf, Array.mem_toList_iff]
    exact Array.mem_append.mpr (Or.inl hf0)
  exact ⟨f, hfp, hx, hy, hw, hh⟩

end LeanTex.Core.Layout
