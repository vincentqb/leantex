import Std.Data.HashSet
import LeanTex.Core.Dim
import LeanTex.Core.Font
import LeanTex.Core.Hyphen
import LeanTex.Core.Ir
import LeanTex.Core.Oklab
import LeanTex.Core.ListMark
import LeanTex.Core.Diag

namespace LeanTex.Core.Layout

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font LeanTex.Core.Ir

structure Geom where
  pageW : Sp := pt 612
  pageH : Sp := pt 792
  hmargin : Sp := inch 1
  vmargin : Sp := inch 1
  fontSize : Sp := Ir.baseFontSize
  /-- The gap between peer paragraphs. The default is the engine's own; a
  document declares its own through `\page{ parskip = ... }`. -/
  parskip : SymGlue := { width := Dim.Length.ofSp (pt 6) }
  /-- Per-level list indent. The default is the engine's own choice — 1.5 em
  at the 10 pt base, shallower than classes.dtx's 2.5/2.2/1.87 em stack,
  which reads deep at this engine's narrower default measure; no external
  authority settles it. A document owns the choice through
  `\style{itemize}{ indent = ... }` (the declared override this default
  yields to). -/
  listIndent : Sp := pt 15
  leading : Nat := 1000
  /-- Whether paragraphs may hyphenate; the class default resolved. Layout
  owns the gate so every caller — build, tests, oracles — obeys it. -/
  hyphenate : Bool := true
  /-- Whether paragraphs justify. Off means ragged right: word spaces stay
  natural, an underfull line costs nothing, and only real overfull is bad. -/
  justify : Bool := true
  /-- Bleed past the trim edge, for the PDF writer: layout works in trim
  coordinates and never sees it. -/
  bleed : Sp := 0
  /-- The band a page footer reserves above the bottom margin: what its ink
  and clearance need beyond the half margin its baseline sits below the body
  area. Zero when there is no footer or the margin already holds it, so an
  undeclared page is unchanged. `Layout.run` computes it (`footBandFor`);
  everything else reads it only through `bodyBottom`. -/
  footBand : Sp := 0
  /-- The band a running head reserves below the top margin: what its ink
  and clearance need beyond the half margin it hangs below. Zero when
  there is no head or the margin already holds it, so an undeclared page
  is unchanged. `Layout.run` computes it (`headBandFor`); everything else
  reads it only through `bodyTop`. -/
  headBand : Sp := 0
  deriving Repr

def Geom.textWidth (g : Geom) : Sp := g.pageW - 2 * g.hmargin

/-- TeX's `\lineskip`: the least space between a line's depth and the next
line's height when the leading cannot hold them apart. Also the least
clearance between the body's ink and a footer's. The value is TeX's own
default (`\lineskip=1pt`, TeXbook p.78). -/
def lineskip : Sp := pt 1

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

/-- The band a footer of ink height `ascent` reserves: its baseline sits
`vmargin/2` below the body area, so whatever of `ascent + lineskip` the half
margin cannot hold comes out of the body. -/
def footBandFor (vmargin ascent : Sp) : Sp := max 0 (ascent + lineskip - vmargin / 2)

/-- The band a running head of ink `ascent + descent` reserves — the
footer's own reservation, fed the head's ink extent below its half-margin
line. The head's ink top sits `vmargin/2` above the body area (its
baseline `ascent` below that), so the whole line hangs toward the body
where the footer hangs only its ascent: whatever of
`ascent + descent + lineskip` the half margin cannot hold comes out of
the body. -/
def headBandFor (vmargin ascent descent : Sp) : Sp :=
  footBandFor vmargin (ascent + descent)

/-- The band arithmetic's one core inequality: a reservation of
`max 0 (x + l - m/2)` on top of the margin `m` always holds the ink extent
`x` plus the clearance `l` hanging from the half-margin line. Both band
sufficiency theorems are this statement — the footer's reflected through the
page height (`band_reserves_below`), the head's read directly — and it needs
no sign hypothesis on the margin, so neither do they:
`\page{ vmargin = -5mm }` parses and flows into `Geom.ofPage`, and the
reservation still suffices there. Bare `Int` binders because `omega` does
not see through the `Sp` abbreviation. -/
theorem band_reserves (m x l : Int) :
    m / 2 + x + l ≤ m + max 0 (x + l - m / 2) := by
  simp only [Int.max_def]
  split <;> omega

/-- `band_reserves` reflected through the page height: what
`bodyBottom_clears_footer` reads. The `generalize` names the band an opaque
atom shared by the goal and the keystone; the rest is linear. -/
private theorem band_reserves_below (pageH m x l : Int) :
    pageH - m - max 0 (x + l - m / 2) + x + l ≤ pageH - m / 2 := by
  have key := band_reserves m x l
  generalize max 0 (x + l - m / 2) = B at key ⊢
  omega

/-- `band_reserves` with the ink extent split into ascent and descent: what
`bodyTop_clears_head` reads. -/
private theorem band_reserves_above (m x y l : Int) :
    m / 2 + x + y + l ≤ m + max 0 (x + y + l - m / 2) := by
  have key := band_reserves m (x + y) l
  generalize max 0 (x + y + l - m / 2) = B at key ⊢
  omega

/-- The reservation is sufficient, for every geometry — negative margins
included (`band_reserves` needs no sign hypothesis): with the band from
`footBandFor`, body ink stops at least `lineskip` above the footer's ink top
(`footY - ascent`, the baseline at half the bottom margin less what the
footer reaches above it). -/
theorem bodyBottom_clears_footer (g : Geom) (ascent : Sp)
    (h : g.footBand = footBandFor g.vmargin ascent) :
    g.bodyBottom + ascent + lineskip ≤ g.pageH - g.vmargin / 2 := by
  simp only [Geom.bodyBottom, footBandFor] at h ⊢
  rw [h]
  exact band_reserves_below g.pageH g.vmargin ascent lineskip

/-- The mirror of `bodyBottom_clears_footer`, for every geometry: with the
band from `headBandFor`, body ink starts at least `lineskip` below the
head's ink bottom — `headY + descent`, the baseline at half the top margin
plus the head's ascent, plus what it hangs below. `band_reserves`, read
directly. -/
theorem bodyTop_clears_head (g : Geom) (ascent descent : Sp)
    (h : g.headBand = headBandFor g.vmargin ascent descent) :
    g.vmargin / 2 + ascent + descent + lineskip ≤ g.bodyTop := by
  simp only [Geom.bodyTop, headBandFor, footBandFor] at h ⊢
  rw [h]
  exact band_reserves_above g.vmargin ascent descent lineskip

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
    leading := spec.leading
    parskip := spec.parskip.getD base.parskip
    hyphenate := spec.hyphenate.getD base.hyphenate
    justify := spec.justify.getD base.justify
    bleed := spec.bleed }

/-- Baseline distance for a size: `Ir.leadingMilli` of it (6⁄5 — the ratio's
source, Bringhurst §2.2.1's routine settings, and its one spelling live
with the scale in Ir; the HTML stylesheet emits the same constant), scaled
by the page's `leading` factor (`\linespread`'s home). The factor is where
a document declares the extra lead a wide measure wants; the engine never
raises it silently. -/
def leadingFor (size : Sp) (factor : Nat := 1000) : Sp :=
  size * (Ir.leadingMilli : Int) / 1000 * factor / 1000

/-- The default vertical rhythm is one system, not three numbers: the peer
gap (`parskip`, 6pt at the 10pt base) is half the base leading, so the
heading's default space above — `2 × parskip` in the block walk — is exactly
one full rhythm unit, and every default gap is a multiple of the half-unit
(Bringhurst §2.2.2: add vertical space in measured intervals, multiples of
the basic leading). The positivity conjunct is what makes a heading's space
above strictly exceed its space below. -/
theorem default_rhythm_multiples :
    2 * ({} : Geom).parskip.width.sp = leadingFor Ir.baseFontSize ∧
    0 < ({} : Geom).parskip.width.sp := by decide

/-- Caption and float gaps sit on the same rhythm: the caption gap is the
half-unit (one `parskip`), the float gap the full unit (two, which is also
exactly LaTeX's `\intextsep` 12pt, classes.dtx 10pt option), and the
caption binds tighter to its object than the float to its page — the
ordering LaTeX's own `\abovecaptionskip` 10pt < `\intextsep` 12pt states
(classes.dtx). A default edit that breaks the quantization or the ordering
fails the build; this is the user-visible "spacing around tables and
figures" contract, stated over the values the engine ships. -/
theorem caption_gaps_rhythm :
    Ir.captionSepDefault.width.sp = ({} : Geom).parskip.width.sp ∧
    Ir.floatSepDefault.width.sp = 2 * ({} : Geom).parskip.width.sp ∧
    Ir.floatSepDefault.width.sp = leadingFor Ir.baseFontSize ∧
    Ir.captionSepDefault.width.sp < Ir.floatSepDefault.width.sp := by decide

/-- The slides stage carries a readable number of text lines. Tantau's rule
for presentations is lines, not points: "between 10 and 20 lines should fit
on each slide; the less lines, the more readable" (beamer user guide
§5.6.1). Both default stages at the default margins and the 11 pt base sit
inside that band — 15 full lines at 16:9, 16 at 4:3 — so the slides
defaults cannot drift apart without this failing the build. -/
theorem slides_lines_in_band :
    10 ≤ (Ir.slidesStage169.2 - 2 * Ir.slidesVMargin) / leadingFor Ir.slidesFontSize ∧
    (Ir.slidesStage169.2 - 2 * Ir.slidesVMargin) / leadingFor Ir.slidesFontSize ≤ 20 ∧
    10 ≤ (Ir.slidesStage43.2 - 2 * Ir.slidesVMargin) / leadingFor Ir.slidesFontSize ∧
    (Ir.slidesStage43.2 - 2 * Ir.slidesVMargin) / leadingFor Ir.slidesFontSize ≤ 20 := by
  decide

/-- The bands never eat the measure: any slides-default geometry whose head
and foot bands come from `headBandFor`/`footBandFor` keeps a positive body
height, and Tantau's 10–20 lines (beamer user guide §5.6.1, the band
`slides_lines_in_band` states for the bare stages) still holds between
`bodyTop` and `bodyBottom`. The ink hypotheses allow each running line two
em of the base size. That bound has no external authority to cite: the
OpenType spec bounds no line metric — OS/2 `sTypoAscender`: "It is not a
general requirement that sTypoAscender − sTypoDescender be equal to
unitsPerEm", and the hhea ascender/descender the engine reads are the
font's own — so two em is this engine's coverage choice, chosen generous
against real faces (typical line metrics sit at 1.0–1.3 em; the shipped
test faces are pinned under the bound in `Tests.lean`). -/
theorem slides_lines_survive_bands (a d f : Sp)
    (h0a : 0 ≤ a) (h0d : 0 ≤ d) (h0f : 0 ≤ f)
    (hh : a + d ≤ 2 * Ir.slidesFontSize) (hf : f ≤ 2 * Ir.slidesFontSize)
    (g : Geom)
    (hg : g.pageH = Ir.slidesStage169.2 ∨ g.pageH = Ir.slidesStage43.2)
    (hv : g.vmargin = Ir.slidesVMargin)
    (hhb : g.headBand = headBandFor g.vmargin a d)
    (hfb : g.footBand = footBandFor g.vmargin f) :
    0 < g.bodyBottom - g.bodyTop ∧
    10 ≤ (g.bodyBottom - g.bodyTop) / leadingFor Ir.slidesFontSize ∧
    (g.bodyBottom - g.bodyTop) / leadingFor Ir.slidesFontSize ≤ 20 := by
  have hvm : Ir.slidesVMargin = 1671942 := by decide
  have hfs : Ir.slidesFontSize = 720896 := by decide
  have hld : leadingFor Ir.slidesFontSize = 865075 := by decide
  have h169 : Ir.slidesStage169.2 = 16719420 := by decide
  have h43 : Ir.slidesStage43.2 = 17834048 := by decide
  have hls : lineskip = 65536 := by decide
  -- The key inequality over bare `Int` binders, as `bodyBottom_clears_footer`
  -- does it: `omega` does not see through the `Sp` abbreviation.
  have key : ∀ a d f hb fb H : Int,
      0 ≤ a → 0 ≤ d → 0 ≤ f →
      a + d ≤ 2 * 720896 → f ≤ 2 * 720896 →
      (H = 16719420 ∨ H = 17834048) →
      hb = max 0 (a + d + 65536 - 1671942 / 2) →
      fb = max 0 (f + 65536 - 1671942 / 2) →
      0 < H - 1671942 - fb - (1671942 + hb) ∧
      10 ≤ (H - 1671942 - fb - (1671942 + hb)) / 865075 ∧
      (H - 1671942 - fb - (1671942 + hb)) / 865075 ≤ 20 := by
    intro a d f hb fb H h0a h0d h0f hh hf hH hhb hfb
    simp only [Int.max_def] at hhb hfb
    rcases hH with h | h <;> subst h <;> split at hhb <;> split at hfb <;> omega
  rw [hfs] at hh hf
  rw [h169] at hg
  rw [h43] at hg
  simp only [headBandFor, footBandFor, hls, hv, hvm] at hhb hfb
  rw [hld]
  simp only [Geom.bodyBottom, Geom.bodyTop]
  rw [hv, hvm]
  exact key a d f g.headBand g.footBand g.pageH h0a h0d h0f hh hf hg hhb hfb

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

/-- The share of a page's leftover placed above the content. Content taller
than the area (leftover ≤ 0) takes nothing above: it stays top-flush and
spills below, never rides off the top of the page. -/
def VDist.aboveShare (d : VDist) (leftover : Sp) : Sp :=
  if leftover ≤ 0 then 0
  else leftover * d.above / (d.above + d.below)

/-- The split loses and invents nothing: the above share never leaves
`[0, leftover]`, and the below share is the exact difference — so both
shares are non-negative and sum to exactly the leftover, whatever the
ratio and whatever rounding the division did. -/
theorem VDist.split_exact (d : VDist) (l : Int) :
    0 ≤ d.aboveShare l ∧ (0 ≤ l → d.aboveShare l ≤ l) ∧
    d.aboveShare l + (l - d.aboveShare l) = l := by
  have hsum : (0 : Int) ≤ (d.above : Int) + (d.below : Int) := by
    have := Int.natCast_nonneg d.above
    have := Int.natCast_nonneg d.below
    omega
  have hcancel : ∀ x y : Int, x + (y - x) = y := by omega
  have hnn : 0 ≤ d.aboveShare l := by
    unfold aboveShare
    split
    · exact Int.le_refl 0
    · next hc =>
      have hc2 : ¬l ≤ (0 : Int) := hc
      have hl : (0 : Int) ≤ l := by omega
      exact Int.ediv_nonneg (Int.mul_nonneg hl (Int.natCast_nonneg _)) hsum
  refine ⟨hnn, ?_, hcancel _ _⟩
  intro hl
  unfold aboveShare
  split
  · exact hl
  · next hc =>
    by_cases hz : (d.above : Int) + (d.below : Int) = 0
    · rw [hz, Int.ediv_zero]
      exact hl
    · have hmul : l * (d.above : Int) ≤ l * ((d.above : Int) + (d.below : Int)) := by
        have hb := Int.natCast_nonneg d.below
        exact Int.mul_le_mul_of_nonneg_left (by omega) hl
      calc l * (d.above : Int) / ((d.above : Int) + (d.below : Int))
          ≤ l * ((d.above : Int) + (d.below : Int)) / ((d.above : Int) + (d.below : Int)) :=
            Int.ediv_le_ediv (by omega) hmul
        _ = l := Int.mul_ediv_cancel l hz

/-- Ratio 1:1 is the old vertical centring, division and guard included:
the generalisation moves no standout frame and no section page. -/
theorem VDist.center_is_halving (l : Sp) :
    VDist.center.aboveShare l = if l ≤ 0 then 0 else l / 2 := by
  unfold aboveShare center
  split
  · rfl
  · simp

/-- The shift of a line with `k` of its page's `n` fil units above it:
TeX's first-order infinite glue, as a share of the page's leftover.
`\vspace{\fill}` above and below the content is k=0 for nothing and k=1
of n=2 for every line — the centring sandwich; a leading fil alone pushes
everything down by the whole leftover (bottom-flush), a trailing fil
alone moves nothing. Content taller than the area (leftover ≤ 0) stays
put, exactly as `VDist.aboveShare` guards. -/
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

/-- "All leftover below" is the old top-flush behaviour: the article page
and every other undeclared page keep their lines exactly where they were. -/
theorem VDist.top_is_flush (l : Sp) : VDist.top.aboveShare l = 0 := by
  unfold aboveShare top
  split
  · rfl
  · simp

/-- The distribution a frame's declaration names. `golden` is the moloch
title page's 2618:1000. -/
def VDist.of : Ir.VAlign → VDist
  | .top => .top
  | .center => .center
  | .bottom => .bottom
  | .golden => .golden

inductive Item where
  | box (w : Sp) (fontIdx : Nat) (color : Ir.Color) (link : Option String)
      (glyphs : Array (Nat × Char × Sp)) (size : Sp) (underline : Bool) (raise : Sp)
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

structure PageOut where
  lines : Array LineOut := #[]
  fills : Array Fill := #[]
  /-- The chrome footer this page carries, resolved at collection time (the
  frame's own number, the section in force): the band of slots the final
  pass lays into the margin once the page count is known. `none` on section
  pages, standout frames, and every page of an unthemed document. -/
  foot : Option (Array Ir.BandSlot) := none
  deriving Repr, Inhabited

structure Out where
  pages : Array PageOut
  diags : Array Diag

-- Flattening: inlines → word/space/break tokens ------------------------------

/-- A resolved text style: which family slot, and the bold/italic bits. -/
structure TextStyle where
  slot : Nat := 0
  bold : Bool := false
  italic : Bool := false
  color : Ir.Color := Ir.Color.black
  /-- Destination of the enclosing `\href`, if any. -/
  link : Option String := none
  /-- Size relative to the surrounding text, per mille. Absolute rather than
  compounding, as in LaTeX: `\large\Large` is Large, not the product. -/
  scale : Nat := 1000
  /-- Set as small caps. Applies to the word, not the face: see
  `smallCapRuns`. -/
  smallcaps : Bool := false
  /-- Under a drawn underline; the run carries it into the set line. -/
  underline : Bool := false
  deriving Repr, BEq, Inhabited

private inductive Tk where
  | word (style : TextStyle) (chars : Array Char)
  | space (style : TextStyle)
  | fill
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
  deriving Repr

private structure FlattenSt where
  toks : Array Tk := #[]
  warnedMath : Bool := false
  diags : Array Diag := #[]

private def warn (st : FlattenSt) (code : DiagCode) (msg : String)
    (help : Option String := none) : FlattenSt :=
  { st with diags := st.diags.push (Diag.of code msg (help := help)) }

/-- Small caps, relative to the surrounding size. Synthesised: the faces we can
count on ship no small-caps variant and the sfnt reader does not apply `smcp`,
so lowercase becomes uppercase set smaller. Real small caps are drawn, not
scaled, so this is a stand-in until a face's own feature can be used. -/
def smallCapScale : Nat := 800

/-- Split a small-caps word so each run carries its own size: capitals stay,
lowercase is raised and set at `smallCapScale`. The runs are separate words
with no glue between them, so they set as one unbreakable unit -- which also
means a small-caps word is not hyphenated. -/
private def smallCapRuns (sty : TextStyle) (cur : Array Char) : Array Tk := Id.run do
  let mut out : Array Tk := #[]
  let mut run : Array Char := #[]
  let mut lower := false
  for c in cur do
    let isLower := c.isLower
    if !run.isEmpty && isLower != lower then
      let s := if lower then { sty with scale := sty.scale * smallCapScale / 1000 } else sty
      out := out.push (.word s run)
      run := #[]
    lower := isLower
    run := run.push (if isLower then c.toUpper else c)
  unless run.isEmpty do
    let s := if lower then { sty with scale := sty.scale * smallCapScale / 1000 } else sty
    out := out.push (.word s run)
  return out

private def pushWord (st : FlattenSt) (sty : TextStyle) (cur : Array Char) : FlattenSt :=
  if sty.smallcaps then
    { st with toks := st.toks ++ smallCapRuns sty cur }
  else
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
private def applyStyle (sty : TextStyle) : Ir.Style → TextStyle
  | .bold => { sty with bold := true }
  | .italic => { sty with italic := true }
  | .emph => { sty with italic := !sty.italic }
  | .mono => { sty with slot := 2 }
  | .sans => { sty with slot := 1 }
  | .smallcaps => { sty with smallcaps := true }
  | .normal => {}
  | .size n => match Ir.sizeScale.lookup n with
    | some k => { sty with scale := k }
    | none => sty

mutual

private def flatten (mathOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (xs : Array Inline) : FlattenSt :=
  flattenList mathOk st sty xs.toList

private def flattenList (mathOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (xs : List Inline) : FlattenSt :=
  match xs with
  | [] => st
  | x :: rest => flattenList mathOk (flattenOne mathOk st sty x) sty rest

private def flattenOne (mathOk : Bool) (st : FlattenSt) (sty : TextStyle)
    (x : Inline) : FlattenSt :=
  match x with
  | .text s => pushText st sty s
  | .icon c _ => { st with toks := st.toks.push (.icon sty c) }
  | .image src spec _ => { st with toks := st.toks.push (.img src spec) }
  | .linebreak extra => { st with toks := st.toks.push (.brk extra) }
  | .fill => { st with toks := st.toks.push .fill }
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
  | .styled s body => flatten mathOk st (applyStyle sty s) body
  | .colored c _ body => flatten mathOk st { sty with color := c } body
  -- A role is a name, pure grouping: zero metric impact, no style change
  -- (role_transparent_layout is the statement).
  | .role _ body => flatten mathOk st sty body
  -- The underline is the link's affordance in both backends (the HTML
  -- anchor keeps the browser's): never colour alone, and never nothing
  -- (WCAG 2.2 SC 1.4.1, use of colour).
  | .link url body => flatten mathOk st { sty with link := some url, underline := true } body
  | .underline body => flatten mathOk st { sty with underline := true } body
  -- A step is pure grouping here: the PDF path dims pending content by
  -- recolouring copies before layout (`run`'s step driver), never by metrics.
  | .step _ _ body => flatten mathOk st sty body
  -- Placeholders are substituted before layout; reaching here means the
  -- document used one outside running content.
  | .pageNumber => pushText st sty "?"
  | .pageCount => pushText st sty "?"

end

-- Items -----------------------------------------------------------------------

private def scaledAt (size : Sp) (font : Font) (units : Nat) : Sp :=
  (units * size.toNat) / font.unitsPerEm

private def glyphOf (size : Sp) (font : Font) (c : Char) : Option (Nat × Char × Sp) :=
  match font.gid c with
  | some g => some (g, c, scaledAt size font (font.widths[g]?.getD 0))
  | none => none

def hyphenGlyph (size : Sp) (font : Font) : Array (Nat × Char × Sp) :=
  match glyphOf size font '-' with
  | some g => #[g]
  | none => #[]

/-- Fixed-width spaces, as a fraction of the em. These are kerns, not
characters: a Type 1-derived face has no glyph at U+2009, so looking one up
drops the space that `\,` asked for. `\!`-style negative kerns are not here
because there is no Unicode character for them. -/
def fixedSpace (c : Char) : Option (Nat × Nat) :=
  if c == '\u2009' then some (1, 6)        -- thin space, TeX's \,
  else if c == '\u2005' then some (1, 4)   -- four-per-em, \:
  else if c == '\u2004' then some (1, 3)   -- three-per-em, \;
  else if c == '\u2007' then some (1, 2)   -- figure space
  else none

/-- One word → items: boxes split by hyphenation points (flagged penalties
carrying the hyphen glyph) and by explicit hyphens (unflagged, no glyph).
A scalar the styled face lacks is set from the precomputed fallback face
(`FontSet.fallback`) at the same size — its own one-glyph box, since a box
carries one face — or dropped when no face covers it. `missing` and `substs`
carry `(styled font, scalar)` so the diagnostic can name the family. -/
private def wordItems (pats : Option Hyphen.Patterns) (size : Sp) (fontIdx : Nat)
    (color : Ir.Color) (link : Option String) (underline : Bool)
    (fs : FontSet) (font : Font) (chars : Array Char) (missing : Array (Nat × Char))
    (substs : Array (Nat × Char × Nat)) (cache : Std.HashMap String (List Nat)) :
    Array Item × Array (Nat × Char) × Array (Nat × Char × Nat) ×
      Std.HashMap String (List Nat) := Id.run do
  let mut missing := missing
  let mut substs := substs
  let mut cache := cache
  let hyphW := (hyphenGlyph size font).foldl (fun w (_, _, adv) => w + adv) 0
  let mut items : Array Item := #[]
  let mut box : Array (Nat × Char × Sp) := #[]
  let mut boxW : Sp := 0
  let flush (items : Array Item) (box : Array (Nat × Char × Sp)) (w : Sp) : Array Item :=
    if box.isEmpty then items else items.push (.box w fontIdx color link box size underline 0)
  let mut i := 0
  for _ in [0:chars.size + 1] do
    if h : i < chars.size then
      let c := chars[i]
      if c.isAlpha then
        let mut j := i
        let mut run : Array Char := #[]
        for _ in [i:chars.size] do
          if h' : j < chars.size then
            if chars[j].isAlpha then
              run := run.push chars[j]
              j := j + 1
            else
              break
          else
            break
        let word := String.ofList run.toList
        let mut breaks : List Nat := []
        match pats with
        | some p =>
          match cache[word]? with
          | some b => breaks := b
          | none =>
            let b := Hyphen.hyphenate p word
            cache := cache.insert word b
            breaks := b
        | none => pure ()
        for (c', k) in run.zipIdx do
          if breaks.contains k then
            items := flush items box boxW
            box := #[]
            boxW := 0
            items := items.push
              (.pen hyphW hyphenPenalty true fontIdx color (hyphenGlyph size font))
          match glyphOf size font c' with
          | some g =>
            box := box.push g
            boxW := boxW + g.2.2
          | none =>
            match fs.fallbackFor c' |>.bind fun fb =>
                (glyphOf size (fs.get fb) c').map (fb, ·) with
            | some (fb, g) =>
              items := flush items box boxW
              box := #[]
              boxW := 0
              items := items.push (.box g.2.2 fb color link #[g] size underline 0)
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
          items := items.push (.box (size * num / den) fontIdx color link #[] size underline 0)
          i := i + 1
        | none =>
        if c == '\u00a0' then
          -- A no-break space is an interword space that is not glue.
          items := flush items box boxW
          box := #[]
          boxW := 0
          items := items.push
            (.box (scaledAt size font (font.advance ' ')) fontIdx color link #[] size underline 0)
          i := i + 1
        else
        match glyphOf size font c with
        | some g =>
          box := box.push g
          boxW := boxW + g.2.2
        | none =>
          match fs.fallbackFor c |>.bind fun fb =>
              (glyphOf size (fs.get fb) c).map (fb, ·) with
          | some (fb, g) =>
            items := flush items box boxW
            box := #[]
            boxW := 0
            items := items.push (.box g.2.2 fb color link #[g] size underline 0)
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
shrinking by a third — the proportions of TeX's default space factor
(TeXbook Ch. 12: interword glue is the font's space with stretch and
shrink from its fontdimens, w/2 and w/3 in the plain fonts). -/
private def interword (size : Sp) (font : Font) : Glue :=
  let w := scaledAt size font (font.advance ' ')
  { width := w, stretch := w / 2, shrink := w / 3 }

/-- Ragged setting as an item transform, leaving the breaker untouched:
every glue keeps its natural width and gains fil, so an underfull line is
free and shrink is never spent — `\raggedright`'s glue model. The lines are
then set unjustified, so the fil never stretches a rendered space. -/
def raggedItems (items : Array Item) : Array Item :=
  items.map fun it =>
    match it with
    | .glue g => .glue { width := g.width, fil := true, parfill := g.parfill }
    | .box .. | .pen .. | .img .. | .rule .. => it

-- The document's scalars, for the driver's per-glyph fallback ------------------

mutual

/-- The scalars a run's formulas ask the math face for — the Mathematical
Alphanumeric code points elaboration mapped variables to live nowhere in
the plain text, so the census must walk the formula bodies themselves. -/
private def mathScalarTextList (acc : Array Char) : List Ir.Inline → Array Char
  | [] => acc
  | x :: rest => mathScalarTextList (mathScalarTextOne acc x) rest

private def mathScalarTextOne (acc : Array Char) : Ir.Inline → Array Char
  | .formula _ _ body => Math.MList.scalarsList acc body
  | .styled _ body => mathScalarTextList acc body.toList
  | .colored _ _ body => mathScalarTextList acc body.toList
  | .role _ body => mathScalarTextList acc body.toList
  | .link _ body => mathScalarTextList acc body.toList
  | .underline body => mathScalarTextList acc body.toList
  | .step _ _ body => mathScalarTextList acc body.toList
  | .text _ => acc
  | .math _ _ => acc
  | .image _ _ _ => acc
  | .icon _ _ => acc
  | .linebreak _ => acc
  | .fill => acc
  | .pageNumber => acc
  | .pageCount => acc

end

/-- The census accumulator: the plain texts a document's faces will be
asked for, and — separately — the scalars its formulas ask the math face
for, so the driver can both cover them (one fallback precompute) and know
whether the document reaches math at all. -/
private structure ScalarAcc where
  texts : Array String := #[]
  math : Array Char := #[]

mutual

/-- Icon scalars, gathered like math scalars: an icon's plain text is its
text alternative, so its glyph would never enter the census through
`plainText` — this walk is what routes it into the same per-scalar
fallback precompute every other scalar uses. -/
private def iconScalarTextList (acc : Array Char) : List Ir.Inline → Array Char
  | [] => acc
  | x :: rest => iconScalarTextList (iconScalarTextOne acc x) rest

private def iconScalarTextOne (acc : Array Char) : Ir.Inline → Array Char
  | .icon c _ => acc.push c
  | .styled _ body => iconScalarTextList acc body.toList
  | .colored _ _ body => iconScalarTextList acc body.toList
  | .role _ body => iconScalarTextList acc body.toList
  | .link _ body => iconScalarTextList acc body.toList
  | .underline body => iconScalarTextList acc body.toList
  | .step _ _ body => iconScalarTextList acc body.toList
  | .text _ => acc
  | .math _ _ => acc
  | .formula _ _ _ => acc
  | .image _ _ _ => acc
  | .linebreak _ => acc
  | .fill => acc
  | .pageNumber => acc
  | .pageCount => acc

end

/-- The plain text of a run and, when it carries formulas or icons, their
scalars: what keeps the per-scalar fallback one mechanism — a math or icon
scalar enters the same precompute a text scalar does. -/
private def textAndMath (out : ScalarAcc) (xs : Array Ir.Inline) : ScalarAcc :=
  { texts := (out.texts.push (Ir.plainText xs)).push
      (String.ofList (iconScalarTextList #[] xs.toList).toList)
    math := mathScalarTextList out.math xs.toList }

mutual

private def scalarTextList (out : ScalarAcc) (itemD enumD : Nat) :
    List Block → ScalarAcc
  | [] => out
  | b :: rest => scalarTextList (scalarTextOne out itemD enumD b) itemD enumD rest

private def scalarTextOne (out : ScalarAcc) (itemD enumD : Nat) :
    Block → ScalarAcc
  | .para xs => textAndMath out xs
  | .section _ _ title => textAndMath out title
  | .list ordered items =>
    -- The level's default marker rides along, so the fallback face is
    -- found before layout asks for the glyph. Per-kind depth, as LaTeX
    -- counts it (`\@itemdepth`/`\@enumdepth`).
    let (itemD, enumD) := if ordered then (itemD, enumD + 1) else (itemD + 1, enumD)
    let level := min (if ordered then enumD else itemD) 4
    scalarTextItems { out with texts := out.texts.push (ListMark.scalars ordered level) } itemD enumD items.toList
  | .center body => scalarTextList out itemD enumD body.toList
  | .quote body => scalarTextList out itemD enumD body.toList
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
  | .verbatim _ s => { out with texts := out.texts.push s }
  -- A rule has no glyphs.
  | .rule _ _ _ => out
  -- A page boundary ships no ink.
  | .pagebreak => out
  -- A picture's labels are set as glyph runs: their scalars are asked of
  -- the body face like any other text.
  | .picture pic => { out with texts := out.texts ++ pic.labelTexts }
  | .frame title _ _ body =>
    scalarTextList (textAndMath out title) itemD enumD body.toList
  -- A framefoot note is set on the page as footer text.
  | .framefoot content => textAndMath out content
  -- Every cell's text, and a caption's, reaches the scalar census: the
  -- fallback scan must see a glyph before layout asks a face for it.
  | .table _ _ _ rows _ => scalarTextTableRows out rows.toList
  | .float _ _ body caption =>
    scalarTextList (textAndMath out caption) itemD enumD body.toList

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
  let mut acc : ScalarAcc := scalarTextList {} 0 0 doc.body.toList
  if let some h := doc.head then
    acc := textAndMath acc h |> fun a => { a with texts := a.texts.push "0123456789" }
  if let some f := doc.foot then
    acc := textAndMath acc f |> fun a => { a with texts := a.texts.push "0123456789" }
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
  .box w e.idx e.color e.link #[] size e.underline 0

/-- Width of assembled math items: boxes only ever enter the stream, so the
advance of a math box is the sum of what it contains plus the kerns the
spacing table put between them — `mathBoxChecks` holds the two ways of
computing it equal in sp. -/
def mathItemsWidth (items : Array Item) : Sp :=
  items.foldl (fun w it => match it with
    | .box bw _ _ _ _ _ _ _ => w + bw
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
    | .box _ _ _ _ glyphs size _ raise =>
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
    | .box w i c l g s u r => .box w i c l g s u (r + delta)
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
  #[.box 0 e.idx e.color e.link #[] 1 false (max 0 top),
    .box 0 e.idx e.color e.link #[] 1 false (min 0 bot)]

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
      (items.push (Item.box w e.idx e.color e.link #[(gv, c, w)] size e.underline dRaise),
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
  -- own name: the page-level `lineskip` is a different, absolute quantity,
  -- and one name for two values is how a future reader fuses them.
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
        (.box surdW e.idx e.color e.link #[(gv, '\u221A', surdW)] size e.underline surdRaise)
      |>.push (Item.rule bodyW θ (raise + ruleBot) e.color)
      |>.push (mathKern e size (-bodyW)))
      ++ raisedBody
      ++ struts e (raise + ruleTop + extraAsc) (min (raise + bBot) (surdRaise + vBot))
    (items, missing0)

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
          (#[(Item.box w e.idx e.color e.link #[(gv, c, w)] size e.underline vRaise)]
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
      ((acc.1.push (.box g.2.2 e.idx e.color e.link #[g] size e.underline raise)), acc.2)
    | none =>
      -- A scalar the math face lacks goes through the per-scalar chain the
      -- driver precomputed for text (`FontSet.fallback`) — one mechanism,
      -- at the math size, its own box since a box carries one face.
      match e.fs.fallbackFor c |>.bind fun fb =>
          (glyphOf size (e.fs.get fb) c).map (fb, ·) with
      | some (fb, g) =>
        ((acc.1.push (.box g.2.2 fb e.color e.link #[g] size e.underline raise)), acc.2)
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
          items := items.push (.box w cur e.color e.link glyphs size e.underline raise)
          glyphs := #[]
          w := 0
        cur := fi
        glyphs := glyphs.push g
        w := w + g.2.2
      | none =>
        unless missing.contains (e.idx, c) do
          missing := missing.push (e.idx, c)
    return (items.push (.box w cur e.color e.link glyphs size e.underline raise), missing)
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

/-- Flatten inlines into Knuth-Plass items. The fourth component maps the
index of a forced-break penalty to extra vertical space the document asked for
there (`\\[1ex]`); it rides beside the items because the line breaker has no
use for it, and putting it in `Item` would make every pattern carry a field
only the page builder reads. -/
private def itemsOfInlines (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (baseStyle : TextStyle) (xs : Array Inline)
    (cache : Std.HashMap String (List Nat)) (imgs : Image.Store := {})
    (textW : Sp := 0) (textH : Sp := 0) :
    Array Item × Array Diag × Std.HashMap String (List Nat) ×
      Std.HashMap Nat Sp := Id.run do
  let st := flatten (fs.mathFont?.isSome) {} baseStyle xs
  let mut items : Array Item := #[]
  let mut missing : Array (Nat × Char) := #[]
  let mut substs : Array (Nat × Char × Nat) := #[]
  let mut extras : Std.HashMap Nat Sp := {}
  let mut cache := cache
  for tk in st.toks do
    match tk with
    | .word sty chars =>
      let idx := fs.lookup sty.slot sty.bold sty.italic
      let sz := size * sty.scale / 1000
      let (ws, m, s, c') :=
        wordItems pats sz idx sty.color sty.link sty.underline fs (fs.get idx) chars
          missing substs cache
      missing := m
      substs := s
      cache := c'
      items := items ++ ws
    | .icon sty c =>
      -- The styled face first (an icon font declared as the body face is
      -- legal), then the fallback chain; either hit is the icon's own face
      -- by design. Only total absence is a loss (E0405, below).
      let idx := fs.lookup sty.slot sty.bold sty.italic
      let sz := size * sty.scale / 1000
      let hit :=
        match glyphOf sz (fs.get idx) c with
        | some g => some (idx, g)
        | none =>
          fs.fallbackFor c |>.bind fun fb =>
            (glyphOf sz (fs.get fb) c).map (fb, ·)
      match hit with
      | some (fb, g) =>
        items := items.push (.box g.2.2 fb sty.color sty.link #[g] sz sty.underline 0)
      | none =>
        unless missing.contains (idx, c) do
          missing := missing.push (idx, c)
    | .formula display sty body =>
      -- The flatten pass pushes a formula token only when a math face with
      -- constants is present.
      match fs.mathFont? with
      | some (idx, font, consts) =>
        -- The math face sets at the size that makes its x-height the
        -- surrounding face's — fontspec's `Scale=MatchLowercase`, the rule
        -- `Math.mathSize` states and its agreement theorems bound to the sp.
        let around := fs.get (fs.lookup sty.slot sty.bold sty.italic)
        let runSize := size * sty.scale / 1000
        let e : MathEnv := {
          idx, font, consts, fs
          color := sty.color
          link := sty.link
          underline := sty.underline
          base := (Math.mathSize runSize.toNat around.xHeightOptical
            around.unitsPerEm font.xHeightOptical font.unitsPerEm : Nat) }
        let (ms, m) := mathItems e display body missing
        -- The substitutions the chain made, named like text's (W0009):
        -- a scalar the math face lacks that a fallback face set. One the
        -- assembly paths recorded missing was never substituted — a grown
        -- construction is one face — so `m` excludes it here.
        for c in Math.MList.scalarsList #[] body do
          if (font.gid c).isNone && !m.contains (idx, c) then
            if let some fb := fs.fallbackFor c then
              if ((fs.get fb).gid c).isSome && !substs.contains (idx, c, fb) then
                substs := substs.push (idx, c, fb)
        missing := m
        items := items ++ ms
      | none => pure ()
    | .space sty =>
      let idx := fs.lookup sty.slot sty.bold sty.italic
      items := items.push (.glue (interword (size * sty.scale / 1000) (fs.get idx)))
    | .fill =>
      -- Stretchable but not a legal breakpoint on its own.
      items := items.push (.glue { fil := true })
    | .img src spec =>
      -- The request resolves against the store the driver filled. An entry
      -- that did not load (the driver has said why) keeps the requested
      -- size around a default 1 in square, so the document still compiles
      -- and the placeholder shows where the figure would stand.
      let idx? := imgs.find? src
      let (iW, iH) := match idx?.bind fun k => (imgs.get? k).bind (·.info) with
        | some inf => (inf.width, inf.height)
        | none => (Dim.inch 1, Dim.inch 1)
      let (w, h) := Image.resolveSize spec iW iH textW textH
      items := items.push (.img idx? (max 0 w) (max 0 h))
    | .brk extra =>
      items := items.push (.glue { fil := true, parfill := true })
      let sp := extra.width.resolve size xHeight
      if sp != 0 then
        extras := extras.insert items.size sp
      items := items.push (.pen 0 forcedCost false 0 Ir.Color.black #[])
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
  for (idx, c) in missing do
    diags := diags.push (Diag.of .E0405
      s!"'{(fs.get idx).family}' has no glyph for '{c}' (U+{hex c.toNat}); dropped"
      (help := "declare a face that covers it in \\fonts, or accept the loss \
with \\allow{E0405}"))
  for (idx, c, fb) in substs do
    diags := diags.push (Diag.of .W0009
      s!"'{(fs.get idx).family}' has no glyph for '{c}' \
        (U+{hex c.toNat}); set from '{(fs.get fb).family}'")
  return (items, diags, cache, extras)
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
    | some (.box _ _ _ _ _ _ _ _) => j > 0
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

def lineStart (items : Array Item) (start : Nat) : Nat := Id.run do
  let mut a := start
  for _ in [a:items.size] do
    match items[a]? with
    | some (.glue _) => a := a + 1
    | some (.pen _ cost _ _ _ _) => if cost ≥ 10000 then break else a := a + 1
    | _ => break
  return a

def measure (items : Array Item) (a j : Nat) : Measure := Id.run do
  let mut m : Measure := {}
  for k in [a:j] do
    match items[k]! with
    | .box w _ _ _ _ _ _ _ => m := { m with natural := m.natural + w }
    | .img _ w _ => m := { m with natural := m.natural + w }
    | .rule w _ _ _ => m := { m with natural := m.natural + w }
    | .glue g => m := { m with
        natural := m.natural + g.width
        stretch := m.stretch + g.stretch
        shrink := m.shrink + g.shrink
        fil := m.fil || g.fil }
    | .pen _ _ _ _ _ _ => pure ()
  if let some (.pen w _ _ _ _ _) := items[j]? then
    m := { m with natural := m.natural + w }
  return m

def overfullDemerits : Int := 100000000

/-- Demerits of one candidate line. -/
def lineDemerits (items : Array Item) (m : Measure) (target : Sp) (j : Nat) : Int :=
  let delta := target - m.natural
  let b : Int :=
    if delta == 0 then 0
    else if delta > 0 then
      if m.fil then 0 else badness delta m.stretch
    else
      if m.shrink < -delta then -1  -- overfull marker
      else badness delta m.shrink
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

/-- Prefix sums over item width/stretch/shrink/fil/forced counts, one slot
past the end, so `kp` measures any line by differencing. -/
structure KpSums where
  w : Array Sp
  s : Array Sp
  k : Array Sp
  f : Array Nat
  forced : Array Nat

def kpSums (items : Array Item) : KpSums := Id.run do
  let n := items.size
  let mut pw : Array Sp := Array.mkEmpty (n + 1)
  let mut ps : Array Sp := Array.mkEmpty (n + 1)
  let mut pk : Array Sp := Array.mkEmpty (n + 1)
  let mut pf : Array Nat := Array.mkEmpty (n + 1)
  let mut pforced : Array Nat := Array.mkEmpty (n + 1)
  pw := pw.push 0
  ps := ps.push 0
  pk := pk.push 0
  pf := pf.push 0
  pforced := pforced.push 0
  for k in [0:n] do
    let (dw, dst, dsh, dfil) : Sp × Sp × Sp × Nat := match items[k]! with
      | .box w _ _ _ _ _ _ _ => (w, 0, 0, 0)
      | .img _ w _ => (w, 0, 0, 0)
      | .rule w _ _ _ => (w, 0, 0, 0)
      | .glue g => (g.width, g.stretch, g.shrink, if g.fil then 1 else 0)
      | .pen _ _ _ _ _ _ => (0, 0, 0, 0)
    pw := pw.push (pw[k]! + dw)
    ps := ps.push (ps[k]! + dst)
    pk := pk.push (pk[k]! + dsh)
    pf := pf.push (pf[k]! + dfil)
    pforced := pforced.push (pforced[k]! + (if isForced items k then 1 else 0))
  return { w := pw, s := ps, k := pk, f := pf, forced := pforced }

/-- The line measure `kp` uses: prefix-sum differences over [a:j) plus the
width of the penalty broken at. Must agree with `measure` wherever `kp`
evaluates it; `scripts/kp-fuzz.lean` holds it to that. -/
def kpMeasure (items : Array Item) (sums : KpSums) (a j : Nat) : Measure :=
  let penW : Sp := match items[j]? with
    | some (.pen w _ _ _ _ _) => w
    | _ => 0
  { natural := sums.w[j]! - sums.w[a]! + penW
    stretch := sums.s[j]! - sums.s[a]!
    shrink := sums.k[j]! - sums.k[a]!
    fil := sums.f[j]! - sums.f[a]! > 0 }

/-- Optimal breakpoints by dynamic programming over break positions, with
prefix-sum line measures and an active list: a node whose line to the
current position is already overfull beyond shrink can only get worse, so
it is considered one last time and then deactivated (one node is always
retained so a solution exists even for unbreakable content). -/
def kp (items : Array Item) (target : Sp) : Array Nat := Id.run do
  let n := items.size
  let sums := kpSums items
  let measureAt (a j : Nat) : Measure := kpMeasure items sums a j
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
              let d := d0 + lineDemerits items m target j + dbl
              match bestHere with
              | some (dBest, _) =>
                if d < dBest then bestHere := some (d, p)
              | none => bestHere := some (d, p)
              -- Once overfull beyond shrink, this predecessor only gets
              -- worse. Keep the best one per flagged state because that is
              -- the only predecessor property future line costs observe.
              if m.natural - m.shrink > target then
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

-- Line setting ----------------------------------------------------------------

private def setLine (items : Array Item) (a j : Nat) (target : Sp)
    (justify : Bool) : Array Seg × Sp × Bool := Id.run do
  let m := measure items a j
  let delta := target - m.natural
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
    | .box w fontIdx color link glyphs size underline raise =>
      -- The declared width is authoritative, as it already is in `measure`: a
      -- kern is a box with a width and no glyphs, and recomputing from the
      -- advances would silently set it to zero.
      segs := segs.push
        (.run fontIdx color link w (glyphs.map fun (g, c, _) => (g, c)) size underline raise)
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
      -- size (and under the underline) of the run it interrupts.
      let (inherited, inheritedUl) := segs.foldl (fun acc s => match s with
        | .run _ _ _ _ _ sz ul _ => (if sz != 0 then sz else acc.1, ul)
        | _ => acc) ((0 : Sp), false)
      segs := segs.push
        (.run fontIdx color none w (glyphs.map fun (g, c, _) => (g, c)) inherited inheritedUl 0)
      width := width + w
  -- drop trailing gaps (paragraph-final fill)
  let mut segs' := segs
  repeat
    match segs'.back? with
    | some (.gap w) =>
      segs' := segs'.pop
      width := width - w
    | _ => break
  return (segs', width, overfull)

-- Page assembly ----------------------------------------------------------------

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
  /-- Depth of the last line placed. -/
  prevDepth : Sp := 0
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
  /-- The last thing placed was a table rule: the next line stacks flush
  under it — its height plus pending skips, no leading, no lineskip — as
  TeX marks `\prevdepth` ignored after an `\hrule` so the box after a rule
  takes exactly the explicit glue. booktabs' rule padding depends on it. -/
  noInterline : Bool := false
  /-- A `tie` op stands between the last placed line and the next one: a
  float's caption and its object. Consumed by the next placement; a page
  break landing on it is reported (W0339), never silent. -/
  tie : Bool := false
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
  /-- Lines and fills already on the page when `.pin` arrived: page-top
  chrome (the frame title and its bar) the distribution never moves. -/
  pinnedLines : Nat := 0
  pinnedFills : Nat := 0
  diags : Array Diag := #[]

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
      b.geom.bodyBottom - (lastY + b.prevDepth)
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
  { b with pages := b.pages.push { lines := lines, fills := fills, foot := b.curFoot },
           cur := {},
           shrinkAbove := #[], pageShrink := 0, needed := 0, skip := {},
           pageBg := none, vdist := .top, pageFils := 0, filsAbove := #[],
           pinnedLines := 0, pinnedFills := 0,
           diags := diags }

/-- A line that shares its baseline with the last one (underline rules)
rides with it, including its share of the page's shrink and of its fil
glue. -/
private def B.pushSibling (b : B) (l : LineOut) : B :=
  { b with cur := { b.cur with lines := b.cur.lines.push l },
           shrinkAbove := b.shrinkAbove.push (b.shrinkAbove.back?.getD 0)
           filsAbove := b.filsAbove.push (b.filsAbove.back?.getD 0) }

private def B.commit (b : B) (line : LineOut) (depth above overflow : Sp) : B :=
  -- The consumed skip's fil counts here, page top included: an author's
  -- \vspace*{\fill} above the first line is what the star means (the
  -- space survives the break), and fil width is zero, so counting it
  -- costs nothing when unused.
  let fils := b.pageFils + (if b.skip.fil then 1 else 0)
  { b with cur := { b.cur with lines := b.cur.lines.push line }
           shrinkAbove := b.shrinkAbove.push above
           pageFils := fils
           filsAbove := b.filsAbove.push fils
           pageShrink := above
           needed := max b.needed overflow
           y := line.y
           freshStart := false
           noInterline := false
           tie := false
           prevDepth := depth
           skip := {} }

/-- The tie's report: the seam the break landed on, named. The float is
still best-effort — the caption opens the next page — and the pending code
says the keep-together is owed. -/
private def B.brokeTie (b : B) : B :=
  if b.tie then
    { b with diags := b.diags.push (Diag.of .W0339
        "a page break separates a caption from the table or figure it belongs to"
        (help := "\\pagebreak before the float moves it whole to the next page")) }
  else b

/-- Place one line. Its height and depth follow the tallest run on it, not
the paragraph's nominal size: a line carrying `\Huge` needs room above its
baseline and below it, or it collides with its neighbours.

The baseline distance is TeX's: the leading of the line being placed, unless
the previous line's depth plus this line's height plus `lineskip` is more.
So a Huge title is followed at the body's leading plus what the title hangs
below its baseline, not at the Huge leading — the next line's size decides,
as it does in TeX where `\baselineskip` is read when a line is appended.

A page fills at natural glue until a line will not fit even with every skip
above it fully shrunk; then the page closes (shrunk to fit if it overflowed)
and the line opens the next, its pending glue discarded as TeX discards glue
at the top of a page. Glue is never stretched: the bottom is ragged. -/
private def B.placeLine (fs : FontSet) (b : B) (x : Sp) (size : Sp) (segs : Array Seg)
    (w : Sp) : B :=
  let nominal := if size == 0 then b.geom.fontSize else size
  -- Each run measured in its own face: a sans title is as tall as the sans
  -- says, not as the body face would be at that size.
  let (tallest, height, depth) := segs.foldl (fun (acc : Sp × Sp × Sp) s => match s with
    | .run idx _ _ _ _ sz _ raise =>
      let font := fs.get idx
      let sz := if sz == 0 then nominal else sz
      (max acc.1 sz,
       max acc.2.1 (scaledAt sz font font.capHeight.toNat + max 0 raise),
       max acc.2.2 (scaledAt sz font (-font.descent).toNat + max 0 (-raise)))
    -- An image stands `h` above the baseline with no depth: it raises the
    -- line's height, never its nominal size, so the leading after it is
    -- decided by the text that follows, as TeX decides it.
    | .image _ _ h => (acc.1, max acc.2.1 h, acc.2.2)
    -- A math rule (a fraction bar) reaches from `raise` to
    -- `raise + thickness`: it can add height above the baseline or depth
    -- below it, never both.
    | .rule _ t r _ => (acc.1, max acc.2.1 (r + t), max acc.2.2 (-r))
    | _ => acc) (nominal, b.capHeight * nominal / b.geom.fontSize,
                 b.descent * nominal / b.geom.fontSize)
  let bottom := b.geom.bodyBottom
  let mk (y : Sp) : LineOut := { x := x, y := y, size := size, segs := segs, setWidth := w }
  let firstY := b.geom.bodyTop + max b.ascent height
  if b.cur.lines.isEmpty || b.freshStart then
    b.commit (mk firstY) depth 0 0
  else
    let interline := if b.noInterline then height
      else max (leadingFor tallest b.geom.leading) (b.prevDepth + height + lineskip)
    let y := b.y + b.skip.width + interline
    let overflow := y + depth - bottom
    let above := b.pageShrink + b.skip.shrink
    if overflow ≤ above then
      b.commit (mk y) depth above overflow
    else
      let b := b.brokeTie.finishPage
      b.commit (mk firstY) depth 0 0

private def B.warnOverfull (b : B) : B :=
  { b with diags := b.diags.push (Diag.of .W0005 "overfull line; no feasible break") }

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
  /-- Marker content set as its own items and placed before the first line. -/
  markerSegs : Option (Array Seg × Sp) := none
  /-- A rule filling the first line after the content. -/
  rule : Option (Sp × Ir.Color) := none

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
  /-- A full-measure horizontal rule as its own line: the title page's
  separator. Placed through `placeLine`, so it spaces, breaks pages, and
  distributes exactly as a line of text does. -/
  | hrule (color : Ir.Color) (thickness : Sp)
  /-- A table rule row, already set: rule (and gap) segs starting at `x`,
  covering `w`. Placed at exactly the pending skip below the previous ink —
  booktabs' padding is the declared seps and nothing else — and it marks
  the builder `noInterline`, so the row below stacks flush too. -/
  | tableRule (thickness : Sp) (x w : Sp) (segs : Array Seg)
  /-- Content placed so far on the open page is chrome pinned to the page
  top — the frame title and its bar: the page's vertical distribution
  moves only the lines and fills that follow, as beamer distributes the
  body below the frametitle, never the frametitle itself. -/
  | pin
  /-- A progress bar under the line just placed: `bg` across `w` from `x`,
  `fg` over the leading `num/den` of it, `thick` tall. -/
  | progress (num den : Nat) (fg bg : Ir.Color) (thick x w : Sp)
  /-- The chrome footer for pages closed from here on: a frame sets it (its
  own number, the section in force), a section page or standout frame
  clears it, and a spill page inherits its frame's. -/
  | foot (content : Option (Array Ir.BandSlot))
  /-- The logo state changes here: pages from this point carry `content`
  (empty clears). Applied by the furniture pass, keyed to page indexes. -/
  | setLogo (content : Array Ir.Inline)
  /-- An elaborated picture placed with its left edge at page x — fills and
  label lines through one `Pic.Place` transform, fitted vertically the way
  a line of the picture's height is. -/
  | picture (x : Sp) (pic : Ir.Pic.Picture)
  /-- The seam between a float's object and its caption: the two belong
  together on one page, and the engine has no keep-together yet. Placement
  consumes it at the next line: a page break landing exactly here is
  reported (W0339, pending), never silent. -/
  | tie

/-- The block walk owes a gap before the next line rather than emitting one
as it goes, because what the gap is depends on everything declared between
two lines. The rules are LaTeX's. `\vspace` is a `\vskip`: it adds. An
element's own space — a heading's `before`, a list's `topsep` — is an
`\addvspace`: against glue already owed it takes the larger, so a list's
bottom space and the heading after it do not stack. `parskip`, the default
between peers, is paid only when nothing was declared. `wantDefault` marks a
peer boundary, `owed` is the glue sequence, `flushGap` pays it when the next
line comes. -/
private structure Acc where
  geom : Geom
  xHeight : Sp
  styles : Ir.Styles := {}
  /-- The `slides` class: frames and sections open fresh pages. -/
  slides : Bool := false
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
  hyphCache : Std.HashMap String (List Nat) := {}
  /-- The document's loaded images, from the driver: layout only measures
  and places them; the bytes ride to the backends. -/
  imgs : Image.Store := {}

/-- A declared length with its rubber: `1.8ex plus 0.8ex minus 0.4ex` keeps
all three parts, so a page can take up the slack the author allowed. -/
private def Acc.resolve (a : Acc) (g : SymGlue) : Glue :=
  g.resolve a.geom.fontSize a.xHeight

private def Acc.parskip (a : Acc) : Glue := a.resolve a.geom.parskip

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
private def Acc.flushGap (a : Acc) : Acc :=
  let a := if a.owed.isEmpty then
      (if a.wantDefault then { a with ops := a.ops.push (.skip a.parskip) } else a)
    else { a with ops := a.ops.push (.skip (a.owed.foldl Glue.add {})) }
  { a with wantDefault := false, owed := #[] }

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

private def Acc.style (a : Acc) (element : String) : Ir.ElementStyle :=
  (a.styles.find? element).getD {}

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

private def collectPara (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (inlines : Array Inline) (indent : Sp) (center : Bool) (size : Sp)
    (baseStyle : TextStyle := {})
    (marker : Option (Array Inline) := none)
    (rule : Option (Sp × Ir.Color) := none) : Acc :=
  let a := a.flushGap
  -- The page's text colour is the default: content that declared its own
  -- keeps it, so a themed page colours everything or nothing silently dies
  -- on a dark standout background.
  let baseStyle := if baseStyle.color == Ir.Color.black then
      { baseStyle with color := a.fg } else baseStyle
  let (items, ds, cache, extras) :=
    itemsOfInlines pats size a.xHeight fs baseStyle inlines a.hyphCache a.imgs
      a.geom.textWidth a.geom.textHeight
  let items := if a.geom.justify then items else raggedItems items
  -- A marker is content: set as a line of its own, unjustified, so it can
  -- carry any style the document gave it. Its diagnostics ride with the
  -- paragraph's — a marker glyph no face covers must warn, not vanish.
  let (markerSegs, ds, cache) := match marker with
    | some m =>
      let (mi, mds, cache, _) :=
        itemsOfInlines pats size a.xHeight fs { color := a.fg } m cache
          a.imgs a.geom.textWidth a.geom.textHeight
      let (segs, w, _) := setLine mi (lineStart mi 0) (mi.size - 1) a.geom.textWidth false
      (some (segs, w), ds ++ mds, cache)
    | none => (none, ds, cache)
  { a with
    hyphCache := cache
    ops := a.ops.push (.para {
      items := items, extras := extras, diags := ds
      target := (a.measure.getD a.geom.textWidth) - indent
      indent := indent, center := center, size := size
      justify := a.geom.justify
      markerSegs := markerSegs, rule := rule }) }

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
  | 1 => geom.fontSize * ((Ir.sizeScale.lookup "Large").getD 1000) / 1000
  | 2 => geom.fontSize * ((Ir.sizeScale.lookup "large").getD 1000) / 1000
  | _ => geom.fontSize

private theorem heading_hierarchy_int (x : Int) (h : 1 * 65536 ≤ x) :
    x * 1440 / 1000 > x * 1200 / 1000 ∧ x * 1200 / 1000 ≥ x := by
  omega

/-- Heading hierarchy (arch-design I3): at every base size of at least one
point, a section sets strictly larger than a subsection, and no heading
sets smaller than its body. The scale (`Ir.sizeScale`, size10.clo's own
values) carries the ordering; the 1 pt floor is what strictness costs
under integer division — below 9 sp (~0.00014 pt) the two levels round
together, so the bound is the coarsest honest one. (The arithmetic lives
in the `Int`-typed lemma above: `omega` reads `Int` syntactically and
does not unfold the `Sp` abbreviation.) -/
theorem heading_hierarchy (g : Geom)
    (hfs : pt 1 ≤ g.fontSize) : -- 1 pt floor: what strictness costs under integer division (docstring)
    sectionSize g 1 > sectionSize g 2 ∧ sectionSize g 2 ≥ g.fontSize := by
  have e1 : sectionSize g 1 = g.fontSize * 1440 / 1000 := by rfl
  have e2 : sectionSize g 2 = g.fontSize * 1200 / 1000 := by rfl
  rw [e1, e2]
  simp only [pt, spPerPt] at hfs
  exact heading_hierarchy_int g.fontSize hfs

/-- Display type: headings, frame titles, section-page and standout text.
Display is not body text: it is never hyphenated (Butterick, Practical
Typography, "Hyphenation": suppress automatic hyphenation where lines are
short — headings foremost — because a break there costs more than it
saves), and therefore never justified either (Butterick, "Justified
text": justification without hyphenation leaves the breaker only word
spaces, and a two-word display line stretches across the whole measure;
moloch's own title and title-page templates are `\raggedright`). The
door takes no patterns and forces ragged, so no heading path can do
either by construction — the invariant is the signature. -/
private def collectDisplay (a : Acc) (fs : FontSet)
    (inlines : Array Inline) (indent : Sp) (center : Bool) (size : Sp)
    (baseStyle : TextStyle := {})
    (rule : Option (Sp × Ir.Color) := none) : Acc :=
  let sub := collectPara { a with geom := { a.geom with justify := false } }
    none fs inlines indent center size (baseStyle := baseStyle) (rule := rule)
  { sub with geom := a.geom }

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

/-- Lay out a `.table`: booktabs' formal table. Columns take their declared
fraction of the measure (or their widest cell), separated by `2·tabcolsep`
(classes.dtx) with the outer pads under `@{}`'s control; each row places
its cells through the column machinery (`colOpen`/`colNext`/`colClose`), so
a row advances by its tallest cell; rules are set rows of rule segments at
booktabs' weights, padded by exactly their declared seps — `tableRule`
placement stacks flush, no leading. `center` centres the whole table box in
the measure (a table under `\centering` or inside a float). -/
private def collectTable (a0 : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (cols : Array Ir.ColSpec) (padL padR : Bool)
    (rows : Array (Array (Array Inline))) (rules : Array (Nat × Ir.TableRule))
    (indent : Sp) (center : Bool) : Acc := Id.run do
  if cols.isEmpty then
    return a0
  let mut a := a0.flushGap
  let size := a.geom.fontSize
  let tok (name : String) (dflt : Dim.Length) : Sp :=
    match a.tokens.find? name with
    | some g => (a.resolve g).width
    | none => dflt.resolve size a.xHeight
  let colsep := tok "tabcolsep" Ir.tabColSep
  let total := (a.measure.getD a.geom.textWidth) - indent
  -- Natural widths, measured per cell (needed for `l`/`c`/`r` column
  -- widths and for right-aligned placement). The measuring pass drops its
  -- diagnostics: the setting pass below emits them once.
  let mut nats : Array (Array Sp) := #[]
  let mut cache := a.hyphCache
  for row in rows do
    let mut rowNats : Array Sp := #[]
    for cell in row do
      let (items, _, c, _) :=
        itemsOfInlines pats size a.xHeight fs { color := a.fg } cell cache
          a.imgs a.geom.textWidth a.geom.textHeight
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
    for (k, r) in rules do
      if k == i then here := here.push r
    let mut hi := 0
    for _ in [0:here.size] do
      if h : hi < here.size then
        match here[hi] with
        | .gap g =>
          -- exactly this space: it replaces a neighbouring rule's sep
          pendBelow := none
          a := { a with ops := a.ops.push (.skip { width := (a.resolve g).width }) }
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
                let l' := a.geom.hmargin + l
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
        | r =>
          let (th, ab, be) := match r with
            | .top => (heavy, aboveTop, belowSep)
            | .bottom => (heavy, aboveSep, belowBottom)
            | _ => (light, aboveSep, belowSep)
          let sep := match prev with
            | 1 => dbl
            | 2 => 0
            | _ => ab
          let ops := (a.ops.push (.skip { width := sep })).push
            (.tableRule th (a.geom.hmargin + x0) tableW #[.rule tableW th 0 fg])
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
          let sub := match spec.align with
            | .center => collectPara sub pats fs cell x true size
            | .right =>
              let nat := ((nats[i]?).bind (·[j]?)).getD 0
              collectPara sub pats fs cell (x + max 0 (wj - nat)) false size
            | .left => collectPara sub pats fs cell x false size
          a := { a with
            ops := a.ops ++ sub.ops
            hyphCache := sub.hyphCache
            diags := sub.diags }
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
private def collectPicture (a : Acc) (pic : Ir.Pic.Picture) (indent : Sp)
    (center : Bool) : Acc :=
  let ((px0, _), (px1, py1)) := pic.bbox
  let w := px1 - px0
  let h := py1 - pic.bbox.1.2
  let avail := (a.measure.getD a.geom.textWidth) - indent
  let a := if w > avail || h > a.geom.textHeight then
      { a with diags := a.diags.push (Diag.of .W0335
        (s!"the picture is {w.toPtString}pt × {h.toPtString}pt against a text area " ++
          s!"of {avail.toPtString}pt × {a.geom.textHeight.toPtString}pt; it may overrun \
the page")
        (help := "shrink the picture ([scale=...]) or widen the text area \
(\\page{ margin = ... })")) }
    else a
  let x := if center then indent + max 0 ((avail - w) / 2) else indent
  let a := a.flushGap
  { a with ops := a.ops.push (.picture (a.geom.hmargin + x) pic) }

mutual

/-- Walk a block sequence, spacing peers by `parskip`. -/
private def collectBlocks (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (blocks : Array Block) (indent : Sp) : Acc :=
  collectBlockList a pats fs blocks.toList indent true

private def collectBlockList (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (blocks : List Block) (indent : Sp) (first : Bool) : Acc :=
  match blocks with
  | [] => a
  | blk :: rest =>
    let a := if first then a else a.wantGap
    let a := collectBlock a pats fs blk indent
    collectBlockList a pats fs rest indent false

/-- One list item: its leading paragraph carries the marker. -/
private def collectItem (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (item : List Block) (indent : Sp) (first : Bool) (marker : Array Inline) : Acc :=
  match item with
  | [] => a
  | blk :: rest =>
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
        collectPara a pats fs content indent false a.geom.fontSize
          (marker := some marker)
      | _, _ => collectBlock a pats fs blk indent
    collectItem a pats fs rest indent false marker

private def collectItems (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (items : List (Array Block)) (indent : Sp) (st : Ir.ElementStyle)
    (ordered : Bool) (level : Nat) (idx : Nat) : Acc :=
  match items with
  | [] => a
  | item :: rest =>
    -- Items are peers separated by the declared gap. The default is none,
    -- as it was: a list is one block, and its leading is its rhythm.
    let a := match idx == 1, st.gap with
      | false, some g => a.addvspace (a.resolve g)
      | _, _ => a
    -- The item's marker: the declared style, or the class default for the
    -- level and, for enumerate, this item's number. The class glyph is
    -- checked against the loaded faces so it degrades to its stand-in
    -- rather than to nothing.
    let covered := fun c =>
      (fs.body.gid c).isSome || (fs.fallbackFor c).isSome
    let marker := st.marker.getD (ListMark.marker ordered level idx covered)
    let a := collectItem a pats fs item.toList indent true marker
    collectItems a pats fs rest indent st ordered level (idx + 1)

/-- Centered content: paragraphs center, anything else nests unchanged. -/
private def collectCentered (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (body : List Block) (indent : Sp) : Acc :=
  match body with
  | [] => a
  | blk :: rest =>
    let a := match blk with
      | .para content => collectPara a pats fs content indent true a.geom.fontSize
      -- The centred title block: the level-0 heading centres with the
      -- furniture around it, at the same LARGE bold the uncentred path sets.
      | .section 0 _ title =>
        collectDisplay a fs title indent true
          (a.geom.fontSize * ((Ir.sizeScale.lookup "LARGE").getD 1000) / 1000)
          (baseStyle := { bold := true })
      -- A centred picture: its box centres in the measure, as the lines of
      -- a centred paragraph do.
      | .picture pic => collectPicture a pic indent true
      -- A table under \centering (or in a float's centred body) centres
      -- as one box in the measure; its cells keep their own alignment.
      | .table cols pl pr rows rules =>
        collectTable a pats fs cols pl pr rows rules indent true
      | _ => collectBlock a pats fs blk indent
    collectCentered (if rest.isEmpty then a else a.wantGap) pats fs rest indent

/-- One column after another: each collects against its own measure at its
own offset, a `colNext` marker between two so placement rewinds the
vertical position. The hyphenation cache threads through; the outer
measure and gap state are restored per column. -/
private def collectColumns (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
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
    let sub := collectBlocks sub pats fs body x0
    let a := { a with
      ops := a.ops ++ sub.ops ++ (if rest.isEmpty then #[] else #[Op.colNext])
      hyphCache := sub.hyphCache }
    collectColumns a pats fs rest (x0 + wi + gutter) shareW gutter total

/-- A standout frame's content: paragraphs centre and set Large bold, in
the page's (inverted) text colour; anything else nests through the normal
walk and still inherits the colour. -/
private def collectStandout (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (body : List Block) (indent : Sp) : Acc :=
  match body with
  | [] => a
  | blk :: rest =>
    let a := match blk with
      | .para content =>
        match (a.style "standout").font with
        | some tpl =>
          collectDisplay a fs (Ir.fillTemplate tpl content) indent true a.geom.fontSize
        | none =>
          collectDisplay a fs content indent true (a.geom.fontSize * 1440 / 1000)
            (baseStyle := { bold := true })
      | _ => collectBlock a pats fs blk indent
    collectStandout (if rest.isEmpty then a else a.wantGap) pats fs rest indent

private def collectBlock (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (blk : Block) (indent : Sp) : Acc :=
  match blk with
  | .para content =>
    collectPara a pats fs content indent false a.geom.fontSize
  | .section level _ title =>
    if level == 0 then
      -- The document title, a heading at level 0: display type at the
      -- scale's LARGE step in the bold face — classes.dtx's \@maketitle
      -- sets {\LARGE \@title \par}. Never a divider: it stands inside the
      -- furniture \maketitle built (the title frame, the centred block),
      -- so it opens no page of its own even in slides.
      collectDisplay a fs title indent false
        (a.geom.fontSize * ((Ir.sizeScale.lookup "LARGE").getD 1000) / 1000)
        (baseStyle := { bold := true })
    else
    -- The section in force, for the footer's \sectiontitle slot.
    let a := if level == 1 then { a with curSection := title } else a
    if a.slides && level == 1 && (a.pal.find? "progressfg").isSome then
      -- The themed section page: its own page, vertically centred, the
      -- title ragged-left in a centred measure with the deck position
      -- drawn under it as a progress bar.
      let a := a.pageBreak
      -- A divider carries no footer; the break above closed the previous
      -- page with its own.
      let a := if a.footAllowed then { a with ops := a.ops.push (.foot none) } else a
      let a := { a with ops := a.ops.push (.pageStyle none VDist.center) }
      -- The centred measure the title and the bar share: moloch's own
      -- 0.7875 of the line width (beamerinnerthememoloch.dtx, section page
      -- progressbar template: \begin{minipage}{0.7875\linewidth}).
      let mp : Sp := a.geom.textWidth * 7875 / 10000
      let indent : Sp := (a.geom.textWidth - mp) / 2
      let st := a.style "sectionpage"
      let a := match st.font with
        | some tpl =>
          collectDisplay a fs (Ir.fillTemplate tpl title) indent false a.geom.fontSize
        | none =>
          collectDisplay a fs title indent false (a.geom.fontSize * 1440 / 1000)
            (baseStyle := { bold := true })
      let fgC := (a.pal.find? "progressfg").getD a.fg
      let bgC := (a.pal.find? "progressbg").getD ((a.pal.find? "bg").getD Ir.Color.white)
      -- The fallback is moloch's own default, `progressbar linewidth=1pt`
      -- (beamerouterthememoloch.dtx, \moloch@outer@setdefaults) — the same
      -- value the bundles declare through the token.
      let thick := ((a.tokens.find? "progressheight").map
        fun g => (a.resolve g).width).getD (pt 1)
      -- No clamp: every threaded position is a some of `Ir.frameNumbers`,
      -- ≤ the denominator by theorem (`frameNumbers_le_count`) — moloch
      -- clamps (beamerouterthememoloch.dtx:290) only because its total
      -- comes from a lagging aux file, and this engine has no aux file to
      -- lag. A deck with no countable frame has no position to show, so
      -- it draws no bar at all rather than a fraction over a fake 1.
      let a := if a.frameCount == 0 then a else
        { a with ops := a.ops.push (.progress
          a.framesDone a.frameCount fgC bgC thick
          (a.geom.hmargin + indent) mp) }
      a.pageBreak
    else
    -- In slides, a section is a divider: its own page between frames rather
    -- than a heading dropped onto the bottom of the previous slide.
    let a := if a.slides then a.pageBreak else a
    let a := if a.footAllowed then
        { a with ops := a.ops.push (.foot none) } else a
    let element := match level with
      | 1 => "section" | 2 => "subsection" | _ => "subsubsection"
    let st := a.style element
    -- Undeclared, a heading stands twice the default gap above its body.
    let a := a.addvspace ((st.before.map a.resolve).getD (a.parskip.add a.parskip))
    -- A declared font template wraps the title; without one, headings set in
    -- the bold face of the body family at the level's size.
    let a := match st.font with
      | some tpl =>
        collectDisplay a fs (Ir.fillTemplate tpl title) indent false a.geom.fontSize
          (rule := st.rule.map fun (r : Ir.Color × Option String) =>
            (headingRuleWeight a.geom.fontSize, r.1))
      | none =>
        collectDisplay a fs title indent false (sectionSize a.geom level)
          (baseStyle := { bold := true })
          (rule := st.rule.map fun (r : Ir.Color × Option String) =>
            (headingRuleWeight a.geom.fontSize, r.1))
    let a := match st.after with
      | some g => a.vskip (a.resolve g)
      | none => a
    if a.slides then a.pageBreak else a
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
    let st := if level == 1 then a.style element
      else (a.styles.find? s!"{element}{level}").getD (a.style element)
    -- LaTeX's `topsep`: the declared space stands above the list and below it.
    let a := match st.before with
      | some g => a.addvspace (a.resolve g)
      | none => a
    let indent := indent + (st.indent.map fun g => (a.resolve g).width).getD a.geom.listIndent
    let a := if ordered then { a with enumDepth := depth } else { a with itemDepth := depth }
    let a := collectItems a pats fs items.toList indent st ordered level 1
    let a := if ordered then { a with enumDepth := depth - 1 }
      else { a with itemDepth := depth - 1 }
    match st.before with
    | some g => a.addvspace (a.resolve g)
    | none => a
  | .center body =>
    collectCentered a pats fs body.toList indent
  -- A role is a name for the HTML class hook; the page it does not touch:
  -- the body collects exactly as it would unwrapped (role_transparent_layout).
  | .role _ body =>
    collectBlocks a pats fs body indent
  | .quote body =>
    -- A quotation is set off by indenting both margins by the list indent:
    -- classes.dtx defines quote and quotation as `\list{}{\rightmargin
    -- \leftmargin}`, and a top-level list's \leftmargin is \leftmargini —
    -- the same indent the engine's lists take. The right edge moves in by
    -- narrowing the measure the body collects against; the outer measure
    -- is restored after, exactly as a column restores it.
    let saved := a.measure
    let sub := { a with
      measure := some ((a.measure.getD a.geom.textWidth) - a.geom.listIndent) }
    let sub := collectBlocks sub pats fs body (indent + a.geom.listIndent)
    { sub with measure := saved }
  | .columns cols =>
    -- Declared widths are per mille of the full measure. The leftover goes
    -- to the widthless columns in equal shares when there are any, and into
    -- equal gutters between the columns otherwise.
    let a := a.flushGap
    let total := (a.measure.getD a.geom.textWidth) - indent
    let declared := cols.foldl (fun s (c : Option Nat × Array Block) =>
      s + ((c.1.map fun f => total * f / 1000).getD 0)) 0
    let unspecified := cols.foldl (fun c (col : Option Nat × Array Block) =>
      if col.1.isNone then c + 1 else c) 0
    let rem := max 0 (total - declared)
    let shareW := if unspecified > 0 then rem / unspecified else 0
    let gutter := if unspecified == 0 && cols.size > 1 then rem / (cols.size - 1) else 0
    let a := { a with ops := a.ops.push .colOpen }
    let a := collectColumns a pats fs cols.toList indent shareW gutter total
    { a with ops := a.ops.push .colClose }
  | .spaced before body =>
    -- Declared space above the block, resolved against the body font: the
    -- gap in place of the default, added to any other declared glue — a
    -- bare `\vspace` after a list adds to the list's `topsep`, as in LaTeX.
    let a := a.vskip (a.resolve before)
    collectBlocks a pats fs body indent
  | .step _ _ body =>
    -- Pure grouping: any dimming was painted into colours before layout.
    collectBlocks a pats fs body indent
  | .only _ body =>
    -- `run` already kept this node for the PDF (`Ir.keepFor "pdf"`), so by
    -- here it is pure grouping, exactly as a resolved step is.
    collectBlocks a pats fs body indent
  | .nav _ body =>
    -- A landmark is an HTML notion; the page keeps the content, transparent.
    collectBlocks a pats fs body indent
  | .note _ =>
    -- A speaker note is not handout content: no lines, no gap.
    a
  | .pagebreak =>
    -- The declared boundary: the builder closes only pages holding
    -- something, so adjacent breaks never make a blank page.
    a.pageBreak
  | .logo content =>
    -- A stateful declaration: the pages from here on carry this content at
    -- their corner. No lines, no gap; placement reads the spans.
    { a with ops := a.ops.push (.setLogo content) }
  | .verbatim covered s =>
    -- Code lines, kept literally, at the scale's own \footnotesize (the
    -- code-frame convention) — derived from the table, not a loose decimal.
    -- No hyphenation patterns: the engine must never invent a hyphen inside
    -- an identifier. A pending overlay's shade rides in `covered`: code
    -- must read as covered like any other text.
    let inner : Array Ir.Inline := #[.styled .mono (Ir.verbatimInlines s)]
    let inner := match covered with
      | some c => #[.colored c none inner]
      | none => inner
    collectPara a none fs inner indent false
      (a.geom.fontSize * ((Ir.sizeScale.lookup "footnotesize").getD 1000) / 1000)
  | .framefoot content =>
    -- Not a line, a state change: the note the following frames' footers
    -- carry. Empty clears back to the chrome default.
    { a with frameFoot := if content.isEmpty then none else some content }
  | .rule color _ thickness =>
    -- The title page's separator: colour and thickness were declared
    -- (palette `separator`, token `separatorheight`); the measure is the
    -- text width, as moloch draws it.
    let a := a.flushGap
    { a with ops := a.ops.push (.hrule color (a.resolve thickness).width) }
  | .picture pic =>
    -- Left on the current indent, as LaTeX places the box where it stands;
    -- a `{center}` around it goes through `collectCentered`'s arm.
    collectPicture a pic indent false
  | .table cols padL padR rows rules =>
    collectTable a pats fs cols padL padR rows rules indent false
  | .float _ capAbove body caption =>
    -- Set off from the text by `floatsep` on both sides, the caption bound
    -- `captionsep` from the content (`caption_gaps_rhythm` holds the
    -- defaults to the rhythm); the body centres, the figure convention the
    -- old center-wrapping gave. Both gaps are `\addvspace`-style: an
    -- element's own space, never stacked onto a neighbour's.
    let floatSep := a.resolve ((a.tokens.find? "floatsep").getD Ir.floatSepDefault)
    let capSep := a.resolve ((a.tokens.find? "captionsep").getD Ir.captionSepDefault)
    let a := a.addvspace floatSep
    -- classes.dtx `\@makecaption`: a caption that fits one line centres; a
    -- longer one sets as an ordinary paragraph.
    let setCaption (a : Acc) : Acc :=
      if caption.isEmpty then a else
      let (items, _, cache, _) :=
        itemsOfInlines pats a.geom.fontSize a.xHeight fs { color := a.fg } caption
          a.hyphCache a.imgs a.geom.textWidth a.geom.textHeight
      let a := { a with hyphCache := cache }
      let fits := itemsNaturalWidth items ≤ (a.measure.getD a.geom.textWidth) - indent
      collectPara a pats fs caption indent fits a.geom.fontSize
    let a := if capAbove then
      let a := setCaption a
      let a := if caption.isEmpty then a else
        a.addvspace capSep |>.pushOp .tie
      collectCentered a pats fs body.toList indent
    else
      let a := collectCentered a pats fs body.toList indent
      let a := if caption.isEmpty then a else
        a.addvspace capSep |>.pushOp .tie
      setCaption a
    a.addvspace floatSep
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
        { a with ops := a.ops.push (.foot (if a.frameNum.isNone then none else a.chromeFoot)) }
      else a
    -- Every frame declares its distribution (beamer's default is centring,
    -- user guide §8.1); only the article page and a continuation page keep
    -- the builder's top-flush default.
    if standout then
      -- Inverted, centred, Large bold. The palette's standout keys
      -- override; without them the frame inverts the page's own colours.
      let bg := (a.pal.find? "standoutbg").getD ((a.pal.find? "fg").getD Ir.Color.black)
      let fg := (a.pal.find? "standoutfg").getD ((a.pal.find? "bg").getD Ir.Color.white)
      let a := { a with ops := a.ops.push (.pageStyle (some bg) (VDist.of valign)) }
      let saved := a.fg
      let a := collectStandout { a with fg := fg } pats fs body.toList indent
      let a := { a with fg := saved }
      a.pageBreak
    else
    let a := { a with ops := a.ops.push (.pageStyle none (VDist.of valign)) }
    let a := if title.isEmpty then a else
      match a.pal.find? "frametitlebg" with
      | some barBg =>
        -- The themed frame title is a colour bar across the whole page,
        -- its text in frametitlefg on it.
        let ftFg := (a.pal.find? "frametitlefg").getD
          ((a.pal.find? "bg").getD Ir.Color.white)
        let saved := a.fg
        let a := { a with fg := ftFg }
        let st := a.style "frametitle"
        let a := match st.font with
          | some tpl =>
            collectDisplay a fs (Ir.fillTemplate tpl title) 0 false a.geom.fontSize
          | none =>
            collectDisplay a fs title 0 false (sectionSize a.geom 1)
              (baseStyle := { bold := true })
        let a := { a with fg := saved
                          ops := a.ops.push (.titleBar barBg (a.geom.fontSize / 2)) }
        { a with wantDefault := true }
      | none =>
        let a := collectDisplay a fs title 0 false (sectionSize a.geom 1)
          (baseStyle := { bold := true })
        { a with wantDefault := true }
    -- The title just placed is page-top chrome: the frame's distribution
    -- moves the body below it, never the title (beamer's frametitle).
    let a := if title.isEmpty then a else { a with ops := a.ops.push .pin }
    -- A golden frame is the title page (only \maketitle declares golden),
    -- and everything on it is display furniture: titles never hyphenate
    -- and never justify (collectDisplay's rule, through the declaration).
    let a := if valign matches .golden then
        let sub := collectBlocks { a with geom := { a.geom with justify := false } }
          none fs body indent
        { sub with geom := a.geom }
      else collectBlocks a pats fs body indent
    a.pageBreak

end

/-- Underline rules for one set line: a second walk over its segs, aligned by
gaps, so it can ride as its own `LineOut` at the same baseline — the PDF
writer's x-tracking stays linear and link rectangles see no extra runs. Each
rule sits at its run's own normalized `post` metrics (`Font.band`) and is
interrupted where glyph ink crosses the band — `Font.inkAt`, from the
outline — with a gap of twice the owning run's rule thickness on each side.
Obstructions are collected in line coordinates across the whole line first,
every glyph run contributing whether or not it is underlined, so ink that
reaches over a run boundary — a negative-sidebearing italic descender, or a
descender's clearance spilling past its own advance — clears the
neighbouring rule too. An obstruction is judged against the band of the run
that owns the glyph; the clearance dilation absorbs the small band
differences between adjacent faces. Empty when the line has no underlined
run, so the common case allocates nothing. -/
private def underlineSegs (fs : FontSet) (lineSize : Sp) (segs : Array Seg) :
    Array Seg := Id.run do
  unless segs.any (fun s => match s with
      | .run _ _ _ _ _ _ true _ => true
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
    | .run fontIdx _ _ w glyphs size _ _ =>
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
  -- Merge: sorted by the low bound, `min`/`max` so no ordering assumption
  -- survives into the result.
  let sorted := obs.qsort fun a b => a.1 < b.1
  let mut merged : Array (Sp × Sp) := #[]
  for (lo, hi) in sorted do
    match merged.back? with
    | some (plo, phi) =>
      if lo ≤ phi then merged := merged.pop.push (min plo lo, max phi hi)
      else merged := merged.push (lo, hi)
    | none => merged := merged.push (lo, hi)
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
    | .run fontIdx color _ w _ size underline _ =>
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
        for (olo, ohi) in merged do
          let lo := max olo x
          let hi := min ohi (x + w)
          if lo < hi then
            if lo > cur then
              out := out.push (.rule (lo - cur) thick raise color)
            out := out.push (.gap (hi - max lo cur))
            cur := hi
        if x + w > cur then
          out := out.push (.rule (x + w - cur) thick raise color)
      x := x + w
  return out

/-- Place one paragraph's lines from precomputed breakpoints. -/
private def placePara (fs : FontSet) (b : B) (j : ParaJob) (breaks : Array Nat) : B := Id.run do
  let mut b := { b with diags := b.diags ++ j.diags }
  let geom := b.geom
  let width := j.target
  let mut prev := 0
  let mut first := true
  for brk in breaks do
    let a := if first then lineStart j.items 0 else lineStart j.items (prev + 1)
    let (segs, w, overfull) := setLine j.items a brk width (!j.center && j.justify)
    if overfull then
      b := b.warnOverfull
    let mut x := if j.center then geom.hmargin + j.indent + (width - w) / 2
      else geom.hmargin + j.indent
    let mut segs := segs
    let mut w := w
    if first then
      -- The marker stands `\labelsep` left of the item: half an em,
      -- LaTeX's own separation (classes.dtx: \setlength\labelsep{.5em}).
      let sep := geom.fontSize / 2
      if let some (ms, mw) := j.markerSegs then
        segs := ms ++ #[Seg.gap sep] ++ segs
        x := x - mw - sep
        w := w + mw + sep
      if let some (thickness, color) := j.rule then
        -- The rule fills what the heading left of its line, a word-space
        -- away from the text, sitting at half the x-height like a dash.
        let gap := j.size / 2
        let ruleW := width - w - gap
        if ruleW > 0 then
          segs := segs ++ #[Seg.gap gap, Seg.rule ruleW thickness (b.xHeight / 2) color]
          w := width
    b := b.placeLine fs x j.size segs w
    -- The line's underlines, as a sibling at the same baseline. Pushed after
    -- `placeLine` so a page break has already decided where the text landed;
    -- the rules land beside it, adding no vertical space.
    let uSegs := underlineSegs fs j.size segs
    unless uSegs.isEmpty do
      if let some last := b.cur.lines.back? then
        b := b.pushSibling
          { x := last.x, y := last.y, size := last.size, segs := uSegs, setWidth := 0 }
    if let some extra := j.extras[brk]? then
      b := { b with skip := { b.skip with width := b.skip.width + extra } }
    prev := brk
    first := false
  return b

mutual

/-- Replace `\pagenumber` / `\pagecount` with literal text. Running content
is laid out after the body, so both numbers are known by then — no second
pass over the document and no aux file. -/
def substPage (n total : Nat) (xs : Array Inline) : Array Inline :=
  (substPageList n total xs.toList).toArray

def substPageOne (n total : Nat) : Inline → Inline
  | .pageNumber => .text (toString n)
  | .pageCount => .text (toString total)
  | .styled st body => .styled st (substPageList n total body.toList).toArray
  | .colored c nm body => .colored c nm (substPageList n total body.toList).toArray
  | .role nm body => .role nm (substPageList n total body.toList).toArray
  | .link u body => .link u (substPageList n total body.toList).toArray
  | .underline body => .underline (substPageList n total body.toList).toArray
  | .step s last body => .step s last (substPageList n total body.toList).toArray
  | .text s => .text s
  | .math d src => .math d src
  -- a formula's body is math atoms and an image carries no inline body:
  -- neither can hold a page-number placeholder
  | .formula d src body => .formula d src body
  | .image src size alt => .image src size alt
  | .icon s l => .icon s l
  | .fill => .fill
  | .linebreak e => .linebreak e

def substPageList (n total : Nat) : List Inline → List Inline
  | [] => []
  | x :: rest => substPageOne n total x :: substPageList n total rest

end

mutual

/-- The physical pass rewrites exactly the physical placeholders: content
carrying none is untouched. This is the substitution half of "the two
sequences stay distinct" — `Ir.frame_sequence_carries_no_physical` is the
rendering half. -/
theorem substPageOne_id (n total : Nat) (x : Inline)
    (h : Ir.hasPhysicalPageOne x = false) : substPageOne n total x = x := by
  match x with
  | .pageNumber => simp [Ir.hasPhysicalPageOne] at h
  | .pageCount => simp [Ir.hasPhysicalPageOne] at h
  | .styled st body =>
    rw [Ir.hasPhysicalPageOne] at h
    rw [substPageOne, substPageList_id n total body.toList h]
  | .colored c nm body =>
    rw [Ir.hasPhysicalPageOne] at h
    rw [substPageOne, substPageList_id n total body.toList h]
  | .role nm body =>
    rw [Ir.hasPhysicalPageOne] at h
    rw [substPageOne, substPageList_id n total body.toList h]
  | .link u body =>
    rw [Ir.hasPhysicalPageOne] at h
    rw [substPageOne, substPageList_id n total body.toList h]
  | .underline body =>
    rw [Ir.hasPhysicalPageOne] at h
    rw [substPageOne, substPageList_id n total body.toList h]
  | .step s last body =>
    rw [Ir.hasPhysicalPageOne] at h
    rw [substPageOne, substPageList_id n total body.toList h]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _ | .fill
  | .linebreak _ => rw [substPageOne]

theorem substPageList_id (n total : Nat) (xs : List Inline)
    (h : Ir.hasPhysicalPageList xs = false) :
    substPageList n total xs = xs := by
  match xs with
  | [] => rw [substPageList]
  | x :: rest =>
    rw [Ir.hasPhysicalPageList, Bool.or_eq_false_iff] at h
    rw [substPageList, substPageOne_id n total x h.1,
      substPageList_id n total rest h.2]

end

/-- Content with no physical placeholder survives the physical pass whole. -/
theorem substPage_id (n total : Nat) (xs : Array Inline)
    (h : Ir.hasPhysicalPage xs = false) : substPage n total xs = xs := by
  rw [substPage, substPageList_id n total xs.toList h]

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
  | hrule (color : Ir.Color) (thickness : Sp)
  | tableRule (thickness : Sp) (x w : Sp) (segs : Array Seg)
  | pin
  | progress (num den : Nat) (fg bg : Ir.Color) (thick x w : Sp)
  | foot (content : Option (Array Ir.BandSlot))
  | para (j : ParaJob) (t : Task (Array Nat))
  | colOpen
  | colNext
  | colClose
  | setLogo (content : Array Ir.Inline)
  | picture (x : Sp) (pic : Ir.Pic.Picture)
  | tie

/-- Placement state saved at a `colOpen`, restored per column: where the
columns start, and the lowest bottom any column reached so far. -/
private structure ColSave where
  y : Sp
  prevDepth : Sp
  skip : Glue
  fresh : Bool
  /-- The `noInterline` state at the open: every cell of a row under a
  table rule stacks flush, not only the first. -/
  flush : Bool
  bottomY : Sp
  bottomDepth : Sp

/-- Typeset a document body into positioned pages. Geometry is resolved by
the caller via `Geom.ofPage`, so layout has one source of truth. -/
def run (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns) (doc : Doc)
    (imgs : Image.Store := {}) :
    Out := Id.run do
  -- The PDF's view of the document: backend conditionals resolve here, at
  -- the backend's entry, so no later pass can see content another backend
  -- owns (`Ir.keepFor_covers` is why dropping here cannot lose content).
  let doc := { doc with body := Ir.keepFor "pdf" doc.body }
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
  let footAllowed := doc.docClass == "slides" && doc.foot.isNone
  let hasFrameFoot := doc.body.any fun blk => match blk with
    | .framefoot xs => !xs.isEmpty
    | _ => false
  let chromeActive := footAllowed && (doc.chrome.hasFooter || hasFrameFoot)
  -- The footer's size is a step of the scale and its colour a palette key,
  -- never a literal: the theme declares both.
  let footSize := geom.fontSize * ((Ir.sizeScale.lookup "small").getD 1000) / 1000
  -- A footer reserves its band before anything is placed, so no body line
  -- can land in it (`bodyBottom_clears_footer` is the sufficiency proof).
  -- With the default margins the half margin holds the foot line whole and
  -- the band is zero: an undeclared page is unchanged.
  let geom := if doc.foot.isSome then
      { geom with footBand := footBandFor geom.vmargin (scale font.ascent) }
    else if chromeActive then
      { geom with footBand :=
          footBandFor geom.vmargin (font.ascent * footSize / (font.unitsPerEm : Int)) }
    else geom
  -- The running head reserves its band the same way, before anything is
  -- placed (`bodyTop_clears_head` is the sufficiency proof). With the
  -- default margins the half margin holds the head line whole and the
  -- band is zero: an undeclared page is unchanged.
  let geom := if doc.head.isSome then
      { geom with headBand :=
          headBandFor geom.vmargin (scale font.ascent) (scale (-font.descent)) }
    else geom
  let xHeight := scale font.xHeight
  -- The resolved design is the one resolving site for the document-level
  -- colours (`Design.ofDoc`): the ink here is the ink `Contrast.docDiags`
  -- judges (`judged_pair_is_shipped`), never a second `getD` chain.
  let design := Ir.Design.ofDoc doc
  let cover := design.cover
  let acc0 : Acc := { geom := geom, xHeight := xHeight, styles := doc.styles
                      slides := doc.docClass == "slides"
                      pal := doc.palette
                      tokens := doc.tokens
                      frameCount := doc.frameCount
                      chromeL := if footAllowed then doc.chrome.footerLeft else none
                      chromeR := if footAllowed then doc.chrome.footerRight else none
                      footAllowed := footAllowed
                      fg := design.fg
                      imgs := imgs }
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
    acc := if firstBlk then acc else acc.wantGap
    firstBlk := false
    match blk with
    | .frame title standout valign body =>
      let num := nums[i]?.getD none
      acc := { acc with frameNum := num, framesDone := num.getD acc.framesDone }
      let steps := Ir.maxStepBlocks body
      if steps ≤ 1 then
        acc := collectBlock acc pats fs
          (.frame title standout valign (Ir.unwrapItemSteps body)) 0
      else
        for k in [1:steps + 1] do
          acc := collectBlock acc pats fs
            (.frame title standout valign (Ir.unwrapItemSteps (Ir.dimBlocks cover k body))) 0
    | other => acc := collectBlock acc pats fs (Ir.unwrapItemStep other) 0
  -- Trailing fil glue stretches on the page it ends (a \vfill nothing
  -- follows is how a page bottom-flushes its leftover), so it must reach
  -- placement; trailing finite glue stays invisible and stays dropped.
  if acc.owed.any (·.fil) then
    acc := { acc with ops := acc.ops.push (.skip (acc.owed.foldl Glue.add {})) }
  -- Break every paragraph in parallel: `kp` is pure and each job independent,
  -- so the tasks race on nothing; joining in document order below keeps the
  -- output independent of scheduling.
  let staged : Array StagedOp := acc.ops.map fun op =>
    match op with
    | .skip g => .skip g
    | .brk => .brk
    | .pageStyle bg c => .pageStyle bg c
    | .titleBar color pad => .titleBar color pad
    | .hrule color th => .hrule color th
    | .tableRule th x w segs => .tableRule th x w segs
    | .pin => .pin
    | .progress num den fg bg thick x w => .progress num den fg bg thick x w
    | .foot c => .foot c
    | .para j => .para j (Task.spawn fun _ => kp j.items j.target)
    | .colOpen => .colOpen
    | .colNext => .colNext
    | .colClose => .colClose
    | .setLogo c => .setLogo c
    | .picture x pic => .picture x pic
    | .tie => .tie
  let b0 : B := {
    geom := geom
    ascent := scale font.ascent
    descent := scale (-font.descent)
    capHeight := scale font.capHeight
    xHeight := xHeight
    docBg := if design.bgDeclared then some design.bg else none
    diags := acc.diags
  }
  let mut b := b0
  let mut prose : Nat := 0
  -- A heading binds to the text it introduces, so its space above must not
  -- be the smaller of the two (the standard rule; Butterick, "space above
  -- and below": the space below should be smaller so the heading sits
  -- visually closer to what follows). Checked only when the document
  -- declared both sides — the defaults satisfy it by theorem.
  for element in ["section", "subsection", "subsubsection"] do
    if let some st := doc.styles.find? element then
      if let (some before, some after) := (st.before, st.after) then
        let up := (before.resolve geom.fontSize xHeight).width
        let down := (after.resolve geom.fontSize xHeight).width
        if down > up then
          b := { b with diags := b.diags.push (Diag.of .W0202
            (s!"'{element}' sets more space below the heading " ++
              s!"({down.toPtString}pt) than above it ({up.toPtString}pt)")
            (help := s!"a heading binds to the text it introduces: in " ++
              s!"\\style\{{element}}\{...} keep 'after' at most 'before'")) }
  let mut colSaves : Array ColSave := #[]
  let mut logoSpans : Array (Nat × Array Inline) := #[]
  for s in staged do
    match s with
    | .setLogo c =>
      -- The page being built (index `pages.size`) and everything after
      -- carry this content; a later span overrides.
      logoSpans := logoSpans.push (b.pages.size, c)
    | .skip g => b := { b with skip := b.skip.add g }
    | .tie => b := { b with tie := true }
    | .brk =>
      -- A boundary closes a page only when the page holds something: two
      -- adjacent frames share one boundary, not an empty page. A style set
      -- for a page that never got content dies with the boundary. Fills
      -- are content too: a picture of fills alone is a page.
      if !b.cur.lines.isEmpty || !b.cur.fills.isEmpty then
        b := b.finishPage
      else
        b := { b with pageBg := none, vdist := .top, pageFils := 0, filsAbove := #[],
                      pinnedLines := 0, pinnedFills := 0 }
    | .pageStyle bg d => b := { b with pageBg := bg, vdist := d }
    | .foot c => b := { b with curFoot := c }
    | .pin =>
      b := { b with pinnedLines := b.cur.lines.size, pinnedFills := b.cur.fills.size }
    | .colOpen =>
      colSaves := colSaves.push {
        y := b.y, prevDepth := b.prevDepth, skip := b.skip
        fresh := b.cur.lines.isEmpty || b.freshStart
        flush := b.noInterline
        bottomY := b.y, bottomDepth := b.prevDepth }
    | .colNext =>
      if let some save := colSaves.back? then
        let save := if b.y > save.bottomY
          then { save with bottomY := b.y, bottomDepth := b.prevDepth }
          else save
        colSaves := colSaves.pop.push save
        b := { b with y := save.y, prevDepth := save.prevDepth, skip := save.skip
                      freshStart := save.fresh, noInterline := save.flush }
    | .colClose =>
      if let some save := colSaves.back? then
        colSaves := colSaves.pop
        let (bottomY, bottomDepth) := if b.y > save.bottomY
          then (b.y, b.prevDepth) else (save.bottomY, save.bottomDepth)
        b := { b with y := bottomY, prevDepth := bottomDepth, skip := {}
                      freshStart := false, noInterline := false }
    | .titleBar color pad =>
      -- The bar sits behind the line just placed: full page width, page
      -- top to `pad` below the line's depth.
      b := match b.cur.lines.back? with
        | some l =>
          let fill : Fill := { x := 0, y := 0, w := b.geom.pageW,
                               h := l.y + b.prevDepth + pad, color := color }
          { b with cur := { b.cur with fills := b.cur.fills.push fill } }
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
      -- `noInterline` makes the next line stack flush, as TeX ignores
      -- `\prevdepth` after an `\hrule`.
      let mk (y : Sp) : LineOut := { x := x, y := y, size := 0, segs := segs, setWidth := w }
      if b.cur.lines.isEmpty || b.freshStart then
        b := { b.commit (mk (b.geom.vmargin + th)) 0 0 0 with noInterline := true }
      else
        let y := b.y + b.prevDepth + b.skip.width + th
        let overflow := y - b.geom.bodyBottom
        let above := b.pageShrink + b.skip.shrink
        if overflow ≤ above then
          b := { b.commit (mk y) 0 above overflow with noInterline := true }
        else
          b := b.brokeTie.finishPage
          b := { b.commit (mk (b.geom.vmargin + th)) 0 0 0 with noInterline := true }
    | .progress num den fg bg thick x w =>
      -- Half a line under the last baseline: the track, then the elapsed
      -- share over it. The bar joins the page's depth so following content
      -- spaces below it.
      let gap := b.geom.fontSize / 2
      let y := b.y + b.prevDepth + gap
      let fills := b.cur.fills.push { x := x, y := y, w := w, h := thick, color := bg }
      let fills := if num == 0 then fills else
        fills.push { x := x, y := y, w := w * (num : Int) / (den : Int), h := thick,
                     color := fg }
      b := { b with cur := { b.cur with fills := fills },
                    prevDepth := b.prevDepth + gap + thick }
    | .para j t =>
      let breaks := t.get
      -- A plain full-measure text paragraph is the continuous reading the
      -- measure band is about; headings, items, code, and columns are not.
      if j.target == geom.textWidth && !j.center && j.size == geom.fontSize &&
          j.markerSegs.isNone && j.rule.isNone then
        prose := max prose breaks.size
      b := placePara fs b j breaks
    | .picture x pic =>
      -- Fit the picture's box the way `placeLine` fits a line of height
      -- `h` and no depth: at the top of a fresh page, else below the last
      -- line's depth, breaking to a new page when even the shrink above
      -- cannot absorb the overflow.
      let ((px0, py0), (px1, py1)) := pic.bbox
      let h := py1 - py0
      let bottom := b.geom.bodyBottom
      let mut yTop := b.geom.vmargin
      let mut above : Sp := 0
      let mut overflow : Sp := 0
      if !(b.cur.lines.isEmpty || b.freshStart) then
        let y := b.y + b.prevDepth + b.skip.width + lineskip
        overflow := y + h - bottom
        above := b.pageShrink + b.skip.shrink
        if overflow ≤ above then
          yTop := y
        else
          b := b.brokeTie.finishPage
          overflow := 0
          above := 0
      -- One transform for everything the picture ships: `Pic.Place` is the
      -- affine map the invertibility and containment theorems range over.
      let place : Ir.Pic.Place := { x0 := x, yTop := yTop, xmin := px0, ymax := py1 }
      let mut fills := b.cur.fills
      let mut lines := b.cur.lines
      let mut shrinks := b.shrinkAbove
      for shape in pic.shapes do
        match shape with
        | .rect rx ry rw rh color =>
          -- The fill's top-left corner is the rect's (min x, max y) corner
          -- through the transform; a negative extent keeps its sorted box.
          let (fx, fy) := place.toPage (min rx (rx + rw), max ry (ry + rh))
          fills := fills.push { x := fx, y := fy,
                                w := max rw (-rw), h := max rh (-rh), color := color }
        | .label lx ly text color scale =>
          let size := b.geom.fontSize * (scale : Int) / 1000
          let (items, _, _, _) := itemsOfInlines none size b.xHeight fs {}
            #[.colored color none #[.text text]] {} imgs b.geom.textWidth b.geom.textHeight
          let breaks := kp items b.geom.textWidth
          if let some brk := breaks[0]? then
            let (segs, w, _) := setLine items (lineStart items 0) brk b.geom.textWidth false
            -- The node's box centres on its anchor, as TikZ anchors a node:
            -- the baseline sits below the centre by half the ink height
            -- less half the depth.
            let (hgt, dep) := segs.foldl (fun (acc : Sp × Sp) seg => match seg with
              | .run idx _ _ _ _ sz _ raise =>
                let font := fs.get idx
                let sz := if sz == 0 then size else sz
                (max acc.1 (scaledAt sz font font.capHeight.toNat + max 0 raise),
                 max acc.2 (scaledAt sz font (-font.descent).toNat + max 0 (-raise)))
              | _ => acc) (0, 0)
            let (cx, cy) := place.toPage (lx, ly)
            lines := lines.push { x := cx - w / 2, y := cy + (hgt - dep) / 2,
                                  size := size, segs := segs, setWidth := w }
            -- Label lines ride with the picture: they share the shrink
            -- above it, so a page set short moves the diagram as one.
            shrinks := shrinks.push above
      b := { b with
        cur := { b.cur with fills := fills, lines := lines }
        shrinkAbove := shrinks
        pageShrink := above
        needed := max b.needed overflow
        y := yTop + h
        prevDepth := 0
        skip := {}
        freshStart := false
        tie := false }
  -- The trailing boundary of a final frame has already closed its page; a
  -- document is never given an empty page for it.
  if !b.cur.lines.isEmpty || !b.cur.fills.isEmpty || b.pages.isEmpty then
    b := b.finishPage
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
  if doc.docClass != "slides" && doc.docClass != "card" && doc.page.measureChecked
      && prose ≥ 4 then
    let alphabet := (List.range 26).foldl (fun acc k =>
      acc + scaledAt geom.fontSize font (font.advance (Char.ofNat ('a'.toNat + k)))) 0
    if alphabet > 0 then
      let l45 := 1415 * alphabet / 1000 + 2303 * spPerPt / 100
      let l65 := 2042 * alphabet / 1000 + 3341 * spPerPt / 100
      let cpl10 := 450 + 200 * (geom.textWidth - l45) / (l65 - l45)
      if cpl10 < 450 || cpl10 > 900 then
        let dir := if cpl10 > 900 then "narrow" else "widen"
        b := { b with diags := b.diags.push (Diag.of .W0201
          (s!"the measure holds about {(cpl10 + 5) / 10} characters " ++
            "per line, outside the readable 45\u201390 band")
          (help := s!"{dir} the text block (\\page\{ hmargin = ... }; 66 characters " ++
            "is the ideal) or declare \\page{ measure = free }")) }
  let pages := b.pages
  -- Running content is laid out per page once the count is known, into the
  -- margin, so it never disturbs the body it annotates.
  let total := pages.size
  let runLine (content : Array Inline) (n : Nat) (y size : Sp) (baseStyle : TextStyle)
      (cache : _) :
      Option LineOut × Array Diag × _ :=
    let sub := substPage n total content
    let (items, ds, cache, _) :=
      itemsOfInlines pats size xHeight fs baseStyle sub cache imgs
        geom.textWidth geom.textHeight
    let target := geom.textWidth
    let breaks := kp items target
    -- A running line is one line by construction — the band reserves one
    -- ascent (`footBandFor`). Content that wraps would silently lose every
    -- line but its first, so losing it is a named diagnostic instead.
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
      itemsOfInlines pats size xHeight fs baseStyle sub cache imgs
        geom.textWidth geom.textHeight
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
  let headY := geom.vmargin / 2 + b0.ascent
  let footY := geom.pageH - geom.vmargin / 2
  let mutedC := design.muted
  let mut out := pages
  let mut diags := b.diags
  let mut cache := acc.hyphCache
  -- The logo: the preamble `\logo` is the initial state, and a `\logo`
  -- block in the body changes it for the pages from that point on — an
  -- empty one clears it, which is how a deck scopes a logo to one frame
  -- (`\logo{...}` before it, `\logo{}` after). One line per state, laid
  -- out once — a logo names no page number — and placed at the lower-right
  -- corner, its right edge on the margin, its box standing on the bottom
  -- margin line.
  let mkLogoLine (content : Array Inline) (cache0 : Std.HashMap String (List Nat)) :
      Option LineOut × Array Diag × Std.HashMap String (List Nat) :=
    let (items, ds, c, _) :=
      itemsOfInlines pats geom.fontSize xHeight fs {} content cache0 imgs
        geom.textWidth geom.textHeight
    let breaks := kp items geom.textWidth
    match breaks[0]? with
    | none => (none, ds, c)
    | some brk =>
      let (segs, w, _) := setLine items (lineStart items 0) brk geom.textWidth false
      (some { x := geom.pageW - geom.hmargin - w
              y := geom.pageH - geom.vmargin
              size := geom.fontSize, segs := segs, setWidth := w }, ds, c)
  for i in [0:out.size] do
    let mut lines := out[i]!.lines
    -- Pages before `runningFrom` carry no running content: an opening page
    -- reads as a title page, not as page one of a run. The gate is the
    -- physical-page model's (`\runninghead[from = 2]`), so it governs only
    -- the physical furniture — head, foot, logo. The chrome footer is
    -- frame furniture on the frame model: whether a page carries it is
    -- decided by its frame's number, and a physical declaration must not
    -- silently gate it.
    let running := doc.runningFrom ≤ i + 1
    if running then
      if let some content := doc.head then
        let (l?, ds, c) := runLine content (i + 1) headY geom.fontSize {} cache
        diags := diags ++ ds
        cache := c
        if let some l := l? then lines := #[l] ++ lines
      if let some content := doc.foot then
        let (l?, ds, c) := runLine content (i + 1) footY geom.fontSize {} cache
        diags := diags ++ ds
        cache := c
        if let some l := l? then lines := lines.push l
    -- The chrome footer the page's frame gave it, slot by slot: the muted
    -- key at the scale's small step, both from declarations. Positions are
    -- fixed (`bandSlotX`); when two boxes collide the lower-rank slot
    -- yields — painted first, so every higher slot paints over it — and the
    -- yield is reported by name (W0333). No box moves: yielding is by ink,
    -- never by position.
    if let some band := out[i]!.foot then
      let mut placed : Array (Ir.BandSlot × LineOut) := #[]
      for slot in band do
        let (l?, ds, c) := slotLine slot.side slot.content (i + 1) footY
          footSize { color := mutedC } cache
        diags := diags ++ ds
        cache := c
        if let some l := l? then placed := placed.push (slot, l)
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
    let logoContent := logoSpans.foldl
      (fun acc (span : Nat × Array Inline) => if span.1 ≤ i then some span.2 else acc)
      doc.logo
    if running then
      if let some content := logoContent then
        unless content.isEmpty do
          let (l?, ds, c) := mkLogoLine content cache
          diags := diags ++ ds
          cache := c
          if let some l := l? then lines := lines.push l
    out := out.set! i { out[i]! with lines := lines }
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
  { pages := out, diags := unique }

end LeanTex.Core.Layout
