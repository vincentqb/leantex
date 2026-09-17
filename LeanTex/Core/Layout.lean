import Std.Data.HashSet
import LeanTex.Core.Dim
import LeanTex.Core.Font
import LeanTex.Core.Hyphen
import LeanTex.Core.Ir
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
  deriving Repr

def Geom.textWidth (g : Geom) : Sp := g.pageW - 2 * g.hmargin

/-- TeX's `\lineskip`: the least space between a line's depth and the next
line's height when the leading cannot hold them apart. Also the least
clearance between the body's ink and a footer's. -/
def lineskip : Sp := pt 1

/-- The lowest y a body line's ink may reach: the bottom margin, less the
band a footer reserves. Every placement decision reads the page bottom from
here and nowhere else — a footer that draws over the last line of body text
is a worse bug than no footer. -/
def Geom.bodyBottom (g : Geom) : Sp := g.pageH - g.vmargin - g.footBand

/-- The band a footer of ink height `ascent` reserves: its baseline sits
`vmargin/2` below the body area, so whatever of `ascent + lineskip` the half
margin cannot hold comes out of the body. -/
def footBandFor (vmargin ascent : Sp) : Sp := max 0 (ascent + lineskip - vmargin / 2)

/-- The reservation is sufficient, for every geometry: with the band from
`footBandFor`, body ink stops at least `lineskip` above the footer's ink top
(`footY - ascent`, the baseline at half the bottom margin less what the
footer reaches above it). The key inequality is proved over bare `Int`
binders because `omega` does not see through the `Sp` abbreviation. -/
theorem bodyBottom_clears_footer (g : Geom) (ascent : Sp) (hm : 0 ≤ g.vmargin)
    (h : g.footBand = footBandFor g.vmargin ascent) :
    g.bodyBottom + ascent + lineskip ≤ g.pageH - g.vmargin / 2 := by
  have key : ∀ pageH m a l : Int, 0 ≤ m →
      pageH - m - max 0 (a + l - m / 2) + a + l ≤ pageH - m / 2 := by
    intro pageH m a l hm
    simp only [Int.max_def]
    split <;> omega
  simp only [Geom.bodyBottom, footBandFor] at h ⊢
  rw [h]
  exact key g.pageH g.vmargin ascent lineskip hm

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

/-- Baseline distance for a size: 6⁄5 of it, scaled by the page's `leading`
factor (`\linespread`'s home). The 1.2 is the routine text setting — 10/12 of
Bringhurst's "settings such as 9/11, 10/12, 11/13 and 12/15 are routine;
longer measures need more lead than short ones" (Elements §2.2.1) — and the
factor is where a document declares the extra lead a wide measure wants; the
engine never raises it silently. -/
def leadingFor (size : Sp) (factor : Nat := 1000) : Sp := size * 6 / 5 * factor / 1000

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
      (glyphs : Array (Nat × Char × Sp)) (size : Sp) (underline : Bool)
  | glue (g : Glue)
  | pen (w : Sp) (cost : Int) (flagged : Bool) (fontIdx : Nat) (color : Ir.Color)
      (glyphs : Array (Nat × Char × Sp))
  deriving Repr, Inhabited

def forcedCost : Int := -10000

def hyphenPenalty : Int := 50

inductive Seg where
  /-- A glyph run. `width` is carried so link rectangles and alignment can be
  computed without re-measuring against the font. -/
  | run (fontIdx : Nat) (color : Ir.Color) (link : Option String) (width : Sp)
      (glyphs : Array (Nat × Char)) (size : Sp) (underline : Bool)
  | gap (w : Sp)
  /-- A horizontal rule, `w` wide and `thickness` thick, on the baseline plus
  `raise`. The heading rule of a designed section, filling its line. -/
  | rule (w : Sp) (thickness : Sp) (raise : Sp) (color : Ir.Color)
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
  frame's own number, the section in force): inline content the final pass
  lays into the margin once the page count is known. `none` on section
  pages, standout frames, and every page of an unthemed document. -/
  foot : Option (Array Inline) := none
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
  deriving Repr

private structure FlattenSt where
  toks : Array Tk := #[]
  warnedMath : Bool := false
  diags : Array Diag := #[]

private def warn (st : FlattenSt) (code msg : String) : FlattenSt :=
  { st with diags := st.diags.push { severity := .warning, code := code, message := msg } }

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

private def flatten (st : FlattenSt) (sty : TextStyle) (xs : Array Inline) : FlattenSt :=
  flattenList st sty xs.toList

private def flattenList (st : FlattenSt) (sty : TextStyle) (xs : List Inline) : FlattenSt :=
  match xs with
  | [] => st
  | x :: rest => flattenList (flattenOne st sty x) sty rest

private def flattenOne (st : FlattenSt) (sty : TextStyle) (x : Inline) : FlattenSt :=
  match x with
  | .text s => pushText st sty s
  | .linebreak extra => { st with toks := st.toks.push (.brk extra) }
  | .fill => { st with toks := st.toks.push .fill }
  | .math _ src =>
    let st := if st.warnedMath then st
      else { warn st "W0003" "math is typeset as plain text until M6" with warnedMath := true }
    pushText st sty src
  | .styled s body => flatten st (applyStyle sty s) body
  | .colored c _ body => flatten st { sty with color := c } body
  -- The underline is the link's affordance in both backends (the HTML
  -- anchor keeps the browser's): never colour alone, and never nothing
  -- (WCAG 2.2 SC 1.4.1, use of colour).
  | .link url body => flatten st { sty with link := some url, underline := true } body
  | .underline body => flatten st { sty with underline := true } body
  -- A step is pure grouping here: the PDF path dims pending content by
  -- recolouring copies before layout (`run`'s step driver), never by metrics.
  | .step _ _ body => flatten st sty body
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
    if box.isEmpty then items else items.push (.box w fontIdx color link box size underline)
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
              items := items.push (.box g.2.2 fb color link #[g] size underline)
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
          items := items.push (.box (size * num / den) fontIdx color link #[] size underline)
          i := i + 1
        | none =>
        if c == '\u00a0' then
          -- A no-break space is an interword space that is not glue.
          items := flush items box boxW
          box := #[]
          boxW := 0
          items := items.push
            (.box (scaledAt size font (font.advance ' ')) fontIdx color link #[] size underline)
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
            items := items.push (.box g.2.2 fb color link #[g] size underline)
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
    | other => other

-- The document's scalars, for the driver's per-glyph fallback ------------------

mutual

private def scalarTextList (out : Array String) (itemD enumD : Nat) :
    List Block → Array String
  | [] => out
  | b :: rest => scalarTextList (scalarTextOne out itemD enumD b) itemD enumD rest

private def scalarTextOne (out : Array String) (itemD enumD : Nat) :
    Block → Array String
  | .para xs => out.push (Ir.plainText xs)
  | .section _ _ title => out.push (Ir.plainText title)
  | .list ordered items =>
    -- The level's default marker rides along, so the fallback face is
    -- found before layout asks for the glyph. Per-kind depth, as LaTeX
    -- counts it (`\@itemdepth`/`\@enumdepth`).
    let (itemD, enumD) := if ordered then (itemD, enumD + 1) else (itemD + 1, enumD)
    let level := min (if ordered then enumD else itemD) 4
    scalarTextItems (out.push (ListMark.scalars ordered level)) itemD enumD items.toList
  | .center body => scalarTextList out itemD enumD body.toList
  | .spaced _ body => scalarTextList out itemD enumD body.toList
  | .columns cols => scalarTextCols out itemD enumD cols.toList
  | .step _ _ body => scalarTextList out itemD enumD body.toList
  -- A note is never set in either backend's pages; its glyphs are not asked
  -- for.
  | .note _ => out
  | .verbatim _ s => out.push s
  -- A rule has no glyphs.
  | .rule _ _ _ => out
  | .frame title _ _ body =>
    scalarTextList (out.push (Ir.plainText title)) itemD enumD body.toList
  -- A framefoot note is set on the page as footer text.
  | .framefoot content => out.push (Ir.plainText content)

private def scalarTextCols (out : Array String) (itemD enumD : Nat) :
    List (Option Nat × Array Block) → Array String
  | [] => out
  | (_, body) :: rest =>
    scalarTextCols (scalarTextList out itemD enumD body.toList) itemD enumD rest

private def scalarTextItems (out : Array String) (itemD enumD : Nat) :
    List (Array Block) → Array String
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
def docScalars (doc : Doc) : Array Char := Id.run do
  let mut texts : Array String := scalarTextList #[] 0 0 doc.body.toList
  if let some h := doc.head then
    texts := (texts.push (Ir.plainText h)).push "0123456789"
  if let some f := doc.foot then
    texts := (texts.push (Ir.plainText f)).push "0123456789"
  for (_, st) in doc.styles.entries do
    if let some tpl := st.font then
      texts := texts.push (Ir.plainText tpl)
    if let some m := st.marker then
      texts := texts.push (Ir.plainText m)
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

/-- Flatten inlines into Knuth-Plass items. The fourth component maps the
index of a forced-break penalty to extra vertical space the document asked for
there (`\\[1ex]`); it rides beside the items because the line breaker has no
use for it, and putting it in `Item` would make every pattern carry a field
only the page builder reads. -/
private def itemsOfInlines (pats : Option Hyphen.Patterns) (size xHeight : Sp)
    (fs : FontSet) (baseStyle : TextStyle) (xs : Array Inline)
    (cache : Std.HashMap String (List Nat)) :
    Array Item × Array Diag × Std.HashMap String (List Nat) ×
      Std.HashMap Nat Sp := Id.run do
  let st := flatten {} baseStyle xs
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
    | .space sty =>
      let idx := fs.lookup sty.slot sty.bold sty.italic
      items := items.push (.glue (interword (size * sty.scale / 1000) (fs.get idx)))
    | .fill =>
      -- Stretchable but not a legal breakpoint on its own.
      items := items.push (.glue { fil := true })
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
    diags := diags.push {
      severity := .warning
      code := "W0004"
      message :=
        s!"'{(fs.get idx).family}' has no glyph for '{c}' (U+{hex c.toNat}); dropped"
    }
  for (idx, c, fb) in substs do
    diags := diags.push {
      severity := .warning
      code := "W0009"
      message := s!"'{(fs.get idx).family}' has no glyph for '{c}' \
        (U+{hex c.toNat}); set from '{(fs.get fb).family}'"
    }
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
    | some (.box _ _ _ _ _ _ _) => j > 0
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
    | .box w _ _ _ _ _ _ => m := { m with natural := m.natural + w }
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
      | .box w _ _ _ _ _ _ => (w, 0, 0, 0)
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
    | .box w fontIdx color link glyphs size underline =>
      -- The declared width is authoritative, as it already is in `measure`: a
      -- kern is a box with a width and no glyphs, and recomputing from the
      -- advances would silently set it to zero.
      segs := segs.push
        (.run fontIdx color link w (glyphs.map fun (g, c, _) => (g, c)) size underline)
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
        | .run _ _ _ _ _ sz ul => (if sz != 0 then sz else acc.1, ul)
        | _ => acc) ((0 : Sp), false)
      segs := segs.push
        (.run fontIdx color none w (glyphs.map fun (g, c, _) => (g, c)) inherited inheritedUl)
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
  /-- The chrome footer for pages closed from here on, from `.foot` ops. -/
  curFoot : Option (Array Inline) := none
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
  let diags := if b.needed > 0 then b.diags.push {
      severity := .note
      code := "N0200"
      message := s!"page {b.pages.size + 1} set {b.needed / 65536}pt short: its skips gave " ++
        s!"{b.needed * 100 / b.pageShrink}% of their {b.pageShrink / 65536}pt of shrink"
    } else b.diags
  -- The leftover between the content's bottom and the bottom margin,
  -- split by the page's declared ratio (`VDist`). Only what follows the
  -- `.pin` mark moves: the frame title and its bar are page-top chrome,
  -- and beamer distributes the body below the frametitle, never the
  -- frametitle itself. The page's fills ride with their lines.
  let delta := if lines.size > b.pinnedLines then
      let lastY := lines.foldl (fun m l => max m l.y) 0
      b.vdist.aboveShare (b.geom.bodyBottom - (lastY + b.prevDepth))
    else 0
  let lines := if delta == 0 then lines else
    lines.mapIdx fun i l => if i < b.pinnedLines then l else { l with y := l.y + delta }
  let fills := if delta == 0 then b.cur.fills else
    b.cur.fills.mapIdx fun i f => if i < b.pinnedFills then f else { f with y := f.y + delta }
  let fills := match b.pageBg.orElse (fun _ => b.docBg) with
    | some c => #[({ x := 0, y := 0, w := b.geom.pageW, h := b.geom.pageH,
                     color := c } : Fill)] ++ fills
    | none => fills
  { b with pages := b.pages.push { lines := lines, fills := fills, foot := b.curFoot },
           cur := {},
           shrinkAbove := #[], pageShrink := 0, needed := 0, skip := {},
           pageBg := none, vdist := .top, pinnedLines := 0, pinnedFills := 0,
           diags := diags }

/-- A line that shares its baseline with the last one (underline rules)
rides with it, including its share of the page's shrink. -/
private def B.pushSibling (b : B) (l : LineOut) : B :=
  { b with cur := { b.cur with lines := b.cur.lines.push l },
           shrinkAbove := b.shrinkAbove.push (b.shrinkAbove.back?.getD 0) }

private def B.commit (b : B) (line : LineOut) (depth above overflow : Sp) : B :=
  { b with cur := { b.cur with lines := b.cur.lines.push line }
           shrinkAbove := b.shrinkAbove.push above
           pageShrink := above
           needed := max b.needed overflow
           y := line.y
           freshStart := false
           prevDepth := depth
           skip := {} }

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
    | .run idx _ _ _ _ sz _ =>
      let font := fs.get idx
      let sz := if sz == 0 then nominal else sz
      (max acc.1 sz, max acc.2.1 (scaledAt sz font font.capHeight.toNat),
       max acc.2.2 (scaledAt sz font (-font.descent).toNat))
    | _ => acc) (nominal, b.capHeight * nominal / b.geom.fontSize,
                 b.descent * nominal / b.geom.fontSize)
  let bottom := b.geom.bodyBottom
  let mk (y : Sp) : LineOut := { x := x, y := y, size := size, segs := segs, setWidth := w }
  let firstY := b.geom.vmargin + max b.ascent height
  if b.cur.lines.isEmpty || b.freshStart then
    b.commit (mk firstY) depth 0 0
  else
    let interline := max (leadingFor tallest b.geom.leading) (b.prevDepth + height + lineskip)
    let y := b.y + b.skip.width + interline
    let overflow := y + depth - bottom
    let above := b.pageShrink + b.skip.shrink
    if overflow ≤ above then
      b.commit (mk y) depth above overflow
    else
      let b := b.finishPage
      b.commit (mk firstY) depth 0 0

private def B.warnOverfull (b : B) : B :=
  { b with diags := b.diags.push {
    severity := .warning
    code := "W0005"
    message := "overfull line (no feasible break)"
  } }

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
  | foot (content : Option (Array Inline))

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
  /-- Frames seen so far / in the whole document: a section page's progress
  bar is the deck position. -/
  framesSeen : Nat := 0
  framesTotal : Nat := 0
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
discards glue at the top of a new one. -/
private def Acc.pageBreak (a : Acc) : Acc :=
  { a with ops := a.ops.push .brk, wantDefault := false, owed := #[] }

private def Acc.style (a : Acc) (element : String) : Ir.ElementStyle :=
  (a.styles.find? element).getD {}

/-- The chrome footer a frame's pages carry: each slot resolved to its
per-page datum — the section in force, the frame's own number — with a fill
pushing the two apart. A `\framefoot` note in force takes the left slot.
`none` when nothing is declared. -/
private def Acc.chromeFoot (a : Acc) : Option (Array Inline) :=
  if a.chromeL.isNone && a.chromeR.isNone && a.frameFoot.isNone then none else
  let slot (s : Ir.ChromeSlot) : Array Inline :=
    match s with
    | .sectionTitle => a.curSection
    | .frameNumber => #[.text (toString a.framesSeen)]
  let left := match a.frameFoot with
    | some xs => xs
    | none => (a.chromeL.map slot).getD #[]
  some (left ++ #[Ir.Inline.fill] ++ ((a.chromeR.map slot).getD #[]))

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
    itemsOfInlines pats size a.xHeight fs baseStyle inlines a.hyphCache
  let items := if a.geom.justify then items else raggedItems items
  -- A marker is content: set as a line of its own, unjustified, so it can
  -- carry any style the document gave it. Its diagnostics ride with the
  -- paragraph's — a marker glyph no face covers must warn, not vanish.
  let (markerSegs, ds, cache) := match marker with
    | some m =>
      let (mi, mds, cache, _) :=
        itemsOfInlines pats size a.xHeight fs { color := a.fg } m cache
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

def sectionSize (geom : Geom) : Nat → Sp
  | 1 => pt 14
  | 2 => pt 12
  | _ => geom.fontSize

/-- Display type: headings, frame titles, section-page and standout text.
Display is not body text and is never hyphenated (Butterick, Practical
Typography, "Hyphenation": suppress automatic hyphenation where lines are
short — headings foremost — because a break there costs more than it
saves). The door takes no patterns at all, so no heading path can
hyphenate by construction — the invariant is the signature. -/
private def collectDisplay (a : Acc) (fs : FontSet)
    (inlines : Array Inline) (indent : Sp) (center : Bool) (size : Sp)
    (baseStyle : TextStyle := {})
    (rule : Option (Sp × Ir.Color) := none) : Acc :=
  collectPara a none fs inlines indent center size (baseStyle := baseStyle)
    (rule := rule)

-- Block walk. Mutual recursion through `List` so the nested calls are
-- structural: no `partial`, and the shape mirrors the IR.
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
      let thick := ((a.tokens.find? "progressheight").map
        fun g => (a.resolve g).width).getD (pt 1)
      let a := { a with ops := a.ops.push (.progress
        (min a.framesSeen a.framesTotal) (max a.framesTotal 1) fgC bgC thick
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
          (rule := st.rule.map fun (r : Ir.Color × Option String) => (pt 6 / 10, r.1))
      | none =>
        collectDisplay a fs title indent false (sectionSize a.geom level)
          (baseStyle := { bold := true })
          (rule := st.rule.map fun (r : Ir.Color × Option String) => (pt 6 / 10, r.1))
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
    let a := if depth > 4 then { a with diags := a.diags.push {
        severity := .warning
        code := "W0010"
        message := s!"lists nest four levels; level {depth} reuses the fourth's marker"
        help := "LaTeX errors here (\"Too deeply nested\"); flatten the nesting" } }
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
  | .note _ =>
    -- A speaker note is not handout content: no lines, no gap.
    a
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
  | .frame title standout valign body =>
    -- A frame is a page boundary, not an article paragraph. Content past
    -- the page bottom spills to a continuation page — best effort, never
    -- clipped. `framesSeen` is counted by `run`'s top-level driver, once
    -- per logical frame, so a stepped frame's pages share it.
    let a := a.pageBreak
    -- The footer belongs to the frame: its pages, spill pages included,
    -- carry the frame's own number; a standout frame carries none (its
    -- inverted page has no pairing for the muted key).
    let a := if a.footAllowed then
        { a with ops := a.ops.push (.foot (if standout then none else a.chromeFoot)) }
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
    -- and everything on it is display furniture: titles never hyphenate.
    let pats := if valign matches .golden then none else pats
    let a := collectBlocks a pats fs body indent
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
      | .run _ _ _ _ _ _ true => true
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
    | .run fontIdx _ _ w glyphs size _ =>
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
    | .run fontIdx color _ w _ size underline =>
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
      let sep := geom.fontSize * 2 / 5
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
  | .link u body => .link u (substPageList n total body.toList).toArray
  | .underline body => .underline (substPageList n total body.toList).toArray
  | .step s last body => .step s last (substPageList n total body.toList).toArray
  | other => other

def substPageList (n total : Nat) : List Inline → List Inline
  | [] => []
  | x :: rest => substPageOne n total x :: substPageList n total rest

end

/-- One op staged for placement: paragraphs carry their breaking task. -/
private inductive StagedOp where
  | skip (g : Glue)
  | brk
  | pageStyle (bg : Option Ir.Color) (vdist : VDist)
  | titleBar (color : Ir.Color) (pad : Sp)
  | hrule (color : Ir.Color) (thickness : Sp)
  | pin
  | progress (num den : Nat) (fg bg : Ir.Color) (thick x w : Sp)
  | foot (content : Option (Array Inline))
  | para (j : ParaJob) (t : Task (Array Nat))
  | colOpen
  | colNext
  | colClose

/-- Placement state saved at a `colOpen`, restored per column: where the
columns start, and the lowest bottom any column reached so far. -/
private structure ColSave where
  y : Sp
  prevDepth : Sp
  skip : Glue
  fresh : Bool
  bottomY : Sp
  bottomDepth : Sp

/-- Typeset a document body into positioned pages. Geometry is resolved by
the caller via `Geom.ofPage`, so layout has one source of truth. -/
def run (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns) (doc : Doc) :
    Out := Id.run do
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
  let xHeight := scale font.xHeight
  let framesTotal := doc.body.foldl (fun n b => match b with
    | .frame _ _ _ _ => n + 1 | _ => n) 0
  let dim := (doc.palette.find? "covered").getD Ir.coveredDefault
  let acc0 : Acc := { geom := geom, xHeight := xHeight, styles := doc.styles
                      slides := doc.docClass == "slides"
                      pal := doc.palette
                      tokens := doc.tokens
                      framesTotal := framesTotal
                      chromeL := if footAllowed then doc.chrome.footerLeft else none
                      chromeR := if footAllowed then doc.chrome.footerRight else none
                      footAllowed := footAllowed
                      fg := (doc.palette.find? "fg").getD Ir.Color.black }
  -- One handout page per overlay step, driven here at the top level: a
  -- multi-step frame collects once per step with pending content dimmed
  -- (`Ir.dimBlocks`), under ONE `framesSeen` — the furniture belongs to the
  -- frame, not the step, so a stepped frame's pages share their progress
  -- position and their frame count. Steps and standout are orthogonal: the
  -- flag rides onto every step page unchanged.
  let mut acc := acc0
  let mut firstBlk := true
  for blk in doc.body do
    acc := if firstBlk then acc else acc.wantGap
    firstBlk := false
    match blk with
    | .frame title standout valign body =>
      acc := { acc with framesSeen := acc.framesSeen + 1 }
      let steps := Ir.maxStepBlocks body
      if steps ≤ 1 then
        acc := collectBlock acc pats fs
          (.frame title standout valign (Ir.unwrapItemSteps body)) 0
      else
        for k in [1:steps + 1] do
          acc := collectBlock acc pats fs
            (.frame title standout valign (Ir.unwrapItemSteps (Ir.dimBlocks dim k body))) 0
    | other => acc := collectBlock acc pats fs (Ir.unwrapItemStep other) 0
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
    | .pin => .pin
    | .progress num den fg bg thick x w => .progress num den fg bg thick x w
    | .foot c => .foot c
    | .para j => .para j (Task.spawn fun _ => kp j.items j.target)
    | .colOpen => .colOpen
    | .colNext => .colNext
    | .colClose => .colClose
  let b0 : B := {
    geom := geom
    ascent := scale font.ascent
    descent := scale (-font.descent)
    capHeight := scale font.capHeight
    xHeight := xHeight
    docBg := doc.palette.find? "bg"
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
          b := { b with diags := b.diags.push {
            severity := .warning
            code := "W0202"
            message := s!"'{element}' sets more space below the heading " ++
              s!"({down.toPtString}pt) than above it ({up.toPtString}pt)"
            help := s!"a heading binds to the text it introduces: in " ++
              s!"\\style\{{element}}\{...} keep 'after' at most 'before'" } }
  let mut colSaves : Array ColSave := #[]
  for s in staged do
    match s with
    | .skip g => b := { b with skip := b.skip.add g }
    | .brk =>
      -- A boundary closes a page only when the page holds something: two
      -- adjacent frames share one boundary, not an empty page. A style set
      -- for a page that never got content dies with the boundary.
      if !b.cur.lines.isEmpty then
        b := b.finishPage
      else
        b := { b with pageBg := none, vdist := .top, pinnedLines := 0, pinnedFills := 0 }
    | .pageStyle bg d => b := { b with pageBg := bg, vdist := d }
    | .foot c => b := { b with curFoot := c }
    | .pin =>
      b := { b with pinnedLines := b.cur.lines.size, pinnedFills := b.cur.fills.size }
    | .colOpen =>
      colSaves := colSaves.push {
        y := b.y, prevDepth := b.prevDepth, skip := b.skip
        fresh := b.cur.lines.isEmpty || b.freshStart
        bottomY := b.y, bottomDepth := b.prevDepth }
    | .colNext =>
      if let some save := colSaves.back? then
        let save := if b.y > save.bottomY
          then { save with bottomY := b.y, bottomDepth := b.prevDepth }
          else save
        colSaves := colSaves.pop.push save
        b := { b with y := save.y, prevDepth := save.prevDepth, skip := save.skip
                      freshStart := save.fresh }
    | .colClose =>
      if let some save := colSaves.back? then
        colSaves := colSaves.pop
        let (bottomY, bottomDepth) := if b.y > save.bottomY
          then (b.y, b.prevDepth) else (save.bottomY, save.bottomDepth)
        b := { b with y := bottomY, prevDepth := bottomDepth, skip := {}
                      freshStart := false }
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
  -- The trailing boundary of a final frame has already closed its page; a
  -- document is never given an empty page for it.
  if !b.cur.lines.isEmpty || b.pages.isEmpty then
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
        b := { b with diags := b.diags.push {
          severity := .warning
          code := "W0201"
          message := s!"the measure holds about {(cpl10 + 5) / 10} characters " ++
            "per line, outside the readable 45\u201390 band"
          help := s!"{dir} the text block (\\page\{ hmargin = ... }; 66 characters " ++
            "is the ideal) or declare \\page{ measure = free }" } }
  let pages := b.pages
  -- Running content is laid out per page once the count is known, into the
  -- margin, so it never disturbs the body it annotates.
  let total := pages.size
  let runLine (content : Array Inline) (n : Nat) (y size : Sp) (baseStyle : TextStyle)
      (cache : _) :
      Option LineOut × Array Diag × _ :=
    let sub := substPage n total content
    let (items, ds, cache, _) :=
      itemsOfInlines pats size xHeight fs baseStyle sub cache
    let target := geom.textWidth
    let breaks := kp items target
    match breaks[0]? with
    | none => (none, ds, cache)
    | some brk =>
      let (segs, w, _) := setLine items (lineStart items 0) brk target true
      (some { x := geom.hmargin, y := y, size := size, segs := segs,
              setWidth := w }, ds, cache)
  let headY := geom.vmargin / 2 + b0.ascent
  let footY := geom.pageH - geom.vmargin / 2
  let mutedC := (doc.palette.find? "muted").getD
    ((doc.palette.find? "fg").getD Ir.Color.black)
  let mut out := pages
  let mut diags := b.diags
  let mut cache := acc.hyphCache
  for i in [0:out.size] do
    let mut lines := out[i]!.lines
    -- Pages before `runningFrom` carry no furniture: an opening page reads
    -- as a title page, not as page one of a run.
    if i + 1 < doc.runningFrom then continue
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
    -- The chrome footer the page's frame gave it: the muted key at the
    -- scale's small step, both from declarations, neither from a backend.
    if let some content := out[i]!.foot then
      let (l?, ds, c) := runLine content (i + 1) footY footSize
        { color := mutedC } cache
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
