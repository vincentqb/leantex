import LeanTex.Core.Dim
import LeanTex.Core.Font
import LeanTex.Core.Hyphen
import LeanTex.Core.Ir
import LeanTex.Core.Diag

namespace LeanTex.Core.Layout

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font LeanTex.Core.Ir

structure Geom where
  pageW : Sp := pt 612
  pageH : Sp := pt 792
  hmargin : Sp := inch 1
  vmargin : Sp := inch 1
  fontSize : Sp := pt 10
  parskip : Sp := pt 6
  listIndent : Sp := pt 15
  leading : Nat := 1000
  deriving Repr

def Geom.textWidth (g : Geom) : Sp := g.pageW - 2 * g.hmargin

/-- Resolve a document's `\page` declaration into layout geometry. One source
of truth: layout reads geometry only from here. -/
def Geom.ofPage (spec : Ir.PageSpec) (base : Geom := {}) : Geom :=
  { base with
    pageW := spec.width
    pageH := spec.height
    hmargin := spec.hmargin
    vmargin := spec.vmargin
    leading := spec.leading }

def leadingFor (size : Sp) (factor : Nat := 1000) : Sp := size * 6 / 5 * factor / 1000

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

structure PageOut where
  lines : Array LineOut := #[]
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
      else { warn st "W0003" "math is typeset as plain text until M4" with warnedMath := true }
    pushText st sty src
  | .styled s body => flatten st (applyStyle sty s) body
  | .colored c _ body => flatten st { sty with color := c } body
  | .link url body => flatten st { sty with link := some url } body
  | .underline body => flatten st { sty with underline := true } body
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

def bulletGlyphs (size : Sp) (font : Font) : Array (Nat × Char × Sp) :=
  match glyphOf size font '–' with
  | some g => #[g]
  | none => hyphenGlyph size font

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
carrying the hyphen glyph) and by explicit hyphens (unflagged, no glyph). -/
private def wordItems (pats : Option Hyphen.Patterns) (size : Sp) (fontIdx : Nat)
    (color : Ir.Color) (link : Option String) (underline : Bool)
    (font : Font) (chars : Array Char) (missing : Array Char)
    (cache : Std.HashMap String (List Nat)) :
    Array Item × Array Char × Std.HashMap String (List Nat) := Id.run do
  let mut missing := missing
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
            unless missing.contains c' do
              missing := missing.push c'
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
          unless missing.contains c do
            missing := missing.push c
        i := i + 1
        if c == '-' then
          items := flush items box boxW
          box := #[]
          boxW := 0
          items := items.push (.pen 0 hyphenPenalty false fontIdx color #[])
    else
      break
  items := flush items box boxW
  return (items, missing, cache)

private def interword (size : Sp) (font : Font) : Glue :=
  let w := scaledAt size font (font.advance ' ')
  { width := w, stretch := w / 2, shrink := w / 3 }

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
  let mut missing : Array Char := #[]
  let mut extras : Std.HashMap Nat Sp := {}
  let mut cache := cache
  for tk in st.toks do
    match tk with
    | .word sty chars =>
      let idx := fs.lookup sty.slot sty.bold sty.italic
      let sz := size * sty.scale / 1000
      let (ws, m, c') :=
        wordItems pats sz idx sty.color sty.link sty.underline (fs.get idx) chars missing cache
      missing := m
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
  for c in missing do
    diags := diags.push {
      severity := .warning
      code := "W0004"
      message := s!"the font has no glyph for '{c}' (U+{hex c.toNat}); dropped"
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

/-- Optimal breakpoints by dynamic programming over break positions, with
prefix-sum line measures and an active list: a node whose line to the
current position is already overfull beyond shrink can only get worse, so
it is considered one last time and then deactivated (one node is always
retained so a solution exists even for unbreakable content). -/
def kp (items : Array Item) (target : Sp) : Array Nat := Id.run do
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
  let measureAt (a j : Nat) : Measure :=
    let penW : Sp := match items[j]? with
      | some (.pen w _ _ _ _ _) => w
      | _ => 0
    { natural := pw[j]! - pw[a]! + penW
      stretch := ps[j]! - ps[a]!
      shrink := pk[j]! - pk[a]!
      fil := pf[j]! - pf[a]! > 0 }
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
          let spansForced := a < j && pforced[j]! - pforced[a]! > 0
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

private structure B where
  geom : Geom
  ascent : Sp
  descent : Sp
  /-- Body x-height in sp, so `ex` tokens resolve against the real font. -/
  xHeight : Sp := 0
  pages : Array PageOut := #[]
  cur : PageOut := {}
  y : Sp := 0
  diags : Array Diag := #[]

private def B.freshY (b : B) : Sp := b.geom.vmargin + b.ascent

private def B.breakPage (b : B) : B :=
  { b with pages := b.pages.push b.cur, cur := {}, y := b.freshY }

/-- Place one line. Vertical space follows the tallest run on it, not the
paragraph's nominal size: a line carrying `\Huge` needs the extra height both
above its baseline and below it, or it collides with its neighbours. -/
private def B.placeLine (b : B) (x : Sp) (size : Sp) (segs : Array Seg) (w : Sp) : B :=
  let nominal := if size == 0 then b.geom.fontSize else size
  let tallest := segs.foldl (fun acc s => match s with
    | .run _ _ _ _ _ sz _ => max acc sz
    | _ => acc) nominal
  let b := if tallest > nominal then
      { b with y := b.y + b.ascent * (tallest - nominal) / nominal } else b
  let descent := b.descent * tallest / nominal
  let b := if b.y + descent > b.geom.pageH - b.geom.vmargin then b.breakPage else b
  let line : LineOut := { x := x, y := b.y, size := size, segs := segs, setWidth := w }
  { b with cur := { lines := b.cur.lines.push line },
           y := b.y + leadingFor tallest b.geom.leading }

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
  bullet : Option (Nat × Array (Nat × Char × Sp)) := none
  /-- Marker content set as its own items and placed before the first line. -/
  markerSegs : Option (Array Seg × Sp) := none
  /-- A rule filling the first line after the content. -/
  rule : Option (Sp × Ir.Color) := none

/-- The block walk emits vertical skips and paragraph jobs; placement replays
them in document order, so the page builder stays sequential and the output
does not depend on task scheduling. -/
private inductive Op where
  | skip (dy : Sp)
  | para (job : ParaJob)

private structure Acc where
  geom : Geom
  xHeight : Sp
  styles : Ir.Styles := {}
  /-- Space a heading asked for below itself; the next block takes it in
  place of `parskip`. -/
  pendingAfter : Option Sp := none
  ops : Array Op := #[]
  hyphCache : Std.HashMap String (List Nat) := {}

private def Acc.skip (a : Acc) (dy : Sp) : Acc :=
  { a with ops := a.ops.push (.skip dy) }

/-- The gap before a peer block: a heading's declared `after` if one is
pending, else `parskip`. -/
private def Acc.peerGap (a : Acc) : Acc :=
  match a.pendingAfter with
  | some dy => { a with ops := a.ops.push (.skip dy), pendingAfter := none }
  | none => a.skip a.geom.parskip

private def Acc.resolve (a : Acc) (g : SymGlue) : Sp :=
  g.width.resolve a.geom.fontSize a.xHeight

private def Acc.style (a : Acc) (element : String) : Ir.ElementStyle :=
  (a.styles.find? element).getD {}

private def collectPara (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (inlines : Array Inline) (indent : Sp) (center : Bool) (size : Sp)
    (baseStyle : TextStyle := {})
    (bullet : Option (Nat × Array (Nat × Char × Sp)) := none)
    (marker : Option (Array Inline) := none)
    (rule : Option (Sp × Ir.Color) := none) : Acc :=
  let (items, ds, cache, extras) :=
    itemsOfInlines pats size a.xHeight fs baseStyle inlines a.hyphCache
  -- A declared marker is content: set as a line of its own, unjustified, so
  -- it can carry any style the document gave it.
  let markerSegs := marker.map fun m =>
    let (mi, _, _, _) := itemsOfInlines pats size a.xHeight fs {} m cache
    let (segs, w, _) := setLine mi (lineStart mi 0) (mi.size - 1) a.geom.textWidth false
    (segs, w)
  { a with
    hyphCache := cache
    ops := a.ops.push (.para {
      items := items, extras := extras, diags := ds
      target := a.geom.textWidth - indent
      indent := indent, center := center, size := size, bullet := bullet
      markerSegs := markerSegs, rule := rule }) }

def sectionSize (geom : Geom) : Nat → Sp
  | 1 => pt 14
  | 2 => pt 12
  | _ => geom.fontSize

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
    let a := if first then a else a.peerGap
    let a := collectBlock a pats fs blk indent
    collectBlockList a pats fs rest indent false

/-- One list item: its leading paragraph carries the marker. -/
private def collectItem (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (item : List Block) (indent : Sp) (first : Bool) (st : Ir.ElementStyle) : Acc :=
  match item with
  | [] => a
  | blk :: rest =>
    let a := if first then a else a.skip a.geom.parskip
    let a := match blk, first with
      | .para content, true =>
        collectPara a pats fs content indent false a.geom.fontSize
          (bullet := some (0, bulletGlyphs a.geom.fontSize fs.body))
          (marker := st.marker)
      | _, _ => collectBlock a pats fs blk indent
    collectItem a pats fs rest indent false st

private def collectItems (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (items : List (Array Block)) (indent : Sp) (first : Bool) (st : Ir.ElementStyle) : Acc :=
  match items with
  | [] => a
  | item :: rest =>
    -- Items are peers separated by the declared gap. The default is none,
    -- as it was: a list is one block, and its leading is its rhythm.
    let a := match first, st.gap with
      | false, some g => a.skip (a.resolve g)
      | _, _ => a
    let a := collectItem a pats fs item.toList indent true st
    collectItems a pats fs rest indent false st

/-- Centered content: paragraphs center, anything else nests unchanged. -/
private def collectCentered (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (body : List Block) (indent : Sp) : Acc :=
  match body with
  | [] => a
  | blk :: rest =>
    let a := match blk with
      | .para content => collectPara a pats fs content indent true a.geom.fontSize
      | _ => collectBlock a pats fs blk indent
    collectCentered a pats fs rest indent

private def collectBlock (a : Acc) (pats : Option Hyphen.Patterns) (fs : FontSet)
    (blk : Block) (indent : Sp) : Acc :=
  match blk with
  | .para content =>
    collectPara a pats fs content indent false a.geom.fontSize
  | .section level _ title =>
    let element := match level with
      | 1 => "section" | 2 => "subsection" | _ => "subsubsection"
    let st := a.style element
    let a := a.skip ((st.before.map a.resolve).getD a.geom.parskip)
    -- A declared font template wraps the title; without one, headings set in
    -- the bold face of the body family at the level's size.
    let a := match st.font with
      | some tpl =>
        collectPara a pats fs (Ir.fillTemplate tpl title) indent false a.geom.fontSize
          (rule := st.rule.map fun (r : Ir.Color × Option String) => (pt 6 / 10, r.1))
      | none =>
        collectPara a pats fs title indent false (sectionSize a.geom level)
          (baseStyle := { bold := true })
          (rule := st.rule.map fun (r : Ir.Color × Option String) => (pt 6 / 10, r.1))
    { a with pendingAfter := st.after.map a.resolve }
  | .list ordered items =>
    let st := a.style (if ordered then "enumerate" else "itemize")
    let a := match st.before, a.ops.back? with
      | some g, some (.skip _) => { a with ops := a.ops.pop.push (.skip (a.resolve g)) }
      | some g, _ => a.skip (a.resolve g)
      | none, _ => a
    let indent := indent + (st.indent.map a.resolve).getD a.geom.listIndent
    collectItems a pats fs items.toList indent true st
  | .center body =>
    collectCentered a pats fs body.toList indent
  | .spaced before body =>
    -- Declared space above the block, resolved against the body font. It is
    -- the gap, not an addition to one: the peer gap already pushed is replaced,
    -- which is what `\vspace` between paragraphs means in LaTeX and what
    -- `\block[before = ...]` was designed to say.
    let g := before.resolve a.geom.fontSize a.xHeight
    let a := match a.ops.back? with
      | some (.skip _) => { a with ops := a.ops.pop.push (.skip g.width) }
      | _ => a.skip g.width
    collectBlocks a pats fs body indent

end

/-- Underline rules for one set line: a second walk over its segs, aligned by
gaps, so it can ride as its own `LineOut` at the same baseline — the PDF
writer's x-tracking stays linear and link rectangles see no extra runs. The
rule sits at the font's own `post` metrics (with a conventional fallback when
the font declares none) and is interrupted around any glyph that reaches
below its top edge, a gap of twice the thickness on each side. Empty when the
line has no underlined run, so the common case allocates nothing. -/
private def underlineSegs (fs : FontSet) (lineSize : Sp) (segs : Array Seg) :
    Array Seg := Id.run do
  unless segs.any (fun s => match s with
      | .run _ _ _ _ _ _ true => true
      | _ => false) do
    return #[]
  let mut out : Array Seg := #[]
  for seg in segs do
    match seg with
    | .gap w => out := out.push (.gap w)
    | .rule w _ _ _ => out := out.push (.gap w)
    | .run fontIdx color _ w glyphs size underline =>
      if !underline then
        out := out.push (.gap w)
      else
        let font := fs.get fontIdx
        let sz := if size == 0 then lineSize else size
        let top := if font.underlinePosition == 0 then -(sz / 10)
          else font.underlinePosition * sz / font.unitsPerEm
        let thick := if font.underlineThickness == 0 then sz / 20
          else font.underlineThickness * sz / font.unitsPerEm
        let raise := top - thick
        -- Skip intervals within [0, w], merged: descender glyphs plus the
        -- clearance either side.
        let mut skips : Array (Sp × Sp) := #[]
        let mut x : Sp := 0
        for (g, _) in glyphs do
          let adv := scaledAt sz font (font.widths[g]?.getD 0)
          if font.descends g then
            let lo := max 0 (x - 2 * thick)
            let hi := min w (x + adv + 2 * thick)
            match skips.back? with
            | some (plo, phi) =>
              if lo ≤ phi then skips := skips.pop.push (plo, max phi hi)
              else skips := skips.push (lo, hi)
            | none => skips := skips.push (lo, hi)
          x := x + adv
        let mut cur : Sp := 0
        for (lo, hi) in skips do
          if lo > cur then
            out := out.push (.rule (lo - cur) thick raise color)
          out := out.push (.gap (hi - max lo cur))
          cur := hi
        if w > cur then
          out := out.push (.rule (w - cur) thick raise color)
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
    let (segs, w, overfull) := setLine j.items a brk width (!j.center)
    if overfull then
      b := b.warnOverfull
    let mut x := if j.center then geom.hmargin + j.indent + (width - w) / 2
      else geom.hmargin + j.indent
    let mut segs := segs
    let mut w := w
    if first then
      let sep := geom.fontSize * 2 / 5
      match j.markerSegs, j.bullet with
      | some (ms, mw), _ =>
        segs := ms ++ #[Seg.gap sep] ++ segs
        x := x - mw - sep
        w := w + mw + sep
      | none, some (bulletFont, bg) =>
        let bw := bg.foldl (fun acc (_, _, adv) => acc + adv) 0
        segs := #[Seg.run bulletFont Ir.Color.black none bw
          (bg.map fun (g, c, _) => (g, c)) j.size false, Seg.gap sep] ++ segs
        x := x - bw - sep
        w := w + bw + sep
      | none, none => pure ()
      if let some (thickness, color) := j.rule then
        -- The rule fills what the heading left of its line, a word-space
        -- away from the text, sitting at half the x-height like a dash.
        let gap := j.size / 2
        let ruleW := width - w - gap
        if ruleW > 0 then
          segs := segs ++ #[Seg.gap gap, Seg.rule ruleW thickness (b.xHeight / 2) color]
          w := width
    b := b.placeLine x j.size segs w
    -- The line's underlines, as a sibling at the same baseline. Pushed after
    -- `placeLine` so a page break has already decided where the text landed;
    -- the rules land beside it, adding no vertical space.
    let uSegs := underlineSegs fs j.size segs
    unless uSegs.isEmpty do
      if let some last := b.cur.lines.back? then
        let uLine : LineOut :=
          { x := last.x, y := last.y, size := last.size, segs := uSegs, setWidth := 0 }
        b := { b with cur := { lines := b.cur.lines.push uLine } }
    if let some extra := j.extras[brk]? then
      b := { b with y := b.y + extra }
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
  | other => other

def substPageList (n total : Nat) : List Inline → List Inline
  | [] => []
  | x :: rest => substPageOne n total x :: substPageList n total rest

end

/-- Typeset a document body into positioned pages. Geometry is resolved by
the caller via `Geom.ofPage`, so layout has one source of truth. -/
def run (geom : Geom) (fs : FontSet) (pats : Option Hyphen.Patterns) (doc : Doc) :
    Out := Id.run do
  let font := fs.body
  let scale (u : Int) : Sp := u * geom.fontSize / font.unitsPerEm
  let xHeight := scale font.xHeight
  let acc := collectBlocks { geom := geom, xHeight := xHeight, styles := doc.styles }
    pats fs doc.body 0
  -- Break every paragraph in parallel: `kp` is pure and each job independent,
  -- so the tasks race on nothing; joining in document order below keeps the
  -- output independent of scheduling.
  let staged : Array (Sum Sp (ParaJob × Task (Array Nat))) := acc.ops.map fun op =>
    match op with
    | .skip dy => .inl dy
    | .para j => .inr (j, Task.spawn fun _ => kp j.items j.target)
  let b0 : B := {
    geom := geom
    ascent := scale font.ascent
    descent := scale (-font.descent)
    xHeight := xHeight
  }
  let mut b := { b0 with y := b0.freshY }
  for s in staged do
    match s with
    | .inl dy => b := { b with y := b.y + dy }
    | .inr (j, t) => b := placePara fs b j t.get
  let pages := b.pages.push b.cur
  -- Running content is laid out per page once the count is known, into the
  -- margin, so it never disturbs the body it annotates.
  let total := pages.size
  let runLine (content : Array Inline) (n : Nat) (y : Sp) (cache : _) :
      Option LineOut × Array Diag × _ :=
    let sub := substPage n total content
    let (items, ds, cache, _) :=
      itemsOfInlines pats geom.fontSize xHeight fs {} sub cache
    let target := geom.textWidth
    let breaks := kp items target
    match breaks[0]? with
    | none => (none, ds, cache)
    | some brk =>
      let (segs, w, _) := setLine items (lineStart items 0) brk target true
      (some { x := geom.hmargin, y := y, size := geom.fontSize, segs := segs,
              setWidth := w }, ds, cache)
  let headY := geom.vmargin / 2 + b0.ascent
  let footY := geom.pageH - geom.vmargin / 2
  let mut out := pages
  let mut diags := b.diags
  let mut cache := acc.hyphCache
  for i in [0:out.size] do
    let mut lines := out[i]!.lines
    -- Pages before `runningFrom` carry no furniture: an opening page reads
    -- as a title page, not as page one of a run.
    if i + 1 < doc.runningFrom then continue
    if let some content := doc.head then
      let (l?, ds, c) := runLine content (i + 1) headY cache
      diags := diags ++ ds
      cache := c
      if let some l := l? then lines := #[l] ++ lines
    if let some content := doc.foot then
      let (l?, ds, c) := runLine content (i + 1) footY cache
      diags := diags ++ ds
      cache := c
      if let some l := l? then lines := lines.push l
    out := out.set! i { lines := lines }
  { pages := out, diags := diags }

end LeanTex.Core.Layout
