import LeanTex.Core.Dim
import LeanTex.Core.Font
import LeanTex.Core.Ir
import LeanTex.Core.Diag

namespace LeanTex.Core.Layout

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Font LeanTex.Core.Ir

structure Geom where
  pageW : Sp := pt 612
  pageH : Sp := pt 792
  margin : Sp := inch 1
  fontSize : Sp := pt 10
  leading : Sp := pt 12
  parskip : Sp := pt 6
  listIndent : Sp := pt 15
  deriving Repr

def Geom.textWidth (g : Geom) : Sp := g.pageW - 2 * g.margin

inductive Item where
  | box (w : Sp) (glyphs : Array (Nat × Char × Sp))
  | glue (g : Glue)
  | pen (w : Sp) (cost : Int) (flagged : Bool)
  deriving Repr, Inhabited

def forcedCost : Int := -10000

inductive Seg where
  | run (glyphs : Array (Nat × Char))
  | gap (w : Sp)
  deriving Repr, Inhabited

structure LineOut where
  x : Sp
  y : Sp
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

private inductive Tk where
  | word (chars : Array Char)
  | space
  | brk
  deriving Repr

private structure FlattenSt where
  toks : Array Tk := #[]
  warnedStyle : Bool := false
  warnedMath : Bool := false
  missing : Array Char := #[]
  diags : Array Diag := #[]

private def warn (st : FlattenSt) (code msg : String) : FlattenSt :=
  { st with diags := st.diags.push { severity := .warning, code := code, message := msg } }

private def pushText (st : FlattenSt) (s : String) : FlattenSt := Id.run do
  let mut st := st
  let mut cur : Array Char := #[]
  for c in s.toList do
    if c == ' ' then
      if !cur.isEmpty then
        st := { st with toks := st.toks.push (.word cur) }
        cur := #[]
      st := { st with toks := st.toks.push .space }
    else
      cur := cur.push c
  if !cur.isEmpty then
    st := { st with toks := st.toks.push (.word cur) }
  return st

private partial def flatten (st : FlattenSt) (xs : Array Inline) : FlattenSt := Id.run do
  let mut st := st
  for x in xs do
    match x with
    | .text s => st := pushText st s
    | .linebreak => st := { st with toks := st.toks.push .brk }
    | .math _ src =>
      if !st.warnedMath then
        st := warn st "W0003" "math is typeset as plain text until M4"
        st := { st with warnedMath := true }
      st := pushText st src
    | .styled _ body =>
      if !st.warnedStyle then
        st := warn st "W0002" "styles are not rendered yet (single font until M3)"
        st := { st with warnedStyle := true }
      st := flatten st body
  return st

-- Items -----------------------------------------------------------------------

private def scaled (geom : Geom) (font : Font) (units : Nat) : Sp :=
  (units * geom.fontSize.toNat) / font.unitsPerEm

private def wordBox (geom : Geom) (font : Font) (chars : Array Char)
    (missing : Array Char) : Item × Array Char := Id.run do
  let mut glyphs : Array (Nat × Char × Sp) := #[]
  let mut w : Sp := 0
  let mut missing := missing
  for c in chars do
    match font.gid c with
    | some g =>
      let adv := scaled geom font (font.widths[g]?.getD 0)
      glyphs := glyphs.push (g, c, adv)
      w := w + adv
    | none =>
      unless missing.contains c do
        missing := missing.push c
  return (.box w glyphs, missing)

private def interword (geom : Geom) (font : Font) : Glue :=
  let w := scaled geom font (font.advance ' ')
  { width := w, stretch := w / 2, shrink := w / 3 }

private def itemsOfInlines (geom : Geom) (font : Font) (xs : Array Inline) :
    Array Item × Array Diag := Id.run do
  let st := flatten {} xs
  let mut items : Array Item := #[]
  let mut missing : Array Char := #[]
  for tk in st.toks do
    match tk with
    | .word chars =>
      let (b, m) := wordBox geom font chars missing
      missing := m
      items := items.push b
    | .space => items := items.push (.glue (interword geom font))
    | .brk =>
      items := items.push (.glue { fil := true })
      items := items.push (.pen 0 forcedCost false)
  -- paragraph end: infinitely stretchable fill, then a forced break
  items := items.push (.glue { fil := true })
  items := items.push (.pen 0 forcedCost false)
  let mut diags := st.diags
  for c in missing do
    diags := diags.push {
      severity := .warning
      code := "W0004"
      message := s!"the font has no glyph for '{c}' (U+{hex c.toNat}); dropped"
    }
  return (items, diags)
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
    | some (.box _ _) => j > 0
    | _ => false
  | some (.pen _ cost _) => cost < 10000
  | _ => false

structure Measure where
  natural : Sp := 0
  stretch : Sp := 0
  shrink : Sp := 0
  fil : Bool := false

/-- Line contents run from the first non-discardable item after the previous
break up to (exclusive) the break item; a penalty break adds its width. -/
def lineStart (items : Array Item) (prevBreak : Nat) : Nat := Id.run do
  let mut a := if prevBreak == 0 then 0 else prevBreak + 1
  for _ in [a:items.size] do
    match items[a]? with
    | some (.glue _) => a := a + 1
    | some (.pen _ cost _) => if cost ≥ 10000 then break else a := a + 1
    | _ => break
  return a

def measure (items : Array Item) (a j : Nat) : Measure := Id.run do
  let mut m : Measure := {}
  for k in [a:j] do
    match items[k]! with
    | .box w _ => m := { m with natural := m.natural + w }
    | .glue g => m := { m with
        natural := m.natural + g.width
        stretch := m.stretch + g.stretch
        shrink := m.shrink + g.shrink
        fil := m.fil || g.fil }
    | .pen _ _ _ => pure ()
  if let some (.pen w _ _) := items[j]? then
    m := { m with natural := m.natural + w }
  return m

def overfullDemerits : Int := 100000000

/-- Badness-based demerits of a candidate line, `none` when hard-infeasible
(can never happen for overfull lines: they get huge but finite demerits so a
solution always exists). -/
def lineDemerits (items : Array Item) (m : Measure) (target : Sp)
    (j : Nat) : Int :=
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
    | some (.pen _ cost _) =>
      if cost ≤ forcedCost then 0
      else if cost > 0 then cost ^ 2
      else -(cost ^ 2)
    | _ => 0
  base + penTerm

def isForced (items : Array Item) (k : Nat) : Bool :=
  match items[k]? with
  | some (.pen _ cost _) => cost ≤ forcedCost
  | _ => false

/-- Optimal breakpoints by dynamic programming over break positions.
Returns the item indices of the chosen breaks, in order. -/
def kp (items : Array Item) (target : Sp) : Array Nat := Id.run do
  let n := items.size
  -- best.get j = some (demerits, previous break) for break position j;
  -- position n is the virtual "start" node stored at index of items? use
  -- prev = n to mean "paragraph start".
  let mut best : Array (Option (Int × Nat)) := Array.replicate (n + 1) none
  best := best.set! n (some (0, n))
  let mut order : Array Nat := #[n]
  for j in [0:n] do
    if canBreakAt items j then
      let mut bestHere : Option (Int × Nat) := none
      for p in order do
        if p == n || p < j then
          -- a line may not span a forced break
          let a := lineStart items (if p == n then 0 else p)
          let mut spansForced := false
          for k in [a:j] do
            if isForced items k then
              spansForced := true
              break
          if !spansForced && a ≤ j then
            match best[p]! with
            | some (d0, _) =>
              let m := measure items a j
              let d := d0 + lineDemerits items m target j
              match bestHere with
              | some (dBest, _) =>
                if d < dBest then bestHere := some (d, p)
              | none => bestHere := some (d, p)
            | none => pure ()
      if bestHere.isSome then
        best := best.set! j bestHere
        order := order.push j
  -- reconstruct from the last break (the final forced penalty)
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
  -- count fil glues for distribution
  let mut fils := 0
  for k in [a:j] do
    if let some (.glue g) := items[k]? then
      if g.fil then fils := fils + 1
  let mut segs : Array Seg := #[]
  let mut width : Sp := 0
  for k in [a:j] do
    match items[k]! with
    | .box _ glyphs =>
      let mut run : Array (Nat × Char) := #[]
      let mut w : Sp := 0
      for (g, c, adv) in glyphs do
        run := run.push (g, c)
        w := w + adv
      segs := segs.push (.run run)
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
    | .pen _ _ _ => pure ()
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
  pages : Array PageOut := #[]
  cur : PageOut := {}
  y : Sp := 0
  diags : Array Diag := #[]

private def B.freshY (b : B) : Sp := b.geom.margin + b.ascent

private def B.breakPage (b : B) : B :=
  { b with pages := b.pages.push b.cur, cur := {}, y := b.freshY }

private def B.placeLine (b : B) (x : Sp) (segs : Array Seg) (w : Sp) : B :=
  let b := if b.y + b.descent > b.geom.pageH - b.geom.margin then b.breakPage else b
  let line : LineOut := { x := x, y := b.y, segs := segs, setWidth := w }
  { b with cur := { lines := b.cur.lines.push line }, y := b.y + b.geom.leading }

private def B.warnOverfull (b : B) : B :=
  { b with diags := b.diags.push {
    severity := .warning
    code := "W0005"
    message := "overfull line (no feasible break)"
  } }

private def typesetPara (b : B) (font : Font) (inlines : Array Inline)
    (indent : Sp) (center : Bool) : B := Id.run do
  let mut b := b
  let geom := b.geom
  let width := geom.textWidth - indent
  let (items, ds) := itemsOfInlines geom font inlines
  b := { b with diags := b.diags ++ ds }
  let breaks := kp items width
  let mut prev := 0
  let mut first := true
  for brk in breaks do
    let a := if first then lineStart items 0 else lineStart items prev
    let (segs, w, overfull) := setLine items a brk width (!center)
    if overfull then
      b := b.warnOverfull
    let x := if center then geom.margin + indent + (width - w) / 2 else geom.margin + indent
    b := b.placeLine x segs w
    prev := brk
    first := false
  return b

partial def typesetBlocks (b : B) (font : Font) (blocks : Array Block)
    (indent : Sp) : B := Id.run do
  let mut b := b
  let geom := b.geom
  let mut firstBlock := true
  for blk in blocks do
    unless firstBlock do
      b := { b with y := b.y + geom.parskip }
    firstBlock := false
    match blk with
    | .para content =>
      b := typesetPara b font content indent false
    | .section _ _ title =>
      b := { b with y := b.y + geom.parskip }
      b := typesetPara b font title indent false
    | .list _ items =>
      for item in items do
        b := typesetBlocks b font item (indent + geom.listIndent)
    | .center body =>
      for cb in body do
        match cb with
        | .para content => b := typesetPara b font content indent true
        | _ => b := typesetBlocks b font #[cb] indent
  return b

/-- Typeset a document body into positioned pages. -/
def run (geom : Geom) (font : Font) (doc : Doc) : Out :=
  let scale (u : Int) : Sp := u * geom.fontSize / font.unitsPerEm
  let b : B := {
    geom := geom
    ascent := scale font.ascent
    descent := scale (-font.descent)
  }
  let b := { b with y := b.freshY }
  let b := typesetBlocks b font doc.body 0
  let pages := b.pages.push b.cur
  { pages := pages, diags := b.diags }

end LeanTex.Core.Layout
