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
  deriving Repr

def Geom.textWidth (g : Geom) : Sp := g.pageW - 2 * g.hmargin

/-- Resolve a document's `\page` declaration into layout geometry. One source
of truth: layout reads geometry only from here. -/
def Geom.ofPage (spec : Ir.PageSpec) (base : Geom := {}) : Geom :=
  { base with
    pageW := spec.width
    pageH := spec.height
    hmargin := spec.hmargin
    vmargin := spec.vmargin }

def leadingFor (size : Sp) : Sp := size * 6 / 5

inductive Item where
  | box (w : Sp) (glyphs : Array (Nat × Char × Sp))
  | glue (g : Glue)
  | pen (w : Sp) (cost : Int) (flagged : Bool) (glyphs : Array (Nat × Char × Sp))
  deriving Repr, Inhabited

def forcedCost : Int := -10000

def hyphenPenalty : Int := 50

inductive Seg where
  | run (glyphs : Array (Nat × Char))
  | gap (w : Sp)
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

private inductive Tk where
  | word (chars : Array Char)
  | space
  | brk
  deriving Repr

private structure FlattenSt where
  toks : Array Tk := #[]
  warnedStyle : Bool := false
  warnedMath : Bool := false
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

mutual

private def flatten (st : FlattenSt) (xs : Array Inline) : FlattenSt :=
  flattenList st xs.toList

private def flattenList (st : FlattenSt) (xs : List Inline) : FlattenSt :=
  match xs with
  | [] => st
  | x :: rest => flattenList (flattenOne st x) rest

private def flattenOne (st : FlattenSt) (x : Inline) : FlattenSt :=
  match x with
  | .text s => pushText st s
  | .linebreak => { st with toks := st.toks.push .brk }
  | .math _ src =>
    let st := if st.warnedMath then st
      else { warn st "W0003" "math is typeset as plain text until M4" with warnedMath := true }
    pushText st src
  | .styled _ body =>
    let st := if st.warnedStyle then st
      else { warn st "W0002" "styles are not rendered yet (single font until M3)" with
        warnedStyle := true }
    flatten st body

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

/-- One word → items: boxes split by hyphenation points (flagged penalties
carrying the hyphen glyph) and by explicit hyphens (unflagged, no glyph). -/
private def wordItems (pats : Option Hyphen.Patterns) (size : Sp) (font : Font)
    (chars : Array Char) (missing : Array Char)
    (cache : Std.HashMap String (List Nat)) :
    Array Item × Array Char × Std.HashMap String (List Nat) := Id.run do
  let mut missing := missing
  let mut cache := cache
  let hyphW := (hyphenGlyph size font).foldl (fun w (_, _, adv) => w + adv) 0
  let mut items : Array Item := #[]
  let mut box : Array (Nat × Char × Sp) := #[]
  let mut boxW : Sp := 0
  let flush (items : Array Item) (box : Array (Nat × Char × Sp)) (w : Sp) : Array Item :=
    if box.isEmpty then items else items.push (.box w box)
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
            items := items.push (.pen hyphW hyphenPenalty true (hyphenGlyph size font))
          match glyphOf size font c' with
          | some g =>
            box := box.push g
            boxW := boxW + g.2.2
          | none =>
            unless missing.contains c' do
              missing := missing.push c'
        i := j
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
          items := items.push (.pen 0 hyphenPenalty false #[])
    else
      break
  items := flush items box boxW
  return (items, missing, cache)

private def interword (size : Sp) (font : Font) : Glue :=
  let w := scaledAt size font (font.advance ' ')
  { width := w, stretch := w / 2, shrink := w / 3 }

private def itemsOfInlines (pats : Option Hyphen.Patterns) (size : Sp) (font : Font)
    (xs : Array Inline) (cache : Std.HashMap String (List Nat)) :
    Array Item × Array Diag × Std.HashMap String (List Nat) := Id.run do
  let st := flatten {} xs
  let mut items : Array Item := #[]
  let mut missing : Array Char := #[]
  let mut cache := cache
  for tk in st.toks do
    match tk with
    | .word chars =>
      let (ws, m, c') := wordItems pats size font chars missing cache
      missing := m
      cache := c'
      items := items ++ ws
    | .space => items := items.push (.glue (interword size font))
    | .brk =>
      items := items.push (.glue { fil := true })
      items := items.push (.pen 0 forcedCost false #[])
  items := items.push (.glue { fil := true })
  items := items.push (.pen 0 forcedCost false #[])
  let mut diags := st.diags
  for c in missing do
    diags := diags.push {
      severity := .warning
      code := "W0004"
      message := s!"the font has no glyph for '{c}' (U+{hex c.toNat}); dropped"
    }
  return (items, diags, cache)
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
  | some (.pen _ cost _ _) => cost < 10000
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
    | some (.pen _ cost _ _) => if cost ≥ 10000 then break else a := a + 1
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
    | .pen _ _ _ _ => pure ()
  if let some (.pen w _ _ _) := items[j]? then
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
    | some (.pen _ cost _ _) =>
      if cost ≤ forcedCost then 0
      else if cost > 0 then cost ^ 2
      else -(cost ^ 2)
    | _ => 0
  base + penTerm

def isForced (items : Array Item) (k : Nat) : Bool :=
  match items[k]? with
  | some (.pen _ cost _ _) => cost ≤ forcedCost
  | _ => false

def isFlagged (items : Array Item) (k : Nat) : Bool :=
  match items[k]? with
  | some (.pen _ _ flagged _) => flagged
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
      | .box w _ => (w, 0, 0, 0)
      | .glue g => (g.width, g.stretch, g.shrink, if g.fil then 1 else 0)
      | .pen _ _ _ _ => (0, 0, 0, 0)
    pw := pw.push (pw[k]! + dw)
    ps := ps.push (ps[k]! + dst)
    pk := pk.push (pk[k]! + dsh)
    pf := pf.push (pf[k]! + dfil)
    pforced := pforced.push (pforced[k]! + (if isForced items k then 1 else 0))
  let measureAt (a j : Nat) : Measure :=
    let penW : Sp := match items[j]? with
      | some (.pen w _ _ _) => w
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
    | .pen _ _ _ _ => pure ()
  -- breaking at a penalty appends its glyphs (the hyphen)
  if let some (.pen w _ _ glyphs) := items[j]? then
    if !glyphs.isEmpty then
      segs := segs.push (.run (glyphs.map fun (g, c, _) => (g, c)))
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
  pages : Array PageOut := #[]
  cur : PageOut := {}
  y : Sp := 0
  diags : Array Diag := #[]
  hyphCache : Std.HashMap String (List Nat) := {}

private def B.freshY (b : B) : Sp := b.geom.vmargin + b.ascent

private def B.breakPage (b : B) : B :=
  { b with pages := b.pages.push b.cur, cur := {}, y := b.freshY }

private def B.placeLine (b : B) (x : Sp) (size : Sp) (segs : Array Seg) (w : Sp) : B :=
  let b := if b.y + b.descent > b.geom.pageH - b.geom.vmargin then b.breakPage else b
  let line : LineOut := { x := x, y := b.y, size := size, segs := segs, setWidth := w }
  { b with cur := { lines := b.cur.lines.push line }, y := b.y + leadingFor size }

private def B.warnOverfull (b : B) : B :=
  { b with diags := b.diags.push {
    severity := .warning
    code := "W0005"
    message := "overfull line (no feasible break)"
  } }

private def typesetPara (b : B) (pats : Option Hyphen.Patterns) (font : Font)
    (inlines : Array Inline) (indent : Sp) (center : Bool) (size : Sp)
    (bullet : Option (Array (Nat × Char × Sp)) := none) : B := Id.run do
  let mut b := b
  let geom := b.geom
  let width := geom.textWidth - indent
  let (items, ds, cache) := itemsOfInlines pats size font inlines b.hyphCache
  b := { b with diags := b.diags ++ ds, hyphCache := cache }
  let breaks := kp items width
  let mut prev := 0
  let mut first := true
  for brk in breaks do
    let a := if first then lineStart items 0 else lineStart items (prev + 1)
    let (segs, w, overfull) := setLine items a brk width (!center)
    if overfull then
      b := b.warnOverfull
    let mut x := if center then geom.hmargin + indent + (width - w) / 2
      else geom.hmargin + indent
    let mut segs := segs
    let mut w := w
    if first then
      if let some bg := bullet then
        let bw := bg.foldl (fun acc (_, _, adv) => acc + adv) 0
        let sep := geom.fontSize * 2 / 5
        segs := #[Seg.run (bg.map fun (g, c, _) => (g, c)), Seg.gap sep] ++ segs
        x := x - bw - sep
        w := w + bw + sep
    b := b.placeLine x size segs w
    prev := brk
    first := false
  return b

def sectionSize (geom : Geom) : Nat → Sp
  | 1 => pt 14
  | 2 => pt 12
  | _ => geom.fontSize

-- Block walk. Mutual recursion through `List` so the nested calls are
-- structural: no `partial`, and the shape mirrors the IR.
mutual

/-- Typeset a block sequence, spacing peers by `parskip`. -/
def typesetBlocks (b : B) (pats : Option Hyphen.Patterns) (font : Font)
    (blocks : Array Block) (indent : Sp) : B :=
  typesetBlockList b pats font blocks.toList indent true

def typesetBlockList (b : B) (pats : Option Hyphen.Patterns) (font : Font)
    (blocks : List Block) (indent : Sp) (first : Bool) : B :=
  match blocks with
  | [] => b
  | blk :: rest =>
    let b := if first then b else { b with y := b.y + b.geom.parskip }
    let b := typesetBlock b pats font blk indent
    typesetBlockList b pats font rest indent false

/-- One list item: its leading paragraph carries the marker. -/
def typesetItem (b : B) (pats : Option Hyphen.Patterns) (font : Font)
    (item : List Block) (indent : Sp) (first : Bool) : B :=
  match item with
  | [] => b
  | blk :: rest =>
    let b := if first then b else { b with y := b.y + b.geom.parskip }
    let b := match blk, first with
      | .para content, true =>
        typesetPara b pats font content indent false b.geom.fontSize
          (bullet := some (bulletGlyphs b.geom.fontSize font))
      | _, _ => typesetBlock b pats font blk indent
    typesetItem b pats font rest indent false

def typesetItems (b : B) (pats : Option Hyphen.Patterns) (font : Font)
    (items : List (Array Block)) (indent : Sp) : B :=
  match items with
  | [] => b
  | item :: rest =>
    let b := typesetItem b pats font item.toList indent true
    typesetItems b pats font rest indent

/-- Centered content: paragraphs center, anything else nests unchanged. -/
def typesetCentered (b : B) (pats : Option Hyphen.Patterns) (font : Font)
    (body : List Block) (indent : Sp) : B :=
  match body with
  | [] => b
  | blk :: rest =>
    let b := match blk with
      | .para content => typesetPara b pats font content indent true b.geom.fontSize
      | _ => typesetBlock b pats font blk indent
    typesetCentered b pats font rest indent

def typesetBlock (b : B) (pats : Option Hyphen.Patterns) (font : Font)
    (blk : Block) (indent : Sp) : B :=
  match blk with
  | .para content =>
    typesetPara b pats font content indent false b.geom.fontSize
  | .section level _ title =>
    let b := { b with y := b.y + b.geom.parskip }
    typesetPara b pats font title indent false (sectionSize b.geom level)
  | .list _ items =>
    typesetItems b pats font items.toList (indent + b.geom.listIndent)
  | .center body =>
    typesetCentered b pats font body.toList indent

end

/-- Typeset a document body into positioned pages. Geometry is resolved by
the caller via `Geom.ofPage`, so layout has one source of truth. -/
def run (geom : Geom) (font : Font) (pats : Option Hyphen.Patterns) (doc : Doc) : Out :=
  let scale (u : Int) : Sp := u * geom.fontSize / font.unitsPerEm
  let b : B := {
    geom := geom
    ascent := scale font.ascent
    descent := scale (-font.descent)
  }
  let b := { b with y := b.freshY }
  let b := typesetBlocks b pats font doc.body 0
  let pages := b.pages.push b.cur
  { pages := pages, diags := b.diags }

end LeanTex.Core.Layout
