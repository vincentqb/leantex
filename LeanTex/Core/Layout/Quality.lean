module

public import LeanTex.Core.Layout
public import LeanTex.Core.Struct
public import LeanTex.Core.Html

/-! # Typographic quality, read off the shipped pages

Judges of what a reader sees on `Layout.Out`: lines past the text area or
ink off the medium, a paragraph's single line stranded at a page boundary, a
hyphen carried over a page turn, a one-word last line, a table row or an
unbreakable block cut by a page break, a heading or a lead-in left at a
page's foot, a page the flow leaves short, glyphs set in a fallback face, a
left edge that steps where protrusion should hang it, and, on the typed
HTML tree, a font program shipped twice. Every judge reads the artifact
alone, so a diagnostic that names a defect never excuses it.

A line's block comes from the structure tree the pages are attributed
against (`LineOut.leaf` indexes `Struct.leaves (Struct.ofDoc (pdfView doc))`),
so "a paragraph" is the IR's paragraph, never a guess from geometry. -/

namespace LeanTex.Core.Layout.Quality

open LeanTex.Core LeanTex.Core.Dim

/-! ## The block a leaf belongs to -/

/-- What a page break may do to a leaf's block. `kind` is the innermost
block-level structure kind (inline wrappers looked through; a formula is
its holder's when inline, its own when displayed); `row` names the table
row and `group` the unbreakable unit (heading, title, caption, figure,
display formula) holding the leaf, and `display` the nearest display block
around it (a list, a table, a listing, a figure, a quotation, a display
formula), by node number. -/
public structure LeafRole where
  kind : Struct.Kind
  row : Option Nat
  group : Option Nat
  display : Option Nat
  deriving Repr, BEq, Inhabited

/-- Inline wrappers: a link, a language span, a reference. A leaf inside
one belongs to the block around it. -/
@[expose] public def transparent : Struct.Kind → Bool
  | .link _ | .span _ | .reference _ => true
  | .document | .section | .title | .heading _ | .paragraph | .list _ | .item | .label
  | .body | .table | .row | .cell | .caption | .figure | .formula | .code | .quote
  | .note | .aside | .nav | .bibEntry | .artifact => false

/-- Kinds whose children are inline content: a formula directly inside one
is set inline, and belongs to it. -/
@[expose] public def holdsInlines : Struct.Kind → Bool
  | .title | .heading _ | .paragraph | .label | .cell | .caption | .note | .bibEntry
  | .artifact => true
  | .document | .section | .list _ | .item | .body | .table | .row | .figure | .formula
  | .code | .quote | .aside | .nav | .link _ | .span _ | .reference _ => false

/-- Kinds a page break may not cut. -/
@[expose] public def unbreakable : Struct.Kind → Bool
  | .title | .heading _ | .caption | .figure => true
  | .document | .section | .paragraph | .list _ | .item | .label | .body | .table | .row
  | .cell | .formula | .code | .quote | .note | .aside | .nav | .bibEntry | .link _
  | .span _ | .reference _ | .artifact => false

/-- Kinds set apart from running prose: what a lead-in introduces. -/
@[expose] public def displays : Struct.Kind → Bool
  | .list _ | .table | .code | .figure | .quote => true
  | .document | .section | .title | .heading _ | .paragraph | .item | .label | .body | .row
  | .cell | .caption | .formula | .note | .aside | .nav | .bibEntry | .link _ | .span _
  | .reference _ | .artifact => false

/-- The block kind of a leaf from its enclosing kinds, innermost first. -/
public def roleKind (kinds : List Struct.Kind) : Struct.Kind :=
  match kinds.filter (!transparent ·) with
  | .formula :: k :: _ => if holdsInlines k then k else .formula
  | k :: _ => k
  | [] => .document

/-- The walk's context: enclosing kinds innermost first, and the nearest
row and unbreakable group by node number. -/
structure Ctx where
  kinds : List Struct.Kind := []
  row : Option Nat := none
  group : Option Nat := none
  display : Option Nat := none

/-- Enter node `id` of `kind`. A formula is a group only when displayed:
its nearest non-wrapper holder takes no inline content. -/
def Ctx.enter (c : Ctx) (kind : Struct.Kind) (id : Nat) : Ctx :=
  let displayed := kind == .formula &&
    !((c.kinds.filter (!transparent ·)).head?.map holdsInlines).getD false
  { kinds := kind :: c.kinds
    row := if kind == .row then some id else c.row
    group := if unbreakable kind || displayed then some id else c.group
    display := if displays kind || displayed then some id else c.display }

structure Roles where
  roles : Array LeafRole := #[]
  nodes : Nat := 0

-- Context walk over the structure tree: the shared `NodeFold` has no close
-- event, and a role needs the kinds above a leaf. Structural recursion
-- through `List`, the accumulator threaded.
mutual

def rolesList (c : Ctx) (acc : Roles) : List Struct.Node → Roles
  | [] => acc
  | n :: rest => rolesList c (rolesOne c acc n) rest

def rolesOne (c : Ctx) (acc : Roles) : Struct.Node → Roles
  | .leaf _ _ =>
    let role : LeafRole :=
      { kind := roleKind c.kinds, row := c.row, group := c.group, display := c.display }
    { acc with roles := acc.roles.push role }
  | .node kind kids =>
    rolesList (c.enter kind acc.nodes) { acc with nodes := acc.nodes + 1 } kids.toList

end

/-- Every leaf's role, by preorder index — the index `LineOut.leaf` holds
(`Struct.structTree_leaves_id`). -/
public def leafRoles (t : Struct.Tree) : Array LeafRole :=
  (rolesList {} {} t.children.toList).roles

/-! ## Reading one line -/

/-- How far a line's segments advance from its `x`. -/
public def advance (l : LineOut) : Sp :=
  l.segs.foldl (fun w s => w + s.advance) 0

/-- The glyphs of a line's runs, in order, each with its advance. -/
def glyphsOf (l : LineOut) : Array (Char × Sp) :=
  l.segs.foldl (fun acc s => match s with
    | .run _ _ _ _ gs .. => gs.foldl (fun a (_, c, adv) => a.push (c, adv)) acc
    | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .image .. | .poly .. => acc) #[]

/-- The last run carrying glyphs. -/
def lastRun? (l : LineOut) : Option Seg :=
  l.segs.reverse.find? fun s => match s with
    | .run _ _ _ _ gs .. => !gs.isEmpty
    | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .image .. | .poly .. => false

/-- Does the line end at a hyphenation point: its last run the breaker's
own discretionary hyphen? -/
public def endsHyphenated (l : LineOut) : Bool :=
  match lastRun? l with
  | some (.run _ _ _ _ _ _ _ _ _ _ .hyphen) => true
  | _ => false

/-- How many interword spaces the line sets. -/
public def wordGaps (l : LineOut) : Nat :=
  l.segs.foldl (fun n s => match s with
    | .gap _ true | .decoratedGap _ true _ => n + 1
    | .gap _ false | .decoratedGap _ false _ | .run .. | .decoration .. | .rule .. | .image ..
    | .poly .. => n) 0

/-- The glyph a line opens on, when its first advancing segment is a text
run (no indent, marker or kern before it) and that run is not a marker. -/
def openingGlyph? (l : LineOut) : Option (Char × Sp) :=
  match l.segs.find? (fun s => s.advance != 0) with
  | some (.run _ _ _ _ gs _ _ _ _ _ attr) =>
    match attr with
    | .label => none
    | .leaf _ | .block _ | .hyphen | .noteMark _ | .unattributed =>
      gs[0]?.map fun (_, c, adv) => (c, adv)
  | _ => none

/-- How far protrusion may hang a line's last glyph past the measure: the
engine's own table (`protrusionLR`) over the glyph's advance, widened by
the line's expansion, which scales the run that holds it. -/
def rightAllowance (l : LineOut) : Sp :=
  match (glyphsOf l).back? with
  | some (c, adv) =>
    let p := adv * ((protrusionLR c).2 : Int) / 1000
    p + p * l.expand.natAbs / 1000
  | none => 0

/-! ## The judges -/

/-- The rounding a set line's right edge carries: each glyph advance and
each expanded run rounds to the scaled point, so a line that fills its
measure exactly lands within one sp per segment of it. -/
def edgeSlack (l : LineOut) : Sp := l.segs.size

/-- Does a segment set ink of its own: a glyph, an image, a rule? A line of
decorations alone is the rider an underline or a strike lays under another
line's text, and stands or falls with that line. -/
def setsInk : Seg → Bool
  | .run _ _ _ _ gs .. => !gs.isEmpty
  | .image .. | .rule .. | .poly .. => true
  | .gap .. | .decoratedGap .. | .decoration .. => false

/-- Does a segment paint at all: its own ink, or a decoration's? -/
def paints (s : Seg) : Bool :=
  setsInk s || match s with
    | .decoration .. => true
    | .run .. | .gap .. | .decoratedGap .. | .rule .. | .image .. | .poly .. => false

/-- The horizontal span the segments `keep` selects cover: from the pen
position of the first to the end of the last, so an indent before the ink
or a fill after it is not counted as ink. -/
public def spanOf (keep : Seg → Bool) (l : LineOut) : Option (Sp × Sp) := Id.run do
  let mut x := l.x
  let mut span : Option (Sp × Sp) := none
  for s in l.segs do
    let next := x + s.advance
    if keep s then
      span := some (match span with
        | some (a, _) => (a, next)
        | none => (x, next))
    x := next
  return span

/-- The span a line's own ink covers. -/
public def inkSpan (l : LineOut) : Option (Sp × Sp) := spanOf setsInk l

/-- How far a body line passes the text area, beyond the hang protrusion
grants it: its ink's right end past `pageW - hmargin` less the last glyph's
allowance, or its ink's left end before `hmargin` less the hang the line
records. Furniture stands in the margin by design and a picture's labels
are the picture's; neither is a line of the text, and a decoration's rider
stands or falls with the line it decorates. -/
public def overflow (geom : Geom) (l : LineOut) : Sp :=
  if l.furniture || l.pictureLabel.isSome then 0 else
    match inkSpan l with
    | none => 0
    | some (a, b) =>
      let right := b - (geom.pageW - geom.hmargin) - rightAllowance l
      let left := geom.hmargin - (a + (if a == l.x then l.hang else 0))
      let past := max right left
      if past > edgeSlack l then past else 0

/-- Every body line's overflow, page by page. -/
public def overflows (geom : Geom) (pages : Array PageOut) : Array Sp :=
  pages.foldl (fun acc p => p.lines.foldl (fun a l =>
    let o := overflow geom l
    if o > 0 then a.push o else a) acc) #[]

/-- Does a line put ink off the medium (the page and its bleed), where no
viewer shows it? Horizontally by its advance, vertically by its glyphs'
own extents. -/
public def offMedium (geom : Geom) (fs : Font.FontSet) (l : LineOut) : Bool :=
  match spanOf paints l with
  | none => false
  | some (a, b) =>
    let (up, down) := segsInk fs l.segs
    !geom.onMedium a (b - a) || l.y - up < -geom.bleed || l.y + down > geom.pageH + geom.bleed

/-- A path's box: its geometry widened by half its stroke. -/
def pathBox (p : PathOut) : (Sp × Sp) × (Sp × Sp) :=
  let pad := (p.stroke.map (·.width / 2)).getD 0
  let ((x0, y0), (x1, y1)) := match p.path with
    | .circle cx cy r => ((cx - r, cy - r), (cx + r, cy + r))
    | .rect x y w h => ((x, y), (x + w, y + h))
    | .tri x1 y1 x2 y2 x3 y3 =>
      ((min x1 (min x2 x3), min y1 (min y2 y3)), (max x1 (max x2 x3), max y1 (max y2 y3)))
    | .segs ss =>
      match ss[0]? with
      | none => ((0, 0), (0, 0))
      | some s0 => ss.foldl (fun ((a, b), (c, d)) s =>
          let ((e, f), (g, h)) := s.box
          ((min a e, min b f), (max c g, max d h))) s0.box
  ((x0 - pad, y0 - pad), (x1 + pad, y1 + pad))

/-- Does a picture path reach off the medium? -/
public def pathOffMedium (geom : Geom) (p : PathOut) : Bool :=
  let ((x0, y0), (x1, y1)) := pathBox p
  x0 < -geom.bleed || y0 < -geom.bleed || x1 > geom.pageW + geom.bleed ||
    y1 > geom.pageH + geom.bleed

/-- Does a filled rectangle reach off the medium? A page ground covers the
medium exactly, and is on it. -/
public def fillOffMedium (geom : Geom) (f : Fill) : Bool :=
  f.x < -geom.bleed || f.y < -geom.bleed || f.x + f.w > geom.pageW + geom.bleed ||
    f.y + f.h > geom.pageH + geom.bleed

/-- Lines, paths and fills with ink off the medium, every page. -/
public def offMediumCount (geom : Geom) (fs : Font.FontSet) (pages : Array PageOut) : Nat :=
  pages.foldl (fun n p =>
    n + (p.lines.filter (offMedium geom fs)).size + (p.paths.filter (pathOffMedium geom)).size +
      (p.fills.filter (fillOffMedium geom)).size) 0

/-- The largest overflow any body line runs past the text area, in whole
points, rounding up: a hair over the edge is a point. -/
public def maxOverflowPt (geom : Geom) (pages : Array PageOut) : Nat :=
  (((overflows geom pages).foldl max 0 + 65535) / 65536).toNat

/-- The role of a line's block, if it names a leaf the tree holds. -/
def roleOf (roles : Array LeafRole) (l : LineOut) : Option LeafRole :=
  l.leaf.bind (roles[·]?)

/-- A line of running prose: a galley line of a paragraph outside a table,
a note or a float. -/
def prose (roles : Array LeafRole) (l : LineOut) : Bool :=
  l.counted && !l.note && ((roleOf roles l).map (·.kind == .paragraph)).getD false

/-- Two consecutive pages the flow runs across: flow pages, or the pages
one frame step spilled onto. An overlay's next step repeats its content on
a page of its own and continues nothing. -/
def continues (a b : PageOut) : Bool :=
  a.frameOrigin == b.frameOrigin

/-- What one page boundary strands: a paragraph whose lines straddle it,
with how many of them end the page before (`before`) and open the page
after (`after`), and whether the page before ends on a hyphen. -/
public structure Straddle where
  leaf : Nat
  before : Nat
  after : Nat
  hyphen : Bool
  deriving Repr, BEq, Inhabited

/-- How many of `ls`, read from the end, belong to `k`. -/
def runFromEnd (ls : Array LineOut) (k : Nat) : Nat :=
  (ls.reverse.toList.takeWhile (·.leaf == some k)).length

/-- How many of `ls`, read from the start, belong to `k`. -/
def runFromStart (ls : Array LineOut) (k : Nat) : Nat :=
  (ls.toList.takeWhile (·.leaf == some k)).length

/-- Every paragraph a page boundary splits, in page order. -/
public def straddles (roles : Array LeafRole) (pages : Array PageOut) : Array Straddle := Id.run do
  let mut out : Array Straddle := #[]
  for (a, b) in pages.toList.zip (pages.toList.drop 1) do
    unless continues a b do continue
    let la := a.lines.filter (·.counted)
    let lb := b.lines.filter (·.counted)
    match la.back?, lb[0]? with
    | some x, some y =>
      if let some k := x.leaf then
        if y.leaf == some k && prose roles x then
          out := out.push { leaf := k, before := runFromEnd la k, after := runFromStart lb k
                            hyphen := endsHyphenated x }
    | _, _ => pure ()
  return out

/-- Club lines: a paragraph's first line alone at the foot of a page. -/
public def clubs (ss : Array Straddle) : Nat := (ss.filter (·.before == 1)).size

/-- Widow lines: a paragraph's last line alone at the head of a page. -/
public def widows (ss : Array Straddle) : Nat := (ss.filter (·.after == 1)).size

/-- Page turns inside a hyphenated word. -/
public def pageHyphens (ss : Array Straddle) : Nat := (ss.filter (·.hyphen)).size

/-- Every prose line of each paragraph, in page order, by leaf. -/
def paragraphLines (roles : Array LeafRole) (pages : Array PageOut) :
    Array (Nat × Array LineOut) := Id.run do
  let mut keys : Array Nat := #[]
  let mut lines : Array (Array LineOut) := #[]
  for p in pages do
    for l in p.lines do
      if prose roles l then
        if let some k := l.leaf then
          if keys.back? == some k then
            lines := lines.modify (lines.size - 1) (·.push l)
          else
            keys := keys.push k
            lines := lines.push #[l]
  return keys.zip lines

/-- One-word last lines: a paragraph of two lines or more whose last line
sets no interword space. -/
public def runts (roles : Array LeafRole) (pages : Array PageOut) : Nat :=
  (paragraphLines roles pages).foldl (fun n (_, ls) =>
    match ls.back? with
    | some l => if 2 ≤ ls.size && wordGaps l == 0 && !(glyphsOf l).isEmpty then n + 1 else n
    | none => n) 0

/-- Hyphen ladders: each hyphenated line that follows two hyphenated lines
of its paragraph. -/
public def ladderLines (roles : Array LeafRole) (pages : Array PageOut) : Nat :=
  (paragraphLines roles pages).foldl (fun n (_, ls) =>
    (ls.foldl (fun (run, n) l =>
      if endsHyphenated l then (run + 1, if run ≥ 2 then n + 1 else n) else (0, n))
      (0, n)).2) 0

/-- The protrusion the engine's table grants a line's opening glyph. -/
def leftAllowance (c : Char) (adv : Sp) : Sp :=
  adv * ((protrusionLR c).1 : Int) / 1000

/-- Lines whose optical left edge steps out of its paragraph's: in a
paragraph set flush left — every line after the first on one measure edge
`x + hang` — a line on that edge that opens on a glyph and hangs it by
other than the protrusion table grants (`protrusionLR`), the step a reader
sees between a hung and an unhung quote. Counted only where the page
protrudes; a paragraph of one line has no edge to step from. -/
public def edgeStepLines (geom : Geom) (roles : Array LeafRole) (pages : Array PageOut) :
    Array LineOut :=
  if !geom.protrude then #[] else
  (paragraphLines roles pages).foldl (fun acc (_, ls) =>
    match ls[1]? with
    | none => acc
    | some second =>
      let edge := second.x + second.hang
      if !(ls.toList.drop 1).all (fun l => l.x + l.hang == edge) then acc else
        ls.foldl (fun acc l =>
          match openingGlyph? l with
          | some (c, adv) =>
            if l.x + l.hang == edge && (l.hang - leftAllowance c adv).natAbs > (edgeSlack l).natAbs
            then acc.push l else acc
          | none => acc) acc) #[]

/-- How many lines step out of their paragraph's optical edge. -/
public def edgeSteps (geom : Geom) (roles : Array LeafRole) (pages : Array PageOut) : Nat :=
  (edgeStepLines geom roles pages).size

/-- Keys present on two consecutive pages the flow runs across. -/
def splitKeys (key : LineOut → Option Nat) (pages : Array PageOut) : Nat := Id.run do
  let mut split : Array Nat := #[]
  for (a, b) in pages.toList.zip (pages.toList.drop 1) do
    unless continues a b do continue
    let ka := a.lines.filterMap fun l => if l.furniture then none else key l
    for l in b.lines do
      unless l.furniture do
        if let some k := key l then
          if ka.contains k && !split.contains k then split := split.push k
  return split.size

/-- Table rows a page break cuts. -/
public def splitRows (roles : Array LeafRole) (pages : Array PageOut) : Nat :=
  splitKeys (fun l => (roleOf roles l).bind (·.row)) pages

/-- Headings, titles, captions, figures and display formulas a page break
cuts. -/
public def splitBlocks (roles : Array LeafRole) (pages : Array PageOut) : Nat :=
  splitKeys (fun l => (roleOf roles l).bind (·.group)) pages

/-! ## What a page boundary leaves behind -/

/-- A page's body lines: neither furniture nor the note apparatus. -/
def bodyLines (p : PageOut) : Array LineOut :=
  p.lines.filter fun l => !l.furniture && !l.note

/-- The first and the last structure leaf a page's body sets, in the
preorder `LineOut.leaf` counts, which is reading order. -/
def leafSpan (p : PageOut) : Option (Nat × Nat) :=
  (bodyLines p).foldl (fun acc l => match l.leaf, acc with
    | some k, some (a, b) => some (min a k, max b k)
    | some k, none => some (k, k)
    | none, acc => acc) none

/-- The leaves a declared boundary opens a page on (`\newpage`,
`\pagebreak`): the leaf count of the page view's blocks ahead of each of its
top-level `.pagebreak`s, the counter `LineOut.leaf` reads
(`Struct.leafCountBlocks`). -/
public def declaredOpenings (doc : Ir.Doc) : Array Nat :=
  ((pdfView doc).body.foldl (fun (acc : Array Nat × Nat) b => match b with
    | .pagebreak => (acc.1.push acc.2, acc.2)
    | _ => (acc.1, acc.2 + Struct.leafCountBlocks #[b])) (#[], 0)).1

/-- Does the flow run from page `a` into page `b` with nothing declared
between them: one flow or one frame step's spill (`continues`), and no
declared boundary after everything `a` sets and no later than what `b`
opens on? -/
public def flowsAcross (opens : Array Nat) (a b : PageOut) : Bool :=
  continues a b && match leafSpan a, leafSpan b with
    | some (_, last), some (first, _) => !opens.any fun o => last < o && o ≤ first
    | _, _ => false

/-- Is a line set wholly in bold: every glyph run in a face of weight 600 or
more? -/
def boldLine (fs : Font.FontSet) (l : LineOut) : Bool :=
  let weights := l.segs.filterMap fun s => match s with
    | .run idx _ _ _ gs .. => if gs.isEmpty then none else some ((fs.fonts[idx]?).map (·.weight))
    | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .image .. | .poly .. => none
  !weights.isEmpty && weights.all fun w => (w.map fun v => decide (600 ≤ v)).getD false

/-- Does the boundary from `a` to `b` strand a heading or a lead-in: the
last block `a`'s body sets, whole on `a`, is a heading, or a paragraph of one
line that is set wholly in bold (a heading in all but name) or is followed
by the display block `b` opens on (the line that introduces it), while the
flow carries what it introduces onto `b`? `pages` is the document, which
says whether the paragraph has lines elsewhere. -/
public def strandedAt (fs : Font.FontSet) (roles : Array LeafRole) (opens : Array Nat)
    (pages : Array PageOut) (a b : PageOut) : Bool :=
  flowsAcross opens a b && match leafSpan a, leafSpan b with
    | some (_, k), some (first, _) =>
      !(bodyLines b).any (·.leaf == some k) && match ((roles[k]?).map (·.kind) : Option Struct.Kind) with
        | some (.heading _) => true
        | some .paragraph =>
          let own := pages.foldl (fun acc p => acc ++ (bodyLines p).filter (·.leaf == some k)) #[]
          own.size == 1 && (own.all (boldLine fs) || ((roles[first]?).bind (·.display)).isSome)
        | _ => false
    | _, _ => false

/-- Headings and lead-ins a page boundary strands (`strandedAt`). -/
public def strandedHeads (fs : Font.FontSet) (roles : Array LeafRole) (opens : Array Nat)
    (pages : Array PageOut) : Nat :=
  ((pages.toList.zip (pages.toList.drop 1)).filter fun (a, b) =>
    strandedAt fs roles opens pages a b).length

/-- The pitch of running prose: the smallest gap between two consecutive
lines of one paragraph on one page. -/
public def linePitch (roles : Array LeafRole) (pages : Array PageOut) : Option Sp :=
  pages.foldl (fun acc p =>
    let ls := p.lines.filter (prose roles)
    (ls.toList.zip (ls.toList.drop 1)).foldl (fun acc (x, y) =>
      if x.leaf == y.leaf && y.y > x.y then
        some (match acc with
          | some m => min m (y.y - x.y)
          | none => y.y - x.y)
      else acc) acc) none

/-- The room a page leaves under its body: from its lowest body baseline to
its floor — the text area's bottom, or a pitch above the top of its
footnotes. -/
public def roomAt (geom : Geom) (pitch : Sp) (a : PageOut) : Option Sp :=
  let low (ls : Array LineOut) (pick : Sp → Sp → Sp) : Option Sp :=
    ls.foldl (fun m l => some (match m with
      | some y => pick y l.y
      | none => l.y)) none
  (low (bodyLines a) max).map fun last =>
    (match low (a.lines.filter (·.note)) min with
      | some top => min geom.bodyBottom (top - pitch)
      | none => geom.bodyBottom) - last

/-- How many lines of room a page may leave at its foot before it reads as
short: a line or two is a ragged bottom's slack or a widow kept; more than
three is room the content did not fill. -/
public def shortPageLines : Nat := 3

/-- Is the boundary from `a` to `b` a short page: the flow continues
(`flowsAcross`) from a page whose body ends more than `shortPageLines` lines
of prose above its floor, leaving room the next page's content did not take? -/
public def shortAt (geom : Geom) (opens : Array Nat) (pitch : Sp) (a b : PageOut) : Bool :=
  flowsAcross opens a b && ((roomAt geom pitch a).map fun r =>
    decide (r > (shortPageLines : Int) * pitch)).getD false

/-- Short pages (`shortAt`), at the document's own prose pitch; a document
with no paragraph of two lines has no pitch to read a page by. -/
public def shortPages (geom : Geom) (roles : Array LeafRole) (opens : Array Nat)
    (pages : Array PageOut) : Nat :=
  match linePitch roles pages with
  | none => 0
  | some pitch =>
    ((pages.toList.zip (pages.toList.drop 1)).filter fun (a, b) =>
      shortAt geom opens pitch a b).length

/-- Is `c` a private-use scalar? An icon face's code points: no text sets
one, so a face chosen for it by coverage is the icon's declared face, not a
fallback. -/
def privateUse (c : Char) : Bool := 0xE000 ≤ c.toNat && c.toNat ≤ 0xF8FF

/-- Text runs set in a face no text slot names: the per-glyph fallback's
work (a formula's runs are the math face's own, and icons are excluded). -/
public def fallbackRuns (fs : Font.FontSet) (pages : Array PageOut) : Nat :=
  let slots := fs.index.map (·.2)
  pages.foldl (fun n p => p.lines.foldl (fun n l => l.segs.foldl (fun n s =>
    match s with
    | .run idx _ _ _ gs _ metrics .. =>
      if gs.isEmpty || metrics.math.isSome || slots.contains idx ||
          gs.all (fun (_, c, _) => privateUse c) then n else n + 1
    | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .image .. | .poly .. => n) n) n) 0

/-! ## The HTML page -/

-- The stylesheets of a tree, in order: one walk over the elements with the
-- accumulator threaded, structurally through `List`.
mutual

def stylesList (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | n :: rest => stylesList (stylesOne acc n) rest

def stylesOne (acc : Array String) : Html.Node → Array String
  | .style css => acc.push css
  | .elem _ _ kids => stylesList acc kids.toList
  | .text _ => acc
  | .script _ _ => acc

end

/-- The font programs a page's stylesheets ship: the source of every
`@font-face` rule, in order. -/
public def fontSources (nodes : Array Html.Node) : Array String :=
  (stylesList #[] nodes.toList).foldl (fun acc css =>
    ((css.splitOn "@font-face").drop 1).foldl (fun acc rule =>
      match ((rule.splitOn "}").headD "").splitOn "url(\"" with
      | _ :: src :: _ => acc.push ((src.splitOn "\")").headD "")
      | _ => acc) acc) #[]

/-- Font programs a page ships more than once: every `@font-face` source
beyond the first carrying the same bytes. -/
public def duplicatePrograms (nodes : Array Html.Node) : Nat :=
  let srcs := fontSources nodes
  let distinct := srcs.foldl (fun (seen : Array (UInt64 × Nat)) s =>
    let k := (hash s, s.length)
    if seen.contains k then seen else seen.push k) #[]
  srcs.size - distinct.size

end LeanTex.Core.Layout.Quality
