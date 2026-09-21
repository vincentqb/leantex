import LeanTex.Core.Dim
import LeanTex.Core.Layout

/-!
# PDF content streams as typed operators

A page's content stream is built as an `Array ContentOp` — one constructor
per painting operator the writer emits — and rendered by `render`, a pure
serializer with an equational theory (`content_render_exact` and its
per-constructor twins). The construction (`contentOps`) is the layout
walk that decides pen moves, `TJ` arrays, and graphics-state changes; the
rendering is spelling only. Marked content (`BDC`/`EMC`) is the next
constructor: it lands as `marked (tag) (body)`, so an ill-nested pair is
unrepresentable, and every exhaustive match here turns into a build error
at each site it must reach.
-/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Layout

/-- One hexadecimal digit of `n`'s low nibble, upper case. -/
def hexDigit (n : Nat) : Char :=
  match n % 16 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'A' | 11 => 'B' | 12 => 'C' | 13 => 'D' | 14 => 'E' | _ => 'F'

/-- `acc` with a glyph id's four hex digits pushed — the digits an
Identity-H CID string spells (ISO 32000-2 §9.7.4.2: two bytes per CID).
Pushing in place is the hot path (every glyph on every page); `gidHex` is
its four-character value, `pushGid_eq` the equation between them. -/
def pushGid (acc : String) (g : Nat) : String :=
  (((acc.push (hexDigit (g / 4096))).push (hexDigit (g / 256))).push (hexDigit (g / 16))).push
    (hexDigit g)

def gidHex (g : Nat) : String := pushGid "" g

theorem pushGid_eq (acc : String) (g : Nat) : pushGid acc g = acc ++ gidHex g := by
  simp only [pushGid, gidHex, String.push_eq_append, String.empty_append, String.append_assoc]

/-- Path construction operators, ISO 32000-2 §8.5.2 (Table 58). -/
inductive PathOp where
  | moveTo (x y : Sp)
  | lineTo (x y : Sp)
  | curveTo (x1 y1 x2 y2 x3 y3 : Sp)
  | close
  | rect (x y w h : Sp)
  deriving Repr, BEq, Inhabited

/-- One element of a `TJ` array (§9.4.3): a glyph string, or a horizontal
adjustment in thousandths of the text space unit. -/
inductive TextItem where
  | glyphs (gids : Array Nat)
  | adjust (d : Int)
  deriving Repr, BEq, Inhabited

/-- Text-object operators (§9.3–9.4): horizontal scale in per-mille,
text matrix, font resource and size, fill colour, and one `TJ` array. -/
inductive TextOp where
  | scale (permille : Int)
  | move (x y : Sp)
  | font (res : Nat) (size : Sp)
  | color (c : Ir.Color)
  | show (items : Array TextItem)
  deriving Repr, BEq, Inhabited

/-- One page-level painting operation, in PDF user space. -/
inductive ContentOp where
  /-- A filled rectangle: a page fill or a rule. -/
  | fill (color : Ir.Color) (x y w h : Sp)
  /-- A picture path with its declared paint; the painting operator
  (`B`/`S`/`f`/`n`) is decided by which paints are present. -/
  | path (fill : Option Ir.Color) (stroke : Option Ir.Pic.Stroke) (segs : Array PathOp)
  /-- The page's one text object, `BT … ET`. -/
  | text (ops : Array TextOp)
  /-- An image XObject mapped onto `w × h` at `(x, y)`. -/
  | image (x y w h : Sp) (res : Nat)
  /-- The outlined box standing where an image that did not load would. -/
  | imageMissing (x y w h : Sp)
  deriving Repr, BEq, Inhabited

def PathOp.render : PathOp → String
  | .moveTo x y => s!"{x.toPtString} {y.toPtString} m "
  | .lineTo x y => s!"{x.toPtString} {y.toPtString} l "
  | .curveTo x1 y1 x2 y2 x3 y3 =>
    s!"{x1.toPtString} {y1.toPtString} {x2.toPtString} {y2.toPtString} \
{x3.toPtString} {y3.toPtString} c "
  | .close => "h "
  | .rect x y w h => s!"{x.toPtString} {y.toPtString} {w.toPtString} {h.toPtString} re "

def TextItem.render : TextItem → String
  | .glyphs gids => (gids.foldl pushGid "<").push '>'
  | .adjust d => toString d

def TextOp.render : TextOp → String
  | .scale p => s!"{p / 10}.{p % 10} Tz\n"
  | .move x y => s!"1 0 0 1 {x.toPtString} {y.toPtString} Tm\n"
  | .font res size => s!"/F{res + 1} {size.toPtString} Tf\n"
  | .color c => c.pdfFill ++ "\n"
  | .show items => (items.foldl (fun acc it => acc ++ it.render) "[") ++ "] TJ\n"

/-- Dash patterns, §8.4.3.6, with pgf's rhythms (pgf manual §15.3.2:
dashed on 3 pt off 3 pt, dotted on the line width off 1 pt). -/
def dashOp (st : Ir.Pic.Stroke) : String :=
  match st.dash with
  | .solid => ""
  | .dashed => "[3 3] 0 d "
  | .dotted => s!"[{st.width.toPtString} 1] 0 d "

/-- The path-painting operator the declared paints select (§8.5.3, Table
60): `B` fills then strokes, `S` strokes, `f` fills, `n` ends the path
without painting. -/
def paintOp : Option Ir.Pic.Stroke → Option Ir.Color → String
  | some _, some _ => "B"
  | some _, none => "S"
  | none, some _ => "f"
  | none, none => "n"

def strokeOp : Option Ir.Pic.Stroke → String
  | some st =>
    let dash := dashOp st
    s!"{st.color.pdfStroke} {st.width.toPtString} w " ++ dash
  | none => ""

def fillOp : Option Ir.Color → String
  | some c => s!"{c.pdfFill} "
  | none => ""

def ContentOp.render : ContentOp → String
  | .fill c x y w h =>
    s!"q {c.pdfFill} {x.toPtString} {y.toPtString} {w.toPtString} {h.toPtString} re f Q"
  | .path fl st segs =>
    let fillS := fillOp fl
    let strokeS := strokeOp st
    let head := "q " ++ fillS ++ strokeS
    let body := segs.foldl (fun acc seg => acc ++ seg.render) head
    body ++ paintOp st fl ++ " Q"
  | .text ops => (ops.foldl (fun acc op => acc ++ op.render) "BT\n") ++ "ET"
  | .image x y w h res =>
    s!"q {w.toPtString} 0 0 {h.toPtString} {x.toPtString} {y.toPtString} cm /Im{res + 1} Do Q"
  | .imageMissing x y w h =>
    -- A neutral grey hairline box: the failure is visible where the figure
    -- would stand, and the diagnostic already said why.
    s!"q 0.62 0.62 0.66 RG 0.75 w {x.toPtString} {y.toPtString} {w.toPtString} \
{h.toPtString} re S Q"

/-- One step of `render`: the first operation opens the stream, every
later one follows a newline. -/
def renderStep : Option String → ContentOp → Option String
  | none, op => some op.render
  | some s, op => some (s ++ "\n" ++ op.render)

/-- The stream: operations one per line. -/
def render (ops : Array ContentOp) : String := (ops.foldl renderStep none).getD ""

/-! ## Construction: the layout walk -/

/-- The text object's walk state. `items` is the open `TJ` array — empty
exactly when no array is open. `font` is the layout face index in force
(`-1` before the first `Tf`), `size` and `color` likewise; `tz` the live
expansion in per-mille delta from 100 %; `x` the layout position; `pen`
where the PDF pen is, once a glyph run has set it. Rules and images
gather here and paint after `ET`: path and `Do` operators may not appear
inside a text object. -/
structure TextSt where
  ops : Array TextOp := #[]
  items : Array TextItem := #[]
  font : Int := -1
  size : Sp := -1
  color : Ir.Color := Ir.Color.black
  tz : Int := 0
  x : Sp := 0
  pen : Option (Sp × Sp) := none
  rules : Array (Ir.Color × Sp × Sp × Sp × Sp) := #[]
  images : Array (Sp × Sp × Sp × Sp × Option Nat) := #[]

def TextSt.op (st : TextSt) (o : TextOp) : TextSt := { st with ops := st.ops.push o }

def TextSt.closeTJ (st : TextSt) : TextSt :=
  if st.items.isEmpty then st else { st with ops := st.ops.push (.show st.items), items := #[] }

/-- Bring the pen to a run at `(st.x, runY)`. Inside an open array with
the face unchanged, a small horizontal move is an adjustment in the live
size — thousandths of the font size times the horizontal scale, so under
expansion the number compensates by the inverse factor, and a viewer that
keeps adjustments in sixteen bits (macOS Preview drops the whole array
past ±32767) never sees one that large. Any other move is an absolute
`Tm`, and closes the array. A fresh line has no pen until its first run
sets one. -/
def adjustFor (dx size tz : Int) : Int :=
  let v0 := dx * 1000 / size
  if tz == 0 then v0 else v0 * 1000 / (1000 + tz)

def TextSt.toPen (st : TextSt) (changes : Bool) (runY : Sp) : TextSt :=
  match st.pen with
  | some (hx, hy) =>
    if hx != st.x || hy != runY then
      let v := adjustFor (st.x - hx) st.size st.tz
      if !st.items.isEmpty && !changes && hy == runY && v.natAbs ≤ 32000 then
        { st with items := st.items.push (.adjust (-v)) }
      else
        st.closeTJ.op (.move st.x runY)
    else st
  | none => st.op (.move st.x runY)

def TextSt.setFont (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp) : TextSt :=
  if st.font != (idx : Int) || st.size != size then
    { st.op (.font (remap[idx]?.getD 0) size) with font := idx, size := size }
  else st

def TextSt.setColor (st : TextSt) (color : Ir.Color) : TextSt :=
  if st.color != color then { st.op (.color color) with color := color } else st

/-- A `TJ` array cannot switch fonts or colours mid-array, so a run in a
different face or colour closes it and emits `Tf`/`rg` before reopening. -/
def TextSt.setFace (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp)
    (color : Ir.Color) : TextSt :=
  ((st.closeTJ).setFont remap idx size).setColor color

/-- One glyph run: the pen, then the face and colour when they change,
then the glyphs. A kern (a run with no glyphs) only moves the layout
position, like a gap. -/
def stepRun (remap : Array Nat) (lineSize ypdf : Sp) (st : TextSt) (idx : Nat)
    (color : Ir.Color) (w : Sp) (glyphs : Array (Nat × Char)) (segSize raise : Sp) : TextSt :=
  if glyphs.isEmpty then { st with x := st.x + w } else
  let runY := ypdf + raise
  let size := if segSize == 0 then lineSize else segSize
  let changes := st.font != (idx : Int) || st.size != size || st.color != color
  let st := st.toPen changes runY
  let st := if changes then st.setFace remap idx size color else st
  { st with items := st.items.push (.glyphs (glyphs.map (·.1))), x := st.x + w,
            pen := some (st.x + w, runY) }

def stepSeg (remap : Array Nat) (imgMap : Array (Option Nat)) (lineSize ypdf : Sp)
    (st : TextSt) : Seg → TextSt
  | .rule w thickness raise color =>
    { st with rules := st.rules.push (color, st.x, ypdf + raise, w, thickness), x := st.x + w }
  | .image idx w h =>
    { st with images := st.images.push (st.x, ypdf, w, h, idx.bind fun k => imgMap[k]?.getD none),
              x := st.x + w }
  | .gap w => { st with x := st.x + w }
  | .run idx color _ w glyphs segSize _ raise _ =>
    stepRun remap lineSize ypdf st idx color w glyphs segSize raise

/-- One line: the expansion factor when it changes (`Tz`, §9.3.4, scales
shapes and advances alike — exactly hz-style expansion, and the run
widths layout emitted are already rescaled by the same factor), then the
segments from the line's left edge with no pen, then the array closed.
The bleed shifts everything: layout works in trim coordinates and the
trim box sits `bleed` in from the medium's corner. -/
def stepLine (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat)) (st : TextSt)
    (l : LineOut) : TextSt :=
  let ypdf := geom.bleed + geom.pageH - l.y
  let st := if l.expand != st.tz then { st.op (.scale (1000 + l.expand)) with tz := l.expand }
    else st
  let st := { st with x := geom.bleed + l.x, pen := none }
  (l.segs.foldl (stepSeg remap imgMap l.size ypdf) st).closeTJ

/-- A picture path in PDF space: the circle as four cubic Bézier arcs (the
standard k = 4(√2−1)/3 ≈ 0.5523 approximation), a rectangle as `re`, an
edge's segments each opening with a move unless it continues the previous
one, a triangle closed. -/
def pathSegs (geom : Geom) : PagePath → Array PathOp
  | .circle cx cy r =>
    let x := geom.bleed + cx
    let y := geom.bleed + geom.pageH - cy
    let k := r * 5523 / 10000
    #[.moveTo (x + r) y,
      .curveTo (x + r) (y + k) (x + k) (y + r) x (y + r),
      .curveTo (x - k) (y + r) (x - r) (y + k) (x - r) y,
      .curveTo (x - r) (y - k) (x - k) (y - r) x (y - r),
      .curveTo (x + k) (y - r) (x + r) (y - k) (x + r) y,
      .close]
  | .rect rx ry rw rh => #[.rect (geom.bleed + rx) (geom.bleed + geom.pageH - ry - rh) rw rh]
  | .segs segs =>
    let pt (x y : Sp) : Sp × Sp := (geom.bleed + x, geom.bleed + geom.pageH - y)
    let step (acc : Option (Sp × Sp) × Array PathOp) (sg : Ir.Pic.PathSeg) :
        Option (Sp × Sp) × Array PathOp :=
      let (prev, out) := acc
      match sg with
      | .line x1 y1 x2 y2 =>
        let a := pt x1 y1
        let b := pt x2 y2
        let out := if prev != some a then out.push (.moveTo a.1 a.2) else out
        (some b, out.push (.lineTo b.1 b.2))
      | .cubic x1 y1 c1x c1y c2x c2y x2 y2 =>
        let a := pt x1 y1
        let c1 := pt c1x c1y
        let c2 := pt c2x c2y
        let b := pt x2 y2
        let out := if prev != some a then out.push (.moveTo a.1 a.2) else out
        (some b, out.push (.curveTo c1.1 c1.2 c2.1 c2.2 b.1 b.2))
    (segs.foldl step (none, #[])).2
  | .tri x1 y1 x2 y2 x3 y3 =>
    let pt (x y : Sp) : Sp × Sp := (geom.bleed + x, geom.bleed + geom.pageH - y)
    let a := pt x1 y1
    let b := pt x2 y2
    let c := pt x3 y3
    #[.moveTo a.1 a.2, .lineTo b.1 b.2, .lineTo c.1 c.2, .close]

def imageOp (x y w h : Sp) : Option Nat → ContentOp
  | some n => .image x y w h n
  | none => .imageMissing x y w h

/-- One page's operations: fills first, in order (the page background,
then any bars), then picture paths (a node's own fill sits under its
label), then the text object, then the images and rules the text walk
gathered. -/
def contentOps (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (page : PageOut) : Array ContentOp :=
  let fills := page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h
  let paths := page.paths.map fun p => ContentOp.path p.fill p.stroke (pathSegs geom p.path)
  let st := page.lines.foldl (stepLine geom remap imgMap) {}
  let images := st.images.map fun (x, y, w, h, res) => imageOp x y w h res
  let rules := st.rules.map fun (c, x, y, w, h) => ContentOp.fill c x y w h
  let body := (fills ++ paths).push (.text st.ops)
  (body ++ images) ++ rules

/-! ## The glyph census -/

/-- The glyph runs an item carries: a `TJ` string is one run, an
adjustment none. -/
def TextItem.runs : TextItem → List (Array Nat)
  | .glyphs gids => [gids]
  | .adjust _ => []

def TextOp.runs : TextOp → List (Array Nat)
  | .scale _ => []
  | .move _ _ => []
  | .font _ _ => []
  | .color _ => []
  | .show items => items.toList.flatMap TextItem.runs

def ContentOp.runs : ContentOp → List (Array Nat)
  | .fill _ _ _ _ _ => []
  | .path _ _ _ => []
  | .text ops => ops.toList.flatMap TextOp.runs
  | .image _ _ _ _ _ => []
  | .imageMissing _ _ _ _ => []

/-- Every glyph run a content stream paints, in stream order. -/
def runsOf (ops : Array ContentOp) : List (Array Nat) := ops.toList.flatMap ContentOp.runs

/-- The glyph run a segment ships: a run's glyph ids when it has any (a
kern is a run with none, and paints nothing). -/
def segRuns : Seg → List (Array Nat)
  | .run _ _ _ _ glyphs _ _ _ _ => if glyphs.isEmpty then [] else [glyphs.map (·.1)]
  | .gap _ => []
  | .rule _ _ _ _ => []
  | .image _ _ _ => []

/-- The shipped glyph census of a page: every run's glyphs, line by line
in segment order — what `pdftotext` reads back, before spelling. -/
def pageRuns (page : PageOut) : List (Array Nat) :=
  page.lines.toList.flatMap fun l => l.segs.toList.flatMap segRuns

/-! ## The equational theory of `render`

Every renderer above is a left fold that appends; these are the list
equations it computes, so a fact about the bytes is a fact about the
typed array. -/

/-- The general fold-with-append law under an arbitrary accumulator. -/
theorem foldl_append_acc (f : α → String) (l : List α) (acc : String) :
    l.foldl (fun s x => s ++ f x) acc = acc ++ l.foldl (fun s x => s ++ f x) "" := by
  induction l generalizing acc with
  | nil => simp [String.append_empty]
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rw [ih (acc ++ f x), ih ("" ++ f x), String.empty_append, String.append_assoc]

theorem foldl_append_eq (f : α → String) (l : List α) (acc : String) :
    l.foldl (fun s x => s ++ f x) acc = acc ++ String.join (l.map f) := by
  show l.foldl (fun s x => s ++ f x) acc = acc ++ (l.map f).foldl (fun r s => r ++ s) ""
  rw [List.foldl_map, foldl_append_acc]

/-- The stream's shape as a list equation: operations joined by newlines.
The specification `render` is proved to compute (`content_render_exact`);
`render` itself accumulates. -/
def renderList : List ContentOp → String
  | [] => ""
  | [o] => o.render
  | o :: rest => o.render ++ ("\n" ++ renderList rest)

theorem renderList_go (l : List ContentOp) (acc : String) :
    l.foldl renderStep (some acc)
      = some (match l with | [] => acc | _ :: _ => acc ++ "\n" ++ renderList l) := by
  induction l generalizing acc with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.foldl_cons, renderStep, ih]
    cases rest with
    | nil => rfl
    | cons y rest' => simp only [renderList, String.append_assoc]

/-- **The renderer computes its list specification.** The accumulating
`render` and the structural `renderList` agree on every operator array —
the equation the old string builder had no way to state, and the one a
fact about the bytes (`mark_ink_exact`, once marked content lands) reduces
to a fact about the typed array through. -/
theorem content_render_exact (ops : Array ContentOp) :
    render ops = renderList ops.toList := by
  unfold render
  rw [← Array.foldl_toList]
  cases ops.toList with
  | nil => rfl
  | cons o rest =>
    simp only [List.foldl_cons]
    rw [show renderStep none o = some o.render from rfl, renderList_go]
    cases rest with
    | nil => rfl
    | cons y rest' => simp only [renderList, Option.getD_some, String.append_assoc]

theorem text_render_exact (ops : Array TextOp) :
    (ContentOp.text ops).render = "BT\n" ++ String.join (ops.toList.map TextOp.render) ++ "ET" := by
  simp only [ContentOp.render]
  rw [← Array.foldl_toList, foldl_append_eq]

theorem show_render_exact (items : Array TextItem) :
    (TextOp.show items).render
      = "[" ++ String.join (items.toList.map TextItem.render) ++ "] TJ\n" := by
  simp only [TextOp.render]
  rw [← Array.foldl_toList, foldl_append_eq]

/-- The glyph string: the ids' hex digits between the angle brackets that
delimit a PDF hexadecimal string (ISO 32000-2 §7.3.4.3). -/
theorem glyphs_render_exact (gids : Array Nat) :
    (TextItem.glyphs gids).render
      = String.singleton '<' ++ String.join (gids.toList.map gidHex) ++ String.singleton '>' := by
  simp only [TextItem.render]
  rw [show pushGid = fun acc g => acc ++ gidHex g from funext fun _ => funext fun _ => pushGid_eq ..,
    ← Array.foldl_toList, foldl_append_eq, String.push_eq_append]
  rfl

theorem path_render_exact (fl : Option Ir.Color) (st : Option Ir.Pic.Stroke) (segs : Array PathOp) :
    (ContentOp.path fl st segs).render
      = "q " ++ fillOp fl ++ strokeOp st ++ String.join (segs.toList.map PathOp.render)
        ++ paintOp st fl ++ " Q" := by
  simp only [ContentOp.render]
  rw [← Array.foldl_toList, foldl_append_eq]
/-- The runs a walk state holds: those already in ops, then the open array's. -/
def TextSt.runs (st : TextSt) : List (Array Nat) :=
  st.ops.toList.flatMap TextOp.runs ++ st.items.toList.flatMap TextItem.runs

theorem flatMap_nil_fun (l : List α) : l.flatMap (fun (_ : α) => ([] : List β)) = [] :=
  List.flatMap_eq_nil_iff.mpr fun _ _ => rfl

theorem op_runs (st : TextSt) (o : TextOp) (h : o.runs = []) : (st.op o).runs = st.runs := by
  simp [TextSt.op, TextSt.runs, h]

theorem closeTJ_runs (st : TextSt) : st.closeTJ.runs = st.runs := by
  unfold TextSt.closeTJ
  split
  · rfl
  · simp [TextSt.runs, TextOp.runs]

theorem closeTJ_items (st : TextSt) : st.closeTJ.items = #[] := by
  unfold TextSt.closeTJ
  split
  · rename_i h
    exact Array.isEmpty_iff.mp h
  · rfl

theorem toPen_runs (st : TextSt) (c : Bool) (y : Sp) : (st.toPen c y).runs = st.runs := by
  unfold TextSt.toPen
  split
  · split
    · simp only []
      split
      · simp [TextSt.runs, TextItem.runs]
      · rw [op_runs _ _ rfl, closeTJ_runs]
    · rfl
  · rw [op_runs _ _ rfl]

theorem setFont_runs (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp) :
    (st.setFont remap idx size).runs = st.runs := by
  unfold TextSt.setFont
  split
  · exact op_runs _ _ rfl
  · rfl

theorem setColor_runs (st : TextSt) (c : Ir.Color) : (st.setColor c).runs = st.runs := by
  unfold TextSt.setColor
  split
  · exact op_runs _ _ rfl
  · rfl

theorem setFace_runs (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp) (c : Ir.Color) :
    (st.setFace remap idx size c).runs = st.runs := by
  unfold TextSt.setFace
  rw [setColor_runs, setFont_runs, closeTJ_runs]

theorem stepRun_runs (remap : Array Nat) (ls y : Sp) (st : TextSt) (idx : Nat) (c : Ir.Color)
    (w : Sp) (glyphs : Array (Nat × Char)) (ss raise : Sp) :
    (stepRun remap ls y st idx c w glyphs ss raise).runs
      = st.runs ++ (if glyphs.isEmpty then [] else [glyphs.map (·.1)]) := by
  unfold stepRun
  split
  · simp [TextSt.runs]
  · simp only []
    generalize hc : (st.font != (idx : Int) || st.size != (if ss == 0 then ls else ss)
      || st.color != c) = changes
    have key : ∀ (s : TextSt) (i : TextItem) (x' : Sp) (p' : Option (Sp × Sp)),
        TextSt.runs { s with items := s.items.push i, x := x', pen := p' } = s.runs ++ i.runs := by
      intro s i x' p'
      simp [TextSt.runs]
    rw [key]
    simp only [TextItem.runs]
    split
    · rw [setFace_runs, toPen_runs]
    · rw [toPen_runs]

theorem stepSeg_runs (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp) (st : TextSt)
    (seg : Seg) : (stepSeg remap imgMap ls y st seg).runs = st.runs ++ segRuns seg := by
  cases seg with
  | rule => simp [stepSeg, TextSt.runs, segRuns]
  | image => simp [stepSeg, TextSt.runs, segRuns]
  | gap => simp [stepSeg, TextSt.runs, segRuns]
  | run => exact stepRun_runs ..

theorem foldl_segs_runs (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp)
    (segs : List Seg) (st : TextSt) :
    (segs.foldl (stepSeg remap imgMap ls y) st).runs = st.runs ++ segs.flatMap segRuns := by
  induction segs generalizing st with
  | nil => simp
  | cons s rest ih => simp [ih, stepSeg_runs, List.append_assoc]

theorem stepLine_runs (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap st l).runs = st.runs ++ l.segs.toList.flatMap segRuns := by
  unfold stepLine
  simp only []
  rw [closeTJ_runs, ← Array.foldl_toList, foldl_segs_runs]
  congr 1
  split
  · exact op_runs _ _ rfl
  · rfl

theorem stepLine_items (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (st : TextSt) (l : LineOut) : (stepLine geom remap imgMap st l).items = #[] := by
  unfold stepLine
  exact closeTJ_items _

theorem foldl_lines_runs (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (lines : List LineOut) (st : TextSt) :
    (lines.foldl (stepLine geom remap imgMap) st).runs
      = st.runs ++ lines.flatMap (fun l => l.segs.toList.flatMap segRuns) := by
  induction lines generalizing st with
  | nil => simp
  | cons l rest ih => simp [ih, stepLine_runs, List.append_assoc]

theorem foldl_lines_items (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (lines : List LineOut) (st : TextSt) (h : st.items = #[]) :
    (lines.foldl (stepLine geom remap imgMap) st).items = #[] := by
  induction lines generalizing st with
  | nil => exact h
  | cons l rest ih => exact ih _ (stepLine_items ..)

theorem imageOp_runs (x y w h : Sp) (r : Option Nat) : (imageOp x y w h r).runs = [] := by
  cases r <;> rfl

/-- **The PDF paints every glyph run the page shipped, in order.** The glyph
census of the typed content stream is the page's run census: no run
dropped, none invented, none reordered — the `_text` fact for the
PageOut → ContentOp projection (not a `Conserves` instance: the walk
changes type, as `structTree_text` does). -/
theorem contentOps_text (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (page : PageOut) : runsOf (contentOps geom remap imgMap page) = pageRuns page := by
  unfold runsOf contentOps pageRuns
  have himg : ∀ t : Sp × Sp × Sp × Sp × Option Nat,
      ContentOp.runs (imageOp t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) = [] :=
    fun t => imageOp_runs ..
  simp only [Array.toList_append, Array.toList_push, Array.toList_map, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.flatMap_map, himg, flatMap_nil_fun]
  simp only [ContentOp.runs, flatMap_nil_fun, List.append_nil, List.nil_append]
  have hr := foldl_lines_runs geom remap imgMap page.lines.toList {}
  have hi := foldl_lines_items geom remap imgMap page.lines.toList {} rfl
  rw [Array.foldl_toList] at hr hi
  simp only [TextSt.runs, hi] at hr
  simpa using hr
theorem hexDigit_inj : ∀ a, a < 16 → ∀ b, b < 16 → hexDigit a = hexDigit b → a = b := by
  decide

theorem hexDigit_mod (a : Nat) : hexDigit a = hexDigit (a % 16) := by
  simp [hexDigit]

theorem hexDigit_eq_mod {a b : Nat} (h : hexDigit a = hexDigit b) : a % 16 = b % 16 := by
  rw [hexDigit_mod a, hexDigit_mod b] at h
  exact hexDigit_inj _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) h

theorem gidHex_toList (g : Nat) :
    (gidHex g).toList
      = [hexDigit (g / 4096), hexDigit (g / 256), hexDigit (g / 16), hexDigit g] := by
  simp [gidHex, pushGid, String.toList_push]

/-- A glyph id in the Identity-H range is recoverable from its four hex
digits: the spelling is injective below 65536 (above it, the leading
digits wrap — the honest bound). -/
theorem gidHex_inj {g₁ g₂ : Nat} (h₁ : g₁ < 65536) (h₂ : g₂ < 65536)
    (h : gidHex g₁ = gidHex g₂) : g₁ = g₂ := by
  have hl := congrArg String.toList h
  rw [gidHex_toList, gidHex_toList] at hl
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨e1, e2, e3, e4⟩ := hl
  have := hexDigit_eq_mod e1
  have := hexDigit_eq_mod e2
  have := hexDigit_eq_mod e3
  have := hexDigit_eq_mod e4
  omega

theorem join_cons (a : String) (as : List String) :
    String.join (a :: as) = a ++ String.join as := by
  unfold String.join
  simp only [List.foldl_cons]
  have := foldl_append_acc (fun x : String => x) as ("" ++ a)
  simp only [String.empty_append] at this
  exact this

theorem join_gidHex_inj : ∀ (l₁ l₂ : List Nat), (∀ g ∈ l₁, g < 65536) → (∀ g ∈ l₂, g < 65536) →
    String.join (l₁.map gidHex) = String.join (l₂.map gidHex) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => by
    have := congrArg String.toList h
    simp [String.toList_append, gidHex_toList] at this
  | x :: _, [], _, _, h => by
    have := congrArg String.toList h
    simp [String.toList_append, gidHex_toList] at this
  | x :: r₁, y :: r₂, h₁, h₂, h => by
    have hl := congrArg String.toList h
    simp only [List.map_cons, join_cons, String.toList_append] at hl
    have hlen : (gidHex x).toList.length = (gidHex y).toList.length := by
      simp [gidHex_toList]
    obtain ⟨hx, hr⟩ := List.append_inj hl hlen
    have hxy := gidHex_inj (h₁ x (by simp)) (h₂ y (by simp)) (String.ext hx)
    have hrest := join_gidHex_inj r₁ r₂ (fun g hg => h₁ g (by simp [hg]))
      (fun g hg => h₂ g (by simp [hg])) (String.ext hr)
    rw [hxy, hrest]

/-- **The glyph string is injective on Identity-H ids.** Two `TJ` glyph
items that spell the same carry the same ids, when every id is below
65536 — the strongest injectivity the stream honestly has: `render`
itself is not injective (`render_not_inj`). -/
theorem glyphs_inj {a b : Array Nat} (ha : ∀ g ∈ a, g < 65536) (hb : ∀ g ∈ b, g < 65536)
    (h : (TextItem.glyphs a).render = (TextItem.glyphs b).render) : a = b := by
  rw [glyphs_render_exact, glyphs_render_exact] at h
  have h := (String.append_left_inj _).mp h
  have h := (String.append_right_inj _).mp h
  exact Array.toList_inj.mp (join_gidHex_inj _ _ (fun g hg => ha g (Array.mem_toList_iff.mp hg))
    (fun g hg => hb g (Array.mem_toList_iff.mp hg)) h)

/-- `render` is not injective: a page fill and a fill-only rectangle path
spell the same operators (as they must — one `re f` is one `re f`), so no
theorem may read an operator array back from its bytes. Every fact about
what the stream carries is stated over the typed array. -/
theorem render_not_inj : ∃ a b : Array ContentOp, a ≠ b ∧ render a = render b :=
  ⟨#[.fill Ir.Color.black 0 0 1 1], #[.path (some Ir.Color.black) none #[.rect 0 0 1 1]],
    fun h => by have := congrArg (·[0]?) h; simp at this, rfl⟩

end LeanTex.Core.Pdf
