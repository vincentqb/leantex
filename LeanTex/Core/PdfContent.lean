module

public import LeanTex.Core.Dim
public import LeanTex.Core.Layout
public import LeanTex.Core.PdfOps
public import LeanTex.Core.GfxPdf

/-!
# PDF content streams as typed operators

A page's content stream is built as an `Array ContentOp` — one constructor
per painting operator the writer emits — and rendered by `render`, a pure
serializer with an equational theory (`render_lines_exact` and its
per-constructor twins). The construction (`contentOps`) is the layout
walk that decides pen moves, `TJ` arrays, and graphics-state changes; the
rendering is spelling only. Marked content (`BDC`/`BMC` … `EMC`) is one
constructor, `marked (tag) (body)`, on both the text object's operators
and the page's: an ill-nested pair is unrepresentable, the body's ink is
what it was (`mark_ink_exact`), and `render` opens and closes each
sequence on lines of its own (`render_lines_exact`), so the stream with
those lines removed is the stream of the unwrapped operators.
-/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Layout

/-- One hexadecimal digit of `n`'s low nibble, upper case. -/
public def hexDigit (n : Nat) : Char :=
  match n % 16 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'A' | 11 => 'B' | 12 => 'C' | 13 => 'D' | 14 => 'E' | _ => 'F'

/-- `acc` with a glyph id's four hex digits pushed — the digits an
Identity-H CID string spells (ISO 32000-2 §9.7.4.2: two bytes per CID).
Pushing in place is the hot path (every glyph on every page); `gidHex` is
its four-character value, `pushGid_eq` the equation between them. -/
private def pushGid (acc : String) (g : Nat) : String :=
  (((acc.push (hexDigit (g / 4096))).push (hexDigit (g / 256))).push (hexDigit (g / 16))).push
    (hexDigit g)

public def gidHex (g : Nat) : String := pushGid "" g

private theorem pushGid_eq (acc : String) (g : Nat) : pushGid acc g = acc ++ gidHex g := by
  simp only [pushGid, gidHex, String.push_eq_append, String.empty_append, String.append_assoc]

/-- The line that opens the sequence: the tag and its property dictionary
before `BDC` (Table 352), or the tag alone before `BMC` when there are no
properties to give (§14.6.1 — `BDC` takes two operands; a bare tag before
it is a syntax error on which a reader drops the rest of the page). Closed
literals: the opener is spelled once per rule and once per fill group on
every page. -/
public def MarkTag.opener : MarkTag → String
  | .artifact none => "/Artifact BMC"
  | .artifact (some .pagination) => "/Artifact << /Type /Pagination >> BDC"
  | .artifact (some .layout) => "/Artifact << /Type /Layout >> BDC"
  | .artifact (some .page) => "/Artifact << /Type /Page >> BDC"
  | .content s mcid _ => s!"/{s} << /MCID {mcid} >> BDC"

/-- What a line's ink stands for, read off the layout: running furniture;
a structure leaf, under the structure type the structure walk gave the
element holding that leaf; or ink no leaf owns (a rules-only line, the
generated heading of an abstract), which is an artifact of no stated
type. Decided once per line and once per image — the origin is known at
the line and lost after. -/
public inductive Origin where
  | furniture
  | unattributed
  | leaf (k : Nat) (tag : String)
  deriving Repr, BEq, Inhabited

/-- A line's origin: `tags` is the structure walk's answer per leaf id
(`PdfStruct.leafTags`), `none` for a leaf no element holds. -/
public def Origin.of (tags : Array (Option String)) (l : LineOut) : Origin :=
  if l.furniture then .furniture else
  match l.leaf with
  | some k =>
    match (tags[k]?).join with
    | some s => .leaf k s
    | none => .unattributed
  | none => .unattributed

/-- The tag an origin's operators sit under. The marked-content identifier
is a placeholder here: `numberMarks` assigns them in stream order once the
page's operators are all built. -/
public def Origin.mark : Origin → MarkTag
  | .furniture => .artifact (some .pagination)
  | .unattributed => .artifact none
  | .leaf k tag => .content tag 0 k

public def PathOp.render : PathOp → String
  | .moveTo x y => s!"{x.toPtString} {y.toPtString} m "
  | .lineTo x y => s!"{x.toPtString} {y.toPtString} l "
  | .curveTo x1 y1 x2 y2 x3 y3 =>
    s!"{x1.toPtString} {y1.toPtString} {x2.toPtString} {y2.toPtString} \
{x3.toPtString} {y3.toPtString} c "
  | .close => "h "
  | .rect x y w h => s!"{x.toPtString} {y.toPtString} {w.toPtString} {h.toPtString} re "

public def TextItem.render : TextItem → String
  | .glyphs gids => (gids.foldl pushGid "<").push '>'
  | .kerned gids nums => Id.run do
    let mut s := "<"
    for h : i in [0:gids.size] do
      let n := nums.getD i 0
      if n != 0 then s := ((s.push '>') ++ toString n).push '<'
      s := pushGid s gids[i]
    return s.push '>'
  | .adjust d => toString d

mutual

/-- One text operator, without its line end: the text object and a marked
sequence each put every operator on a line of its own. -/
public def TextOp.render : TextOp → String
  | .scale p => s!"{p / 10}.{p % 10} Tz"
  | .move x y => s!"1 0 0 1 {x.toPtString} {y.toPtString} Tm"
  | .font res size => s!"/F{res + 1} {size.toPtString} Tf"
  | .color c => c.pdfFill
  | .show items => (items.foldl (fun acc it => acc ++ it.render) "[") ++ "] TJ"
  | .marked t body => TextOp.renderLines (t.opener ++ "\n") body.toList ++ "EMC"

/-- The operators onto `acc`, each followed by its line end. -/
private def TextOp.renderLines (acc : String) : List TextOp → String
  | [] => acc
  | o :: rest => TextOp.renderLines (acc ++ o.render ++ "\n") rest

end

/-- A paint set for filling: a device colour's operator, or the pattern
colour space and a shading pattern (§8.6.6.2, §8.7.3). -/
private def pdfPaintFill : PdfPaint → String
  | .solid c => c.pdfFill
  | .pattern res _ => s!"/Pattern cs /P{res + 1} scn"

private def pdfPaintStroke : PdfPaint → String
  | .solid c => c.pdfStroke
  | .pattern res _ => s!"/Pattern CS /P{res + 1} SCN"

/-- Line caps and joins as `J`/`j` operands (§8.4.3.3–4). -/
private def capCode : Gfx.Cap → Nat
  | .butt => 0
  | .round => 1
  | .square => 2

private def joinCode : Gfx.Join → Nat
  | .miter => 0
  | .round => 1
  | .bevel => 2

/-- A dash pattern, §8.4.3.6: the array in points, then the phase. -/
private def dashSpelling (d : Array Sp) (p : Sp) : String :=
  "[" ++ " ".intercalate (d.toList.map Sp.toPtString) ++ "] " ++ p.toPtString ++ " d "

private def fillState : Option PaintFill → String
  | some f => pdfPaintFill f.paint ++ " "
  | none => ""

/-- A stroke's state: its paint and width always, then what differs from
the initial graphics state — caps, joins, the miter limit, the dash. -/
private def strokeState : Option PaintStroke → String
  | some st =>
    s!"{pdfPaintStroke st.paint} {st.width.toPtString} w " ++
      (match st.cap with
       | some c => s!"{capCode c} J "
       | none => "") ++
      (match st.join with
       | some j => s!"{joinCode j} j "
       | none => "") ++
      (match st.miter with
       | some r => s!"{ratDecimal r} M "
       | none => "") ++
      (match st.dash with
       | some (d, p) => dashSpelling d p
       | none => "")
  | none => ""

private def gsState : Option ExtG → String
  | some g => s!"/GS{g.res + 1} gs "
  | none => ""

/-- The path-painting operator the declared paints select (§8.5.3, Table
60): `B` fills then strokes, `S` strokes, `f` fills, `n` ends the path
without painting; a star fills by the even–odd rule. -/
private def paintOp : Option PaintFill → Option PaintStroke → String
  | some f, some _ => if f.evenOdd then "B*" else "B"
  | none, some _ => "S"
  | some f, none => if f.evenOdd then "f*" else "f"
  | none, none => "n"

/-- The operator a stamp form's outline paints with (§8.5.3, Table 60), by
the paints it names and its fill rule. -/
private def outlineOp : Option Gfx.Rule → Bool → String
  | some .nonzero, true => "B"
  | some .evenOdd, true => "B*"
  | none, true => "S"
  | some .nonzero, false => "f"
  | some .evenOdd, false => "f*"
  | none, false => "n"

/-- A saved state's opening line: `q`, the matrix, the alphas, each clip
path with its rule. -/
public def groupHeader (m : Option Gfx.Affine) (gs : Option ExtG)
    (clips : Array (Array PathOp × Gfx.Rule)) : String :=
  let cm := match m with
    | some mm => " " ++ mm.operands ++ " cm"
    | none => ""
  let gsS := match gs with
    | some g => s!" /GS{g.res + 1} gs"
    | none => ""
  let clipS := String.join (clips.toList.map fun c =>
    let rule := match c.2 with
      | .nonzero => "W n"
      | .evenOdd => "W* n"
    " " ++ String.join (c.1.toList.map PathOp.render) ++ rule)
  "q" ++ cm ++ gsS ++ clipS

/-- An XObject's name: a figure raster `/Ri`, a form `/Fm`. -/
private def xobjectName (res : Nat) : XKind → String
  | .raster _ => s!"/Ri{res + 1}"
  | .symbol => s!"/Fm{res + 1}"
  | .group => s!"/Fm{res + 1}"
  | .stamp _ _ _ => s!"/Fm{res + 1}"

/-- The state a stamp's instance sets for its form to paint with: its
alphas, its fill colour, its stroke's colour and parameters. -/
private def xobjectState : XKind → String
  | .stamp fp sp gs =>
    gsState gs ++
      (match fp with
       | some p => pdfPaintFill p ++ " "
       | none => "") ++ (strokeState sp)
  | .raster _ => ""
  | .symbol => ""
  | .group => ""

mutual

public def ContentOp.render : ContentOp → String
  | .fill c x y w h =>
    s!"q {c.pdfFill} {x.toPtString} {y.toPtString} {w.toPtString} {h.toPtString} re f Q"
  | .paint fl st gs segs =>
    let head := "q " ++ gsState gs ++ fillState fl ++ (strokeState st)
    let body := segs.foldl (fun acc seg => acc ++ seg.render) head
    body ++ paintOp fl st ++ " Q"
  | .text ops => (ops.foldl (fun acc op => acc ++ op.render ++ "\n") "BT\n") ++ "ET"
  | .image x y w h res =>
    s!"q {w.toPtString} 0 0 {h.toPtString} {x.toPtString} {y.toPtString} cm /Im{res + 1} Do Q"
  | .imageMissing x y w h =>
    -- A neutral grey hairline box: the failure is visible where the figure
    -- would stand, and the diagnostic already said why.
    s!"q 0.62 0.62 0.66 RG 0.75 w {x.toPtString} {y.toPtString} {w.toPtString} \
{h.toPtString} re S Q"
  | .marked t body => ContentOp.renderLines (t.opener ++ "\n") body.toList ++ "EMC"
  | .group m gs clips body => ContentOp.renderLines (groupHeader m gs clips ++ "\n") body.toList ++ "Q"
  | .shade res _ => s!"/Sh{res + 1} sh"
  | .outline fl st segs =>
    let op := outlineOp fl st
    segs.foldl (fun acc seg => acc ++ seg.render) "" ++ op
  | .xobject m res kind _ =>
    let cm := match m with
      | some mm => " " ++ mm.operands ++ " cm"
      | none => ""
    "q" ++ cm ++ " " ++ xobjectState kind ++ xobjectName res kind ++ " Do Q"

/-- The operations onto `acc`, each followed by its line end. -/
private def ContentOp.renderLines (acc : String) : List ContentOp → String
  | [] => acc
  | o :: rest => ContentOp.renderLines (acc ++ o.render ++ "\n") rest

end

/-- One step of `render`: the first operation opens the stream, every
later one follows a newline. -/
private def renderStep : Option String → ContentOp → Option String
  | none, op => some op.render
  | some s, op => some (s ++ "\n" ++ op.render)

/-- The stream: operations one per line. -/
public def render (ops : Array ContentOp) : String := (ops.foldl renderStep none).getD ""

/-! ## Construction: the layout walk -/

/-- An image the text walk gathered for painting after `ET`: its box, its
XObject resource when it loaded, and the origin of the line it stood in
— a loaded image is real content under its line's leaf, a furniture
line's image (a logo) a pagination artifact. -/
public structure ImgOut where
  x : Sp
  y : Sp
  w : Sp
  h : Sp
  res : Option Nat
  origin : Origin
  deriving Repr, BEq, Inhabited

/-- A glyph's advance as the file states it: its `hmtx` width in
millionths of the em, rounded to the nearest — what the `/W` array spells,
to three decimals of a thousandth, and so the width a viewer's pen
advances by (`TextSt.widths`). Exact in thousandths for a face on a
1000-unit em; to 5·10⁻⁷ em otherwise, where whole thousandths would drift
the pen up to one per glyph. -/
private def widthμOf (upem units : Nat) : Int := ((units * 1000000 + upem / 2) / upem : Nat)

public def pdfWidthμ (font : Font.Font) (g : Nat) : Int :=
  widthμOf font.unitsPerEm (font.widths[g]?.getD 0)

/-- The embedded faces' `pdfWidthμ` widths, by layout face index (`keep`,
the faces the file embeds; any other face ships no glyph): the writer's
pen reads one width per glyph shipped, so they are tabled once per
document — by the same `widthμOf` — and read by index with a `0` past a
face's last glyph, as `pdfWidthμ` answers there. -/
public def widthTable (fonts : Array Font.Font) (keep : Array Nat) : Array (Array Int) :=
  fonts.mapIdx fun k f => if keep.contains k then f.widths.map (widthμOf f.unitsPerEm) else #[]


/-- The viewer's pen inside the open `TJ` array, as the writer computes it
from what it wrote (§9.4.4): `xm` the x the array's `Tm` spells, in
thousandths of a point (`Sp.toPtMilli`, the value a reader parses back),
`y` the baseline it spells, and `adv` the advance since then in millionths
of the text size — each glyph adds its `/W` width in that unit, each `TJ`
number `n` subtracts `1000 n`. The horizontal scale multiplies both terms
alike, so it enters only where a layout length is converted
(`penTarget`). -/
public structure Pen where
  xm : Int
  y : Sp
  adv : Int
  deriving Repr, BEq, Inhabited

/-- The text object's walk state. `items` is the open `TJ` array — empty
exactly when no array is open. `font` is the layout face index in force
(`-1` before the first `Tf`), `size` and `color` likewise; `tz` the live
expansion in per-mille delta from 100 %; `x` the layout position; `pen`
where the viewer's pen is (`Pen`), once a `Tm` has set it; `widths` each
face's `/W` widths in millionths of the em, by layout face index and glyph
id (`widthTable`) — what the file tells the viewer, and so what the pen
advances by. Rules and
images gather here and paint after `ET`: path and `Do` operators may not
appear inside a text object. -/
public structure TextSt where
  ops : Array TextOp := #[]
  items : Array TextItem := #[]
  font : Int := -1
  size : Sp := -1
  color : Ir.Color := Ir.Color.black
  tz : Int := 0
  x : Sp := 0
  pen : Option Pen := none
  widths : Array (Array Int) := #[]
  rules : Array (Ir.Color × Sp × Sp × Sp × Sp) := #[]
  /-- The filled polygons the lines carried (a formula's cancel marks), in
  page coordinates: layout ink like the rules, painted with them. -/
  polys : Array (Ir.Color × Array (Sp × Sp)) := #[]
  images : Array ImgOut := #[]

private def TextSt.op (st : TextSt) (o : TextOp) : TextSt := { st with ops := st.ops.push o }

private def TextSt.closeTJ (st : TextSt) : TextSt :=
  if st.items.isEmpty then st else { st with ops := st.ops.push (.show st.items), items := #[] }

/-- `num / den` rounded to the nearest integer, half away from zero, the
numerator given as a sign and a magnitude: every product the pen's
conversions round is formed in `Nat`, where a value below 2⁶³ is a machine
word — an `Int` past 2³¹ is a heap number, and these run once per glyph. -/
@[inline] private def roundDiv (neg : Bool) (num den : Nat) : Int :=
  if den == 0 then 0 else
    let q : Nat := (2 * num + den) / (2 * den)
    if neg then -(q : Int) else q

/-- A layout x as the pen advance that reaches it, in the pen's unit:
`(x − Tm) / (size · scale)` in millionths, with the `Tm` x and the size as
the file spells them (`xm`, `sm`: thousandths of a point) and the scale
`1000 + tz` per mille, rounded to the nearest millionth — that is,
`(1000·x − 65536·xm) · 1953125 / (128 · sm · (1000 + tz))`, since
10⁹ / 65536 = 1953125 / 128; the difference is split into its positive and
negative parts so it is formed as a magnitude (`roundDiv`). -/
private def penTarget (sm tz xm : Int) (x : Sp) : Int :=
  let den : Nat := 128 * sm.toNat * (1000 + tz).toNat
  let pos : Nat := 1000 * x.toNat + 65536 * (-xm).toNat
  let neg : Nat := 65536 * xm.toNat + 1000 * (-x).toNat
  if neg ≤ pos then roundDiv false ((pos - neg) * 1953125) den
  else roundDiv true ((neg - pos) * 1953125) den

/-- A laid-out advance `P` from a run's start as the pen advance it needs,
in millionths of the size the file spells (`sm`): `P · 1953125 / (128 · sm)`,
rounded. The line's expansion cancels out of it — the layout scales the run
by the factor the viewer scales the pen by. -/
@[inline] private def runOffset (sm : Int) (P : Sp) : Int :=
  roundDiv (P < 0) (P.natAbs * 1953125) (128 * sm.natAbs)

/-- The `TJ` number that brings a pen standing `d` millionths past its
target (short of it when negative) to within half a thousandth: `d / 1000`
rounded to the nearest integer, half up — zero exactly when the pen is
already that close. -/
@[inline] public def nudge (d : Int) : Int := (d + 500) / 1000

/-- **A nudged pen stands within half a thousandth of the em of its
target.** Whatever the distance `d`, the residue `d − 1000 · nudge d` lies
in `[−500, 499]` millionths: the resolution of a `TJ` number, and nothing
more. -/
public theorem nudge_between (d : Int) :
    -500 ≤ d - 1000 * nudge d ∧ d - 1000 * nudge d ≤ 499 := by
  unfold nudge
  omega

/-- An absolute move: the open array closed, `Tm` at the layout x and
`runY`, and the pen restarted at the x the `Tm` spells. -/
private def TextSt.moveTo (st : TextSt) (runY : Sp) : TextSt :=
  { st.closeTJ.op (.move st.x runY) with
    pen := some { xm := st.x.toPtMilli, y := runY, adv := 0 } }

/-- Bring the pen to a run at `(st.x, runY)`. Inside an open array with
the face unchanged and the baseline the same, the move is the number that
puts the viewer's pen within half a thousandth of the em of the layout's
x (`nudge`, measured from where the file's own arithmetic left it), unless
that number exceeds ±32000 — a viewer that keeps adjustments in sixteen
bits (macOS Preview drops the whole array past ±32767) never sees one that
large. Any other move is an absolute `Tm` (`moveTo`), which closes the
array: a face or size change re-bases the pen, whose unit is the size. A
fresh line has no pen until its first run sets one. -/
private def TextSt.toPen (st : TextSt) (changes : Bool) (runY : Sp) : TextSt :=
  match st.pen with
  | some p =>
    let n := nudge (p.adv - penTarget st.size.toPtMilli st.tz p.xm st.x)
    if !st.items.isEmpty && !changes && p.y == runY && n.natAbs ≤ 32000 then
      if n == 0 then st
      else { st with items := st.items.push (.adjust n),
                     pen := some { p with adv := p.adv - 1000 * n } }
    else st.moveTo runY
  | none => st.moveTo runY

private def TextSt.setFont (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp) : TextSt :=
  if st.font != (idx : Int) || st.size != size then
    { st.op (.font (remap[idx]?.getD 0) size) with font := idx, size := size }
  else st

private def TextSt.setColor (st : TextSt) (color : Ir.Color) : TextSt :=
  if st.color != color then { st.op (.color color) with color := color } else st

/-- A `TJ` array cannot switch fonts or colours mid-array, so a run in a
different face or colour closes it and emits `Tf`/`rg` before reopening. -/
private def TextSt.setFace (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp)
    (color : Ir.Color) : TextSt :=
  ((st.closeTJ).setFont remap idx size).setColor color

/-- A run's string being placed: its glyph ids, their numbers beside
them, the pen (`Pen.adv`'s unit) and the laid-out advance `P` reached. One
record of scalars and scalar arrays, updated in place — a nested tuple
would cost the loop three allocations a glyph. -/
public structure PlaceSt where
  gids : Array Nat
  nums : Array Int
  adv : Int
  P : Sp

/-- One glyph of a run onto its string: the number that brings the pen
from where the previous glyph's `/W` width left it to `tgt P` — the
glyph's layout position, `P` its laid-out advance from the run's start —
then the glyph and its own width. -/
@[inline] public def placeStep (wμ : Nat → Int) (tgt : Sp → Int) (st : PlaceSt) :
    Nat × Char × Sp → PlaceSt
  | (g, _, a) =>
    let n := nudge (st.adv - tgt st.P)
    ⟨st.gids.push g, st.nums.push n, st.adv - 1000 * n + wμ g, st.P + a⟩

/-- `placeStep`'s string as a list: each glyph with the number set before
it, from pen `adv` at laid-out advance `P`. -/
public def placeSpec (wμ : Nat → Int) (tgt : Sp → Int) :
    Int → Sp → List (Nat × Char × Sp) → List (Nat × Int)
  | _, _, [] => []
  | adv, P, (g, _, a) :: rest =>
    let n := nudge (adv - tgt P)
    (g, n) :: placeSpec wμ tgt (adv - 1000 * n + wμ g) (P + a) rest

/-- Where a viewer's pen stands as each glyph of a kerned string begins,
from pen `p` — §9.4.4's arithmetic, the number first, then the glyph's
width — whatever chose the numbers. -/
public def penStarts (wμ : Nat → Int) : Int → List (Nat × Int) → List Int
  | _, [] => []
  | p, (g, n) :: rest => (p - 1000 * n) :: penStarts wμ (p - 1000 * n + wμ g) rest

/-- Each glyph's laid-out advance from the run's start. -/
public def glyphStarts : Sp → List (Nat × Char × Sp) → List Sp
  | _, [] => []
  | P, (_, _, a) :: rest => P :: glyphStarts (P + a) rest

/-- The fold builds `placeSpec`'s string: its glyph ids, and beside them
its numbers. -/
public theorem placeStep_fold_exact (wμ : Nat → Int) (tgt : Sp → Int) (gs : List (Nat × Char × Sp))
    (ga : Array Nat) (na : Array Int) (adv : Int) (P : Sp) :
    (gs.foldl (placeStep wμ tgt) ⟨ga, na, adv, P⟩).gids.toList
        = ga.toList ++ (placeSpec wμ tgt adv P gs).map (·.1)
      ∧ (gs.foldl (placeStep wμ tgt) ⟨ga, na, adv, P⟩).nums.toList
        = na.toList ++ (placeSpec wμ tgt adv P gs).map (·.2) := by
  induction gs generalizing ga na adv P with
  | nil => simp [placeSpec]
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp only [List.foldl_cons, placeStep, placeSpec]
    obtain ⟨h1, h2⟩ := ih (ga.push g) (na.push (nudge (adv - tgt P)))
      (adv - 1000 * nudge (adv - tgt P) + wμ g) (P + a)
    exact ⟨by rw [h1]; simp, by rw [h2]; simp⟩

public theorem placeSpec_glyphs_id (wμ : Nat → Int) (tgt : Sp → Int) (gs : List (Nat × Char × Sp))
    (adv : Int) (P : Sp) : (placeSpec wμ tgt adv P gs).map (·.1) = gs.map (·.1) := by
  induction gs generalizing adv P with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp [placeSpec, ih]

/-- Placing a run keeps its glyphs, in order: only numbers are added. -/
public theorem place_glyphs_id (wμ : Nat → Int) (tgt : Sp → Int) (glyphs : Array (Nat × Char × Sp))
    (adv : Int) : (glyphs.foldl (placeStep wμ tgt) ⟨#[], #[], adv, 0⟩).gids = glyphs.map (·.1) := by
  apply Array.toList_inj.mp
  rw [Array.toList_map, ← Array.foldl_toList, (placeStep_fold_exact ..).1]
  simpa using placeSpec_glyphs_id wμ tgt glyphs.toList adv 0

/-- The numbers the fold writes are `placeSpec`'s, the ones `place_between`
places by. -/
public theorem place_nums_exact (wμ : Nat → Int) (tgt : Sp → Int) (glyphs : Array (Nat × Char × Sp))
    (adv : Int) : (glyphs.foldl (placeStep wμ tgt) ⟨#[], #[], adv, 0⟩).nums.toList
      = (placeSpec wμ tgt adv 0 glyphs.toList).map (·.2) := by
  rw [← Array.foldl_toList, (placeStep_fold_exact ..).2]
  simp

public theorem placeSpec_length_exact (wμ : Nat → Int) (tgt : Sp → Int) (gs : List (Nat × Char × Sp))
    (adv : Int) (P : Sp) : (penStarts wμ adv (placeSpec wμ tgt adv P gs)).length = gs.length := by
  induction gs generalizing adv P with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp [placeSpec, penStarts, ih]

public theorem glyphStarts_length_exact (P : Sp) (gs : List (Nat × Char × Sp)) :
    (glyphStarts P gs).length = gs.length := by
  induction gs generalizing P with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp [glyphStarts, ih]

/-- **Every glyph a run paints starts where the layout put it**, to the
resolution of the file: by the viewer's own arithmetic over the numbers
`placeStep` writes and the widths the file declares (`penStarts`), each
glyph's pen stands within `[−500, 499]` millionths of the em — under half
a thousandth — of its target, the layout's position for it (both lists
hold one entry per glyph: `placeSpec_length_exact`,
`glyphStarts_length_exact`). The written advances are the laid-out
advances, pair kerns included; and since each number is chosen from where
the file's arithmetic actually left the pen, the residue never accumulates
along a line. -/
public theorem place_between (wμ : Nat → Int) (tgt : Sp → Int) (adv : Int) (P : Sp)
    (gs : List (Nat × Char × Sp)) :
    ∀ d ∈ List.zipWith (· - ·) (penStarts wμ adv (placeSpec wμ tgt adv P gs))
        ((glyphStarts P gs).map tgt), -500 ≤ d ∧ d ≤ 499 := by
  induction gs generalizing adv P with
  | nil => simp [placeSpec, penStarts]
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp only [placeSpec, penStarts, glyphStarts, List.map_cons, List.zipWith_cons_cons,
      List.mem_cons]
    rintro d (rfl | hd)
    · have := nudge_between (adv - tgt P)
      omega
    · exact ih _ _ d hd

/-- A run's string: plain when no glyph needed a number, kerned otherwise. -/
private def runItem (gids : Array Nat) (nums : Array Int) : TextItem :=
  if nums.all (· == 0) then .glyphs gids else .kerned gids nums

/-- A placed run onto the open array: its string, the layout x past its
width, and the pen where the file's arithmetic left it. -/
private def TextSt.pushRun (st : TextSt) (item : TextItem) (w : Sp) (pen : Pen) : TextSt :=
  { st with items := st.items.push item, x := st.x + w, pen := some pen }

/-- One glyph run: the pen, then the face and colour when they change,
then the glyphs, each placed where the layout put it (`placeStep`): a
glyph's layout position is the run's x plus its laid-out advance from the
run's start — the pair kerns the layout applied included — under the
line's expansion as the layout scaled the run (`w + w·f/1000`). The pen
the file's arithmetic reaches is where every later move is measured from.
A kern (a run with no glyphs) only moves the layout position, like a gap. -/
private def stepRun (remap : Array Nat) (lineSize ypdf : Sp) (st : TextSt) (idx : Nat)
    (color : Ir.Color) (w : Sp) (glyphs : Array (Nat × Char × Sp)) (segSize raise : Sp) :
    TextSt :=
  if glyphs.isEmpty then { st with x := st.x + w } else
  let runY := ypdf + raise
  let size := if segSize == 0 then lineSize else segSize
  let changes := st.font != (idx : Int) || st.size != size || st.color != color
  let st := st.toPen changes runY
  let st := if changes then st.setFace remap idx size color else st
  let p := st.pen.getD { xm := st.x.toPtMilli, y := runY, adv := 0 }
  let sm := st.size.toPtMilli
  let t0 := penTarget sm st.tz p.xm st.x
  let wf := st.widths.getD idx #[]
  -- Sized once: grown by doubling, these arrays' freed halves left the page
  -- renderer to fresh allocator pages, and rendering took twice as long.
  let r := glyphs.foldl (placeStep (wf.getD · 0) (fun P => t0 + runOffset sm P))
    ⟨Array.mkEmpty glyphs.size, Array.mkEmpty glyphs.size, p.adv, 0⟩
  st.pushRun (runItem r.gids r.nums) w { p with adv := r.adv }

private def stepSeg (remap : Array Nat) (imgMap : Array (Option Nat)) (lineSize ypdf : Sp)
    (og : Origin) (st : TextSt) : Seg → TextSt
  | .rule w thickness raise color | .decoration _ w thickness raise color =>
    { st with rules := st.rules.push (color, st.x, ypdf + raise, w, thickness), x := st.x + w }
  | .poly pts color =>
    { st with polys := st.polys.push (color, pts.map fun (px, py) => (st.x + px, ypdf + py)) }
  | .image idx w h =>
    { st with images := st.images.push { x := st.x, y := ypdf, w, h,
                                         res := idx.bind fun k => imgMap[k]?.getD none,
                                         origin := og },
              x := st.x + w }
  | .gap w _ | .decoratedGap w _ _ => { st with x := st.x + w }
  | .run idx color _ w glyphs segSize _ _ raise _ _ =>
    stepRun remap lineSize ypdf st idx color w glyphs segSize raise

/-- One line's operators, walked from a state whose `ops` are empty: the
expansion factor when it changes (`Tz`, §9.3.4, scales shapes and
advances alike — exactly hz-style expansion, and the run widths layout
emitted are already rescaled by the same factor), then the segments from
the line's left edge with no pen, then the array closed. The result's
`ops` are the line's own, for `stepLine` to append or to wrap; the images
it gathers carry the line's origin. The bleed shifts everything: layout
works in trim coordinates and the trim box sits `bleed` in from the
medium's corner. -/
private def lineSt (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat)) (og : Origin)
    (st : TextSt) (l : LineOut) : TextSt :=
  let ypdf := geom.bleed + geom.pageH - l.y
  let st : TextSt := { st with ops := #[] }
  let st := if l.expand != st.tz then { st.op (.scale (1000 + l.expand)) with tz := l.expand }
    else st
  let st := { st with x := geom.bleed + l.x, pen := none }
  (l.segs.foldl (stepSeg remap imgMap l.size ypdf og) st).closeTJ

/-- A polygon's path: to its first point, a line to each next, closed. -/
private def polyPath (pts : Array (Sp × Sp)) : Array PathOp :=
  match pts.toList with
  | [] => #[]
  | (x, y) :: rest =>
    (rest.foldl (fun acc (x, y) => acc.push (.lineTo x y)) #[.moveTo x y]).push .close

/-- A line's polygon as the operator that fills it. -/
private def polyOp (p : Ir.Color × Array (Sp × Sp)) : ContentOp :=
  .paint (some { paint := .solid p.1, evenOdd := false }) none none (polyPath p.2)

/-- The tag every furniture line's operators sit under: running heads,
feet and page numbers are pagination artifacts (Table 363). -/
private def furnitureTag : MarkTag := .artifact (some .pagination)

/-- One line onto the text object, under the wrapper its origin names: a
furniture line's operators as one pagination artifact; a line painting a
structure leaf as one marked-content sequence of that leaf's structure
type (identifier assigned later by `numberMarks`); a line no leaf owns as
one artifact of no type. A line whose operators are empty (an image-only
line, whose ink paints after `ET`) adds nothing — a sequence around
nothing would be an identifier with no content. A furniture line is
wrapped whatever it holds: the furniture census counts lines. -/
public def stepLine (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) : TextSt :=
  let og := Origin.of tags l
  let s := lineSt geom remap imgMap og st l
  match og with
  | .furniture => { s with ops := st.ops.push (.marked furnitureTag s.ops) }
  | .unattributed =>
    { s with ops := if s.ops.isEmpty then st.ops else st.ops.push (.marked (.artifact none) s.ops) }
  | .leaf k tag =>
    { s with ops := if s.ops.isEmpty then st.ops
                    else st.ops.push (.marked (.content tag 0 k) s.ops) }

/-- The specification twin of `stepLine`: the same line, nothing wrapped —
what the writer emitted before marked content existed. `mark_ink_exact`
is stated against it. -/
private def stepLinePlain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) : TextSt :=
  let s := lineSt geom remap imgMap (Origin.of tags l) st l
  { s with ops := st.ops ++ s.ops }

/-- The page's PDF space from layout coordinates: x from the medium's left
edge (the bleed), y up from its bottom. -/
@[expose] public def pageIso (geom : Geom) : Gfx.Iso :=
  { flipY := true, dx := geom.bleed, dy := geom.bleed + geom.pageH }

/-- A picture's ink as operators: its figure under layout's placement
composed into the page's PDF space (`GfxPdf.emit`). A picture's figure has
no labels — they are the page's lines. -/
@[expose] public def inkPaint (geom : Geom) (ix : GfxPdf.Request → Nat) (k : InkOut) :
    Array ContentOp :=
  GfxPdf.emit ix (fun _ e => nomatch e) ((pageIso geom).compose k.place) k.fig

/-- A single operation under an artifact wrapper. -/
private def artifact (kind : Option ArtifactKind) (o : ContentOp) : ContentOp :=
  .marked (.artifact kind) #[o]

/-- A block of operations under one artifact wrapper, or nothing when
there are none: a page's fills are one sequence and its rules another —
one opener and one `EMC` per block, where one per operation cost a
rule-heavy document seven per cent of its size and a fifth of its
writing time for no reader's benefit. -/
private def artifactBlock (kind : Option ArtifactKind) (ops : Array ContentOp) : Array ContentOp :=
  if ops.isEmpty then #[] else #[.marked (.artifact kind) ops]

/-- An image that loaded is real content under its line's origin; the
placeholder box of one that did not is decoration — a layout artifact,
the diagnostic having already said why. -/
private def imageOp (i : ImgOut) : ContentOp :=
  match i.res with
  | some n => .marked i.origin.mark #[.image i.x i.y i.w i.h n]
  | none => artifact (some .layout) (.imageMissing i.x i.y i.w i.h)

private def imageOpPlain (i : ImgOut) : ContentOp :=
  match i.res with
  | some n => .image i.x i.y i.w i.h n
  | none => .imageMissing i.x i.y i.w i.h

/-- The tag a picture's paths sit under: the structure type the walk gave
the picture's leaf, or — for a path no leaf owns, which the layout never
ships (`placePicture` stamps every path with its picture's leaf) — an
artifact of no type. -/
private def groupTag (tags : Array (Option String)) : Option Nat → MarkTag
  | some k =>
    match (tags[k]?).join with
    | some s => .content s 0 k
    | none => .artifact none
  | none => .artifact none

/-- An open group of paths closed onto the stream as one sequence. -/
private def flushGroup (tags : Array (Option String)) (out : Array ContentOp) :
    Option (Option Nat × Array ContentOp) → Array ContentOp
  | none => out
  | some (lf, ops) => out.push (.marked (groupTag tags lf) ops)

/-- Picture ink grouped per picture: consecutive inks stamped with the same
leaf are one picture's and sit under one sequence (the layout pushes a
picture's one ink with its leaf, `placePicture`). An ink that paints nothing
opens nothing. Structural on the list; the open group travels as state so
the walk needs no lookahead. -/
private def inkGroupsList (geom : Geom) (ix : GfxPdf.Request → Nat) (tags : Array (Option String))
    (out : Array ContentOp) (cur : Option (Option Nat × Array ContentOp)) :
    List InkOut → Array ContentOp
  | [] => flushGroup tags out cur
  | k :: rest =>
    let ops := inkPaint geom ix k
    if ops.isEmpty then inkGroupsList geom ix tags out cur rest
    else match cur with
      | some (lf, acc) =>
        if lf == k.leaf then inkGroupsList geom ix tags out (some (lf, acc ++ ops)) rest
        else inkGroupsList geom ix tags (flushGroup tags out cur) (some (k.leaf, ops)) rest
      | none => inkGroupsList geom ix tags out (some (k.leaf, ops)) rest

private def inkGroups (geom : Geom) (ix : GfxPdf.Request → Nat) (tags : Array (Option String))
    (inks : Array InkOut) : Array ContentOp :=
  inkGroupsList geom ix tags #[] none inks.toList

mutual

/-- Marked-content identifiers assigned in stream order from `n`: every
`content` tag takes the next number, artifacts take none, and the walk
descends every body — so identifiers are unique per page whatever the
construction nested (`numberMarks_mcids_exact`). The tag's type and leaf
are kept; only the identifier changes. -/
private def TextOp.number (n : Nat) : TextOp → TextOp × Nat
  | o@(.scale _) => (o, n)
  | o@(.move _ _) => (o, n)
  | o@(.font _ _) => (o, n)
  | o@(.color _) => (o, n)
  | o@(.show _) => (o, n)
  | .marked (.artifact a) body =>
    let r := TextOp.numberList n #[] body.toList
    (.marked (.artifact a) r.1, r.2)
  | .marked (.content s _ k) body =>
    let r := TextOp.numberList (n + 1) #[] body.toList
    (.marked (.content s n k) r.1, r.2)

private def TextOp.numberList (n : Nat) (acc : Array TextOp) : List TextOp → Array TextOp × Nat
  | [] => (acc, n)
  | o :: rest =>
    let r := TextOp.number n o
    TextOp.numberList r.2 (acc.push r.1) rest

end

mutual

private def ContentOp.number (n : Nat) : ContentOp → ContentOp × Nat
  | o@(.fill _ _ _ _ _) => (o, n)
  | o@(.paint _ _ _ _) => (o, n)
  | o@(.shade _ _) => (o, n)
  | o@(.outline _ _ _) => (o, n)
  | o@(.xobject _ _ _ _) => (o, n)
  | .group m gs clips body =>
    let r := ContentOp.numberList n #[] body.toList
    (.group m gs clips r.1, r.2)
  | .text ops =>
    let r := TextOp.numberList n #[] ops.toList
    (.text r.1, r.2)
  | o@(.image _ _ _ _ _) => (o, n)
  | o@(.imageMissing _ _ _ _) => (o, n)
  | .marked (.artifact a) body =>
    let r := ContentOp.numberList n #[] body.toList
    (.marked (.artifact a) r.1, r.2)
  | .marked (.content s _ k) body =>
    let r := ContentOp.numberList (n + 1) #[] body.toList
    (.marked (.content s n k) r.1, r.2)

private def ContentOp.numberList (n : Nat) (acc : Array ContentOp) :
    List ContentOp → Array ContentOp × Nat
  | [] => (acc, n)
  | o :: rest =>
    let r := ContentOp.number n o
    ContentOp.numberList r.2 (acc.push r.1) rest

end

/-- A page's operators with their marked-content identifiers assigned in
stream order from 0. -/
public def numberMarks (ops : Array ContentOp) : Array ContentOp :=
  (ContentOp.numberList 0 #[] ops.toList).1

/-- One page's operations: fills first, in order (the page background,
then any bars), as one artifact of no stated type — the layout ships
backgrounds, bars and cut marks in one array; then picture paths, one
sequence per picture under its figure's type; then the text object, each
line under its origin's wrapper; then the images the text walk gathered,
each under its line's origin, a placeholder a layout artifact; then the
rules it gathered, as one layout artifact. Identifiers in stream order
over the middle — paths, text, images; the two artifact blocks hold fills
only and carry none, and a rule-heavy page would pay their rebuild for
nothing. Every painting operator sits under exactly one wrapper
(`mcids_partition_covers`). -/
public def contentOps (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (page : PageOut) : Array ContentOp :=
  let fills := page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h
  let paths := inkGroups geom ix tags page.inks
  let st := page.lines.foldl (stepLine geom remap imgMap tags) { widths }
  let images := st.images.map imageOp
  let rules := st.rules.map fun (c, x, y, w, h) => ContentOp.fill c x y w h
  let middle := numberMarks ((paths.push (.text st.ops)) ++ images)
  (artifactBlock none fills ++ middle) ++ artifactBlock (some .layout) (rules ++ st.polys.map polyOp)

/-- The specification twin of `contentOps`: the same operations with no
marked content — the writer before this layer, kept so `mark_ink_exact`
can name the stream it must reproduce. -/
public def contentOpsPlain (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (page : PageOut) : Array ContentOp :=
  let fills := page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h
  let paths := page.inks.flatMap (inkPaint geom ix)
  let st := page.lines.foldl (stepLinePlain geom remap imgMap tags) { widths }
  let images := st.images.map imageOpPlain
  let rules := st.rules.map fun (c, x, y, w, h) => ContentOp.fill c x y w h
  let body := (fills ++ paths).push (.text st.ops)
  (body ++ images) ++ (rules ++ st.polys.map polyOp)

/-! ## The glyph census -/

/-- The glyph runs an item carries: a `TJ` string is one run, an
adjustment none. -/
private def TextItem.runs : TextItem → List (Array Nat)
  | .glyphs gids => [gids]
  | .kerned gids _ => [gids]
  | .adjust _ => []

mutual

private def TextOp.runs : TextOp → List (Array Nat)
  | .scale _ => []
  | .move _ _ => []
  | .font _ _ => []
  | .color _ => []
  | .show items => items.toList.flatMap TextItem.runs
  | .marked _ body => TextOp.runsList body.toList

/-- The glyph census of a text-operator sequence, also used by artifact checks. -/
public def TextOp.runsList : List TextOp → List (Array Nat)
  | [] => []
  | o :: rest =>
    let tail := TextOp.runsList rest
    o.runs ++ tail

end

mutual

private def ContentOp.runs : ContentOp → List (Array Nat)
  | .fill _ _ _ _ _ => []
  | .paint _ _ _ _ => []
  | .shade _ _ => []
  | .outline _ _ _ => []
  | .group _ _ _ body => ContentOp.runsList body.toList
  | .xobject _ _ _ body => ContentOp.runsList body.toList
  | .text ops => ops.toList.flatMap TextOp.runs
  | .image _ _ _ _ _ => []
  | .imageMissing _ _ _ _ => []
  | .marked _ body => ContentOp.runsList body.toList

private def ContentOp.runsList : List ContentOp → List (Array Nat)
  | [] => []
  | o :: rest =>
    let tail := ContentOp.runsList rest
    o.runs ++ tail

end

/-- Every glyph run a content stream paints, in stream order. -/
public def runsOf (ops : Array ContentOp) : List (Array Nat) := ops.toList.flatMap ContentOp.runs

/-! ## Marked content: the line spec and the ink underneath -/

/-- One line of a content stream as the renderer lays it: an operator's
spelling, the opener with its tag (`BDC`, or `BMC` when the tag carries
no properties), or an `EMC`. `lines` is the structural
spec `render` computes (`render_lines_exact`): a fact about which lines
open and close sequences is stated here, and reaches the bytes through
that theorem. -/
public inductive Line where
  | op (s : String)
  | open (tag : MarkTag)
  | emc
  deriving Repr, BEq, Inhabited

public def Line.render : Line → String
  | .op s => s
  | .open t => t.opener
  | .emc => "EMC"

public def Line.isOpen : Line → Bool
  | .open _ => true
  | .op _ => false
  | .emc => false

public def Line.isEmc : Line → Bool
  | .emc => true
  | .op _ => false
  | .open _ => false

/-- The marked-content lines dropped: what a strip of `BDC`/`EMC` lines
leaves of a stream. -/
public def stripMarks (ls : List Line) : List Line := ls.filter fun l => !l.isOpen && !l.isEmc

mutual

public def TextOp.lines : TextOp → List Line
  | .scale p => [.op (TextOp.render (.scale p))]
  | .move x y => [.op (TextOp.render (.move x y))]
  | .font res size => [.op (TextOp.render (.font res size))]
  | .color c => [.op (TextOp.render (.color c))]
  | .show items => [.op (TextOp.render (.show items))]
  | .marked t body => .open t :: (TextOp.linesList body.toList ++ [.emc])

private def TextOp.linesList : List TextOp → List Line
  | [] => []
  | o :: rest =>
    let tail := TextOp.linesList rest
    o.lines ++ tail

end

mutual

public def ContentOp.lines : ContentOp → List Line
  | .fill c x y w h => [.op (ContentOp.render (.fill c x y w h))]
  | .paint fl st gs segs => [.op (ContentOp.render (.paint fl st gs segs))]
  | .shade res g => [.op (ContentOp.render (.shade res g))]
  | .outline fl st segs => [.op (ContentOp.render (.outline fl st segs))]
  | .xobject m res kind body => [.op (ContentOp.render (.xobject m res kind body))]
  | .group m gs clips body =>
    .op (groupHeader m gs clips) :: (ContentOp.linesList body.toList ++ [.op "Q"])
  | .text ops => .op "BT" :: (TextOp.linesList ops.toList ++ [.op "ET"])
  | .image x y w h res => [.op (ContentOp.render (.image x y w h res))]
  | .imageMissing x y w h => [.op (ContentOp.render (.imageMissing x y w h))]
  | .marked t body => .open t :: (ContentOp.linesList body.toList ++ [.emc])

private def ContentOp.linesList : List ContentOp → List Line
  | [] => []
  | o :: rest =>
    let tail := ContentOp.linesList rest
    o.lines ++ tail

end

/-- The stream's lines, in order. -/
public def lines (ops : Array ContentOp) : List Line := ContentOp.linesList ops.toList

/-- Lines joined by their separators: the stream `render` spells. A spec,
not the writer's path (`render` accumulates); the tails are bound so the
copy each prepend makes is visible where it stands. -/
public def joinLines : List Line → String
  | [] => ""
  | l :: rest =>
    let tail := joinTail rest
    l.render ++ tail
where
  joinTail : List Line → String
    | [] => ""
    | l :: rest =>
      let tail := joinTail rest
      "\n" ++ l.render ++ tail

/-- Lines each closed by its line end: the body of a marked sequence, or
of the text object. -/
private def termLines : List Line → String
  | [] => ""
  | l :: rest =>
    let tail := termLines rest
    l.render ++ "\n" ++ tail

mutual

/-- The ink under a text operator: a marked sequence flattened to its
body, in order; a leaf as it is. -/
private def TextOp.ink : TextOp → List TextOp
  | .scale p => [.scale p]
  | .move x y => [.move x y]
  | .font res size => [.font res size]
  | .color c => [.color c]
  | .show items => [.show items]
  | .marked _ body => TextOp.inkList body.toList

private def TextOp.inkList : List TextOp → List TextOp
  | [] => []
  | o :: rest =>
    let tail := TextOp.inkList rest
    o.ink ++ tail

end

private def inkText (ops : Array TextOp) : Array TextOp := (TextOp.inkList ops.toList).toArray

mutual

/-- The ink under a page operation: wrappers dropped at every depth, the
text object's own wrappers included. -/
private def ContentOp.ink : ContentOp → List ContentOp
  | .fill c x y w h => [.fill c x y w h]
  | .paint fl st gs segs => [.paint fl st gs segs]
  | .shade res g => [.shade res g]
  | .outline fl st segs => [.outline fl st segs]
  | .xobject m res kind body => [.xobject m res kind body]
  | .group m gs clips body => [.group m gs clips (ContentOp.inkList body.toList).toArray]
  | .text ops => [.text (inkText ops)]
  | .image x y w h res => [.image x y w h res]
  | .imageMissing x y w h => [.imageMissing x y w h]
  | .marked _ body => ContentOp.inkList body.toList

private def ContentOp.inkList : List ContentOp → List ContentOp
  | [] => []
  | o :: rest =>
    let tail := ContentOp.inkList rest
    o.ink ++ tail

end

/-- The stream with every marked-content wrapper removed, bodies kept in
order: the operators that paint. -/
public def inkOps (ops : Array ContentOp) : Array ContentOp := (ContentOp.inkList ops.toList).toArray

/-- A decoration leaf: a fill or a placeholder box — the operations this
layer never leaves bare (`artifacts_covers`). -/
public def ContentOp.decoration : ContentOp → Bool
  | .fill _ _ _ _ _ => true
  | .imageMissing _ _ _ _ => true
  | .paint _ _ _ _ => false
  | .shade _ _ => false
  | .outline _ _ _ => false
  | .group _ _ _ _ => false
  | .xobject _ _ _ _ => false
  | .text _ => false
  | .image _ _ _ _ _ => false
  | .marked _ _ => false

/-- The glyph run a segment ships: a run's glyph ids when it has any (a
kern is a run with none, and paints nothing). -/
public def segRuns : Seg → List (Array Nat)
  | .run _ _ _ _ glyphs _ _ _ _ _ _ => if glyphs.isEmpty then [] else [glyphs.map (·.1)]
  | .gap _ _ | .decoratedGap _ _ _ => []
  | .rule _ _ _ _ | .decoration _ _ _ _ _ => []
  | .image _ _ _ => []
  | .poly _ _ => []

/-- The shipped glyph census of a page: every run's glyphs, line by line
in segment order — what `pdftotext` reads back, before spelling. -/
public def pageRuns (page : PageOut) : List (Array Nat) :=
  page.lines.toList.flatMap fun l => l.segs.toList.flatMap segRuns

/-! ## The equational theory of `render`

Every renderer above is a left fold that appends; these are the list
equations it computes, so a fact about the bytes is a fact about the
typed array. -/

/-- The general fold-with-append law under an arbitrary accumulator. -/
private theorem foldl_append_acc (f : α → String) (l : List α) (acc : String) :
    l.foldl (fun s x => s ++ f x) acc = acc ++ l.foldl (fun s x => s ++ f x) "" := by
  induction l generalizing acc with
  | nil => simp [String.append_empty]
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rw [ih (acc ++ f x), ih ("" ++ f x), String.empty_append, String.append_assoc]

private theorem foldl_append_eq (f : α → String) (l : List α) (acc : String) :
    l.foldl (fun s x => s ++ f x) acc = acc ++ String.join (l.map f) := by
  rw [String.join_eq_foldl]
  rw [List.foldl_map, foldl_append_acc]

/-- The stream's shape as a list equation: operations joined by newlines.
The specification `render` is proved to compute (`content_render_exact`);
`render` itself accumulates. -/
private def renderList : List ContentOp → String
  | [] => ""
  | [o] => o.render
  | o :: rest => o.render ++ ("\n" ++ renderList rest)

private theorem renderList_go (l : List ContentOp) (acc : String) :
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
private theorem content_render_exact (ops : Array ContentOp) :
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

public theorem text_render_exact (ops : Array TextOp) :
    (ContentOp.text ops).render
      = "BT\n" ++ String.join (ops.toList.map fun o => o.render ++ "\n") ++ "ET" := by
  simp only [ContentOp.render, String.append_assoc]
  rw [← Array.foldl_toList, foldl_append_eq, String.append_assoc]

public theorem show_render_exact (items : Array TextItem) :
    (TextOp.show items).render
      = "[" ++ String.join (items.toList.map TextItem.render) ++ "] TJ" := by
  simp only [TextOp.render]
  rw [← Array.foldl_toList, foldl_append_eq]

/-- The glyph string: the ids' hex digits between the angle brackets that
delimit a PDF hexadecimal string (ISO 32000-2 §7.3.4.3). -/
public theorem glyphs_render_exact (gids : Array Nat) :
    (TextItem.glyphs gids).render
      = String.singleton '<' ++ String.join (gids.toList.map gidHex) ++ String.singleton '>' := by
  simp only [TextItem.render]
  rw [show pushGid = fun acc g => acc ++ gidHex g from funext fun _ => funext fun _ => pushGid_eq ..,
    ← Array.foldl_toList, foldl_append_eq, String.push_eq_append]
  rfl

private theorem paint_render_exact (fl : Option PaintFill) (st : Option PaintStroke)
    (gs : Option ExtG) (segs : Array PathOp) :
    (ContentOp.paint fl st gs segs).render
      = "q " ++ gsState gs ++ fillState fl ++ (strokeState st)
        ++ String.join (segs.toList.map PathOp.render) ++ paintOp fl st ++ " Q" := by
  simp only [ContentOp.render]
  rw [← Array.foldl_toList, foldl_append_eq]

/-! ### Figure operators -/

mutual

/-- An operator a figure paints with: a path, a shading, a saved state or
an XObject over figure operators — never text, a page image, a placeholder
or marked content, so it carries no glyph run and no marked-content
sequence, and its ink is itself. -/
public def ContentOp.figureOnly : ContentOp → Bool
  | .paint _ _ _ _ => true
  | .shade _ _ => true
  | .outline _ _ _ => true
  | .group _ _ _ body => ContentOp.figureOnlyList body.toList
  | .xobject _ _ _ body => ContentOp.figureOnlyList body.toList
  | .fill _ _ _ _ _ => false
  | .text _ => false
  | .image _ _ _ _ _ => false
  | .imageMissing _ _ _ _ => false
  | .marked _ _ => false

public def ContentOp.figureOnlyList : List ContentOp → Bool
  | [] => true
  | o :: rest => o.figureOnly && ContentOp.figureOnlyList rest

end

private theorem figureOnlyList_iff (l : List ContentOp) :
    ContentOp.figureOnlyList l = true ↔ ∀ o ∈ l, o.figureOnly = true := by
  induction l with
  | nil => simp [ContentOp.figureOnlyList]
  | cons o rest ih => simp [ContentOp.figureOnlyList, ih]

private theorem figureOnly_of_mem (body : Array ContentOp) (h : ∀ o ∈ body, o.figureOnly = true) :
    ContentOp.figureOnlyList body.toList = true :=
  (figureOnlyList_iff _).mpr fun o ho => h o (Array.mem_toList_iff.mp ho)

mutual

private theorem emitOne_figureOnly (ix : GfxPdf.Request → Nat)
    (outlines : Array (Array Gfx.Subpath)) (bodyOps : Array (Array ContentOp))
    (hb : ∀ b ∈ bodyOps, ∀ o ∈ b, o.figureOnly = true) :
    ∀ (n : Gfx.Node Empty) (fr : GfxPdf.Frame) (acc : Array ContentOp),
      (∀ o ∈ acc, o.figureOnly = true) →
      ∀ o ∈ GfxPdf.emitOne ix (fun _ e => nomatch e) outlines bodyOps fr acc n,
        o.figureOnly = true
  | .draw g fl st, fr, acc, ha => by
    intro o ho
    simp only [GfxPdf.emitOne, Array.mem_push] at ho
    rcases ho with ho | rfl
    · exact ha o ho
    · rfl
  | .group xf clips alpha kids, fr, acc, ha => by
    intro o ho
    simp only [GfxPdf.emitOne] at ho
    split at ho
    · exact emitList_figureOnly ix outlines bodyOps hb kids.toList fr acc ha o ho
    · split at ho
      · simp only [Array.mem_push] at ho
        rcases ho with ho | rfl
        · exact ha o ho
        · exact figureOnly_of_mem _ (emitList_figureOnly ix outlines bodyOps hb kids.toList _ #[]
            (by simp))
      · simp only [Array.mem_push] at ho
        rcases ho with ho | rfl
        · exact ha o ho
        · simp only [ContentOp.figureOnly, ContentOp.figureOnlyList, Bool.and_true]
          exact figureOnly_of_mem _ (emitList_figureOnly ix outlines bodyOps hb kids.toList _ #[]
            (by simp))
  | .use k xf, fr, acc, ha => by
    intro o ho
    simp only [GfxPdf.emitOne] at ho
    split at ho
    · next body hbody =>
      simp only [Array.mem_push] at ho
      rcases ho with ho | rfl
      · exact ha o ho
      · exact figureOnly_of_mem _ (hb body (Array.mem_of_getElem? hbody))
    · exact ha o ho
  | .stamp o' xf fl st, fr, acc, ha => by
    intro o ho
    simp only [GfxPdf.emitOne] at ho
    split at ho
    · simp only [Array.mem_push] at ho
      rcases ho with ho | rfl
      · exact ha o ho
      · rfl
    · simp only [Array.mem_push] at ho
      rcases ho with ho | rfl
      · exact ha o ho
      · rfl
  | .image k xf, fr, acc, ha => by
    intro o ho
    simp only [GfxPdf.emitOne, Array.mem_push] at ho
    rcases ho with ho | rfl
    · exact ha o ho
    · rfl
  | .label l, _, _, _ => nomatch l
  | .words _, fr, acc, ha => by
    intro o ho
    simp only [GfxPdf.emitOne] at ho
    exact ha o ho

private theorem emitList_figureOnly (ix : GfxPdf.Request → Nat)
    (outlines : Array (Array Gfx.Subpath)) (bodyOps : Array (Array ContentOp))
    (hb : ∀ b ∈ bodyOps, ∀ o ∈ b, o.figureOnly = true) :
    ∀ (xs : List (Gfx.Node Empty)) (fr : GfxPdf.Frame) (acc : Array ContentOp),
      (∀ o ∈ acc, o.figureOnly = true) →
      ∀ o ∈ GfxPdf.emitList ix (fun _ e => nomatch e) outlines bodyOps fr acc xs,
        o.figureOnly = true
  | [], _, acc, ha => ha
  | n :: rest, fr, acc, ha => by
    simp only [GfxPdf.emitList]
    exact emitList_figureOnly ix outlines bodyOps hb rest fr _
      (emitOne_figureOnly ix outlines bodyOps hb n fr acc ha)

end

/-- **A picture's ink is figure operators only**: no glyph run, no
marked-content sequence, under whatever placement and resource naming. -/
private theorem inkPaint_figureOnly (geom : Geom) (ix : GfxPdf.Request → Nat) (k : InkOut) :
    ∀ o ∈ inkPaint geom ix k, o.figureOnly = true := by
  unfold inkPaint GfxPdf.emit
  refine emitList_figureOnly ix _ _ ?_ _ _ #[] (by simp)
  intro b hb o ho
  unfold GfxPdf.bodyOpsOf at hb
  simp only [Array.mem_map] at hb
  obtain ⟨body, _, rfl⟩ := hb
  exact emitList_figureOnly ix _ #[] (by simp) _ _ #[] (by simp) o ho

mutual

private theorem figureOnly_runs : ∀ (o : ContentOp), o.figureOnly = true → o.runs = []
  | .paint _ _ _ _, _ => rfl
  | .shade _ _, _ => rfl
  | .outline _ _ _, _ => rfl
  | .group _ _ _ body, h => by
    simp only [ContentOp.figureOnly] at h
    simp only [ContentOp.runs]
    exact figureOnlyList_runs body.toList h
  | .xobject _ _ _ body, h => by
    simp only [ContentOp.figureOnly] at h
    simp only [ContentOp.runs]
    exact figureOnlyList_runs body.toList h
  | .fill _ _ _ _ _, h => by simp [ContentOp.figureOnly] at h
  | .text _, h => by simp [ContentOp.figureOnly] at h
  | .image _ _ _ _ _, h => by simp [ContentOp.figureOnly] at h
  | .imageMissing _ _ _ _, h => by simp [ContentOp.figureOnly] at h
  | .marked _ _, h => by simp [ContentOp.figureOnly] at h

private theorem figureOnlyList_runs : ∀ (l : List ContentOp), ContentOp.figureOnlyList l = true →
    ContentOp.runsList l = []
  | [], _ => rfl
  | o :: rest, h => by
    simp only [ContentOp.figureOnlyList, Bool.and_eq_true] at h
    simp only [ContentOp.runsList, figureOnly_runs o h.1, figureOnlyList_runs rest h.2,
      List.append_nil]

end
/-- The runs a walk state holds: those already in ops, then the open array's. -/
private def TextSt.runs (st : TextSt) : List (Array Nat) :=
  st.ops.toList.flatMap TextOp.runs ++ st.items.toList.flatMap TextItem.runs

private theorem flatMap_nil_fun (l : List α) : l.flatMap (fun (_ : α) => ([] : List β)) = [] :=
  List.flatMap_eq_nil_iff.mpr fun _ _ => rfl

private theorem op_runs (st : TextSt) (o : TextOp) (h : o.runs = []) : (st.op o).runs = st.runs := by
  simp [TextSt.op, TextSt.runs, h]

private theorem closeTJ_runs (st : TextSt) : st.closeTJ.runs = st.runs := by
  unfold TextSt.closeTJ
  split
  · rfl
  · simp [TextSt.runs, TextOp.runs]

private theorem closeTJ_items (st : TextSt) : st.closeTJ.items = #[] := by
  unfold TextSt.closeTJ
  split
  · rename_i h
    exact Array.isEmpty_iff.mp h
  · rfl

private theorem moveTo_runs (st : TextSt) (y : Sp) : (st.moveTo y).runs = st.runs := by
  have h := op_runs st.closeTJ (.move st.x y) rfl
  rw [closeTJ_runs] at h
  exact h

private theorem toPen_runs (st : TextSt) (c : Bool) (y : Sp) : (st.toPen c y).runs = st.runs := by
  unfold TextSt.toPen
  split
  · simp only []
    split
    · split
      · rfl
      · simp [TextSt.runs, TextItem.runs]
    · exact moveTo_runs st y
  · exact moveTo_runs st y

private theorem setFont_runs (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp) :
    (st.setFont remap idx size).runs = st.runs := by
  unfold TextSt.setFont
  split
  · exact op_runs _ _ rfl
  · rfl

private theorem setColor_runs (st : TextSt) (c : Ir.Color) : (st.setColor c).runs = st.runs := by
  unfold TextSt.setColor
  split
  · exact op_runs _ _ rfl
  · rfl

private theorem setFace_runs (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp) (c : Ir.Color) :
    (st.setFace remap idx size c).runs = st.runs := by
  unfold TextSt.setFace
  rw [setColor_runs, setFont_runs, closeTJ_runs]

private theorem runItem_runs (gids : Array Nat) (nums : Array Int) : (runItem gids nums).runs = [gids] := by
  unfold runItem
  split <;> rfl

private theorem pushRun_runs (st : TextSt) (i : TextItem) (w : Sp) (p : Pen) :
    (st.pushRun i w p).runs = st.runs ++ i.runs := by
  simp [TextSt.pushRun, TextSt.runs]

private theorem stepRun_runs (remap : Array Nat) (ls y : Sp) (st : TextSt) (idx : Nat) (c : Ir.Color)
    (w : Sp) (glyphs : Array (Nat × Char × Sp)) (ss raise : Sp) :
    (stepRun remap ls y st idx c w glyphs ss raise).runs
      = st.runs ++ (if glyphs.isEmpty then [] else [glyphs.map (·.1)]) := by
  unfold stepRun
  split
  · simp [TextSt.runs]
  · simp only [pushRun_runs, runItem_runs, Array.mkEmpty_eq, place_glyphs_id]
    congr 1
    simp only [apply_ite TextSt.runs, setFace_runs, toPen_runs, ite_self]

private theorem stepSeg_runs (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp) (og : Origin)
    (st : TextSt) (seg : Seg) : (stepSeg remap imgMap ls y og st seg).runs = st.runs ++ segRuns seg := by
  cases seg with
  | rule | decoration => simp [stepSeg, TextSt.runs, segRuns]
  | image => simp [stepSeg, TextSt.runs, segRuns]
  | gap | decoratedGap => simp [stepSeg, TextSt.runs, segRuns]
  | poly => simp [stepSeg, TextSt.runs, segRuns]
  | run => exact stepRun_runs ..

private theorem foldl_segs_runs (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp)
    (og : Origin) (segs : List Seg) (st : TextSt) :
    (segs.foldl (stepSeg remap imgMap ls y og) st).runs = st.runs ++ segs.flatMap segRuns := by
  induction segs generalizing st with
  | nil => simp
  | cons s rest ih => simp [ih, stepSeg_runs, List.append_assoc]

private theorem TextOp.runsList_eq (l : List TextOp) : TextOp.runsList l = l.flatMap TextOp.runs := by
  induction l with
  | nil => rfl
  | cons o rest ih => simp [TextOp.runsList, ih]

private theorem ContentOp.runsList_eq (l : List ContentOp) :
    ContentOp.runsList l = l.flatMap ContentOp.runs := by
  induction l with
  | nil => rfl
  | cons o rest ih => simp [ContentOp.runsList, ih]

private theorem lineSt_runs (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (og : Origin) (st : TextSt) (l : LineOut) :
    (lineSt geom remap imgMap og st l).runs
      = st.items.toList.flatMap TextItem.runs ++ l.segs.toList.flatMap segRuns := by
  unfold lineSt
  simp only []
  rw [closeTJ_runs, ← Array.foldl_toList, foldl_segs_runs]
  congr 1
  split
  · simp [TextSt.runs, TextSt.op, TextOp.runs]
  · simp [TextSt.runs]

private theorem lineSt_items (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (og : Origin) (st : TextSt) (l : LineOut) : (lineSt geom remap imgMap og st l).items = #[] := by
  unfold lineSt
  exact closeTJ_items _

/-- The runs of a text object's operators after one line: the line's runs
in segment order appended, whatever wrapper the origin chose — a wrapper
ships its body's runs, and an empty line ships none. -/
private theorem stepLine_runs (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap tags st l).runs = st.runs ++ l.segs.toList.flatMap segRuns := by
  unfold stepLine
  have hs := lineSt_runs geom remap imgMap (Origin.of tags l) st l
  have hi := lineSt_items geom remap imgMap (Origin.of tags l) st l
  simp only [TextSt.runs] at hs ⊢
  rw [hi] at hs ⊢
  simp only [List.flatMap_nil, List.append_nil] at hs ⊢
  have hempty : (lineSt geom remap imgMap (Origin.of tags l) st l).ops.isEmpty = true →
      List.flatMap TextItem.runs st.items.toList = []
        ∧ List.flatMap segRuns l.segs.toList = [] := by
    intro he
    rw [← List.append_eq_nil_iff, ← hs, Array.isEmpty_iff.mp he]
    simp
  split
  · simp [Array.toList_push, List.flatMap_append, TextOp.runs, TextOp.runsList_eq, hs,
      List.append_assoc]
  · split
    · rename_i he
      simp [(hempty he).1, (hempty he).2]
    · simp [Array.toList_push, List.flatMap_append, TextOp.runs, TextOp.runsList_eq, hs,
        List.append_assoc]
  · split
    · rename_i he
      simp [(hempty he).1, (hempty he).2]
    · simp [Array.toList_push, List.flatMap_append, TextOp.runs, TextOp.runsList_eq, hs,
        List.append_assoc]

private theorem stepLine_items (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap tags st l).items = #[] := by
  simp only [stepLine]
  split <;> exact lineSt_items ..

private theorem foldl_lines_runs (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (lines : List LineOut) (st : TextSt) :
    (lines.foldl (stepLine geom remap imgMap tags) st).runs
      = st.runs ++ lines.flatMap (fun l => l.segs.toList.flatMap segRuns) := by
  induction lines generalizing st with
  | nil => simp
  | cons l rest ih => simp [ih, stepLine_runs, List.append_assoc]

private theorem foldl_lines_items (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (lines : List LineOut) (st : TextSt) (h : st.items = #[]) :
    (lines.foldl (stepLine geom remap imgMap tags) st).items = #[] := by
  induction lines generalizing st with
  | nil => exact h
  | cons l rest ih => exact ih _ (stepLine_items ..)

private theorem imageOp_runs (i : ImgOut) : (imageOp i).runs = [] := by
  unfold imageOp
  split <;> simp [artifact, ContentOp.runs, ContentOp.runsList]

private theorem flushGroup_runs (tags : Array (Option String)) (out : Array ContentOp)
    (cur : Option (Option Nat × Array ContentOp)) (hc : ∀ g ∈ cur, ∀ o ∈ g.2, o.runs = [])
    (ho : ∀ o ∈ out, o.runs = []) : ∀ o ∈ flushGroup tags out cur, o.runs = [] := by
  intro o h
  cases cur with
  | none => exact ho o h
  | some g =>
    simp only [flushGroup, Array.mem_push] at h
    rcases h with h | rfl
    · exact ho o h
    · simp only [ContentOp.runs, ContentOp.runsList_eq]
      exact List.flatMap_eq_nil_iff.mpr fun o' h' => hc g rfl o' (Array.mem_def.mpr h')

/-- Every operator of the ink groups is one marked sequence of figure
operators. -/
private theorem inkGroupsList_shape (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tags : Array (Option String)) (inks : List InkOut) (out : Array ContentOp)
    (cur : Option (Option Nat × Array ContentOp))
    (hc : ∀ g ∈ cur, ∀ o ∈ g.2, o.figureOnly = true)
    (ho : ∀ o ∈ out, ∃ t body, o = .marked t body ∧ ∀ b ∈ body, b.figureOnly = true) :
    ∀ o ∈ inkGroupsList geom ix tags out cur inks,
      ∃ t body, o = .marked t body ∧ ∀ b ∈ body, b.figureOnly = true := by
  have hflush : ∀ (out : Array ContentOp) (cur : Option (Option Nat × Array ContentOp)),
      (∀ g ∈ cur, ∀ o ∈ g.2, o.figureOnly = true) →
      (∀ o ∈ out, ∃ t body, o = .marked t body ∧ ∀ b ∈ body, b.figureOnly = true) →
      ∀ o ∈ flushGroup tags out cur, ∃ t body, o = .marked t body ∧ ∀ b ∈ body, b.figureOnly = true := by
    intro out cur hc ho o h
    cases cur with
    | none => exact ho o h
    | some g =>
      simp only [flushGroup, Array.mem_push] at h
      rcases h with h | rfl
      · exact ho o h
      · exact ⟨_, _, rfl, hc g rfl⟩
  induction inks generalizing out cur with
  | nil => exact hflush out cur hc ho
  | cons k rest ih =>
    simp only [inkGroupsList]
    have hk := inkPaint_figureOnly geom ix k
    split
    · exact ih out cur hc ho
    · split
      · rename_i lf acc
        split
        · apply ih
          · intro g hg o h
            simp only [Option.mem_def, Option.some.injEq] at hg
            subst hg
            simp only [Array.mem_append] at h
            rcases h with h | h
            · exact hc _ rfl o h
            · exact hk o h
          · exact ho
        · apply ih
          · intro g hg o h
            simp only [Option.mem_def, Option.some.injEq] at hg
            subst hg
            exact hk o h
          · exact hflush out _ hc ho
      · apply ih
        · intro g hg o h
          simp only [Option.mem_def, Option.some.injEq] at hg
          subst hg
          exact hk o h
        · exact ho

private theorem inkGroups_shape (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tags : Array (Option String)) (inks : Array InkOut) :
    ∀ o ∈ inkGroups geom ix tags inks,
      ∃ t body, o = .marked t body ∧ ∀ b ∈ body, b.figureOnly = true :=
  inkGroupsList_shape geom ix tags inks.toList #[] none (by simp) (by simp)

/-- A picture's ink paints no glyph run, however grouped. -/
private theorem inkGroups_runs (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tags : Array (Option String)) (inks : Array InkOut) :
    (inkGroups geom ix tags inks).toList.flatMap ContentOp.runs = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro o h
  obtain ⟨t, body, rfl, hb⟩ := inkGroups_shape geom ix tags inks o (Array.mem_def.mpr h)
  simp only [ContentOp.runs]
  exact figureOnlyList_runs _ (figureOnly_of_mem body hb)

private theorem artifact_runs (k : Option ArtifactKind) (o : ContentOp) :
    (artifact k o).runs = o.runs := by
  simp [artifact, ContentOp.runs, ContentOp.runsList]

private theorem artifactBlock_runs (k : Option ArtifactKind) (ops : Array ContentOp) :
    (artifactBlock k ops).toList.flatMap ContentOp.runs = ops.toList.flatMap ContentOp.runs := by
  unfold artifactBlock
  split
  · rename_i h
    simp [Array.isEmpty_iff.mp h]
  · simp [ContentOp.runs, ContentOp.runsList_eq]

mutual

/-- Numbering the marked-content identifiers touches no glyph run. -/
private theorem TextOp.number_runs : ∀ (o : TextOp) (n : Nat), (TextOp.number n o).1.runs = o.runs
  | .scale _, _ => rfl
  | .move _ _, _ => rfl
  | .font _ _, _ => rfl
  | .color _, _ => rfl
  | .show _, _ => rfl
  | .marked (.artifact a) body, n => by
    have h := TextOp.numberList_runs body.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [TextOp.number, TextOp.runs, TextOp.runsList_eq, h]
  | .marked (.content s m k) body, n => by
    have h := TextOp.numberList_runs body.toList (n + 1) #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [TextOp.number, TextOp.runs, TextOp.runsList_eq, h]

private theorem TextOp.numberList_runs : ∀ (l : List TextOp) (n : Nat) (acc : Array TextOp),
    (TextOp.numberList n acc l).1.toList.flatMap TextOp.runs
      = acc.toList.flatMap TextOp.runs ++ l.flatMap TextOp.runs
  | [], n, acc => by simp [TextOp.numberList]
  | o :: rest, n, acc => by
    rw [TextOp.numberList]
    simp [TextOp.numberList_runs rest, Array.toList_push, TextOp.number_runs o n]

end

mutual

private theorem ContentOp.number_runs : ∀ (o : ContentOp) (n : Nat),
    (ContentOp.number n o).1.runs = o.runs
  | .fill _ _ _ _ _, _ => rfl
  | .paint _ _ _ _, _ => rfl
  | .shade _ _, _ => rfl
  | .outline _ _ _, _ => rfl
  | .xobject _ _ _ _, _ => rfl
  | .group m gs clips body, n => by
    have h := ContentOp.numberList_runs body.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.runs, ContentOp.runsList_eq, h]
  | .image _ _ _ _ _, _ => rfl
  | .imageMissing _ _ _ _, _ => rfl
  | .text ops, n => by
    have h := TextOp.numberList_runs ops.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.runs, h]
  | .marked (.artifact a) body, n => by
    have h := ContentOp.numberList_runs body.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.runs, ContentOp.runsList_eq, h]
  | .marked (.content s m k) body, n => by
    have h := ContentOp.numberList_runs body.toList (n + 1) #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.runs, ContentOp.runsList_eq, h]

private theorem ContentOp.numberList_runs : ∀ (l : List ContentOp) (n : Nat) (acc : Array ContentOp),
    (ContentOp.numberList n acc l).1.toList.flatMap ContentOp.runs
      = acc.toList.flatMap ContentOp.runs ++ l.flatMap ContentOp.runs
  | [], n, acc => by simp [ContentOp.numberList]
  | o :: rest, n, acc => by
    rw [ContentOp.numberList]
    simp [ContentOp.numberList_runs rest, Array.toList_push, ContentOp.number_runs o n]

end

private theorem numberMarks_runs_list (ops : Array ContentOp) :
    (numberMarks ops).toList.flatMap ContentOp.runs = ops.toList.flatMap ContentOp.runs := by
  unfold numberMarks
  rw [ContentOp.numberList_runs]
  simp

public theorem numberMarks_runs (ops : Array ContentOp) : runsOf (numberMarks ops) = runsOf ops :=
  numberMarks_runs_list ops

/-- **The PDF paints every glyph run the page shipped, in order.** The glyph
census of the typed content stream is the page's run census: no run
dropped, none invented, none reordered — the `_text` fact for the
PageOut → ContentOp projection (not a `Conserves` instance: the walk
changes type, as `structTree_text` does). -/
public theorem contentOps_text (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (page : PageOut) :
    runsOf (contentOps geom remap widths imgMap tags ix page) = pageRuns page := by
  unfold contentOps
  unfold runsOf pageRuns
  simp only [Array.toList_append, List.flatMap_append, artifactBlock_runs, numberMarks_runs_list]
  simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Array.toList_map, List.flatMap_map, imageOp_runs,
    flatMap_nil_fun, inkGroups_runs]
  simp only [ContentOp.runs, polyOp, flatMap_nil_fun, List.append_nil, List.nil_append]
  have hr := foldl_lines_runs geom remap imgMap tags page.lines.toList { widths }
  have hi := foldl_lines_items geom remap imgMap tags page.lines.toList { widths } rfl
  rw [Array.foldl_toList] at hr hi
  simp only [TextSt.runs, hi] at hr
  simpa using hr
private theorem hexDigit_inj : ∀ a, a < 16 → ∀ b, b < 16 → hexDigit a = hexDigit b → a = b := by
  decide

private theorem hexDigit_mod (a : Nat) : hexDigit a = hexDigit (a % 16) := by
  simp [hexDigit]

private theorem hexDigit_eq_mod {a b : Nat} (h : hexDigit a = hexDigit b) : a % 16 = b % 16 := by
  rw [hexDigit_mod a, hexDigit_mod b] at h
  exact hexDigit_inj _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) h

private theorem gidHex_toList (g : Nat) :
    (gidHex g).toList
      = [hexDigit (g / 4096), hexDigit (g / 256), hexDigit (g / 16), hexDigit g] := by
  simp [gidHex, pushGid, String.toList_push]

/-- A glyph id in the Identity-H range is recoverable from its four hex
digits: the spelling is injective below 65536 (above it, the leading
digits wrap — the honest bound). -/
public theorem gidHex_inj {g₁ g₂ : Nat} (h₁ : g₁ < 65536) (h₂ : g₂ < 65536)
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

private theorem join_cons (a : String) (as : List String) :
    String.join (a :: as) = a ++ String.join as :=
  String.join_cons

private theorem join_gidHex_inj : ∀ (l₁ l₂ : List Nat), (∀ g ∈ l₁, g < 65536) → (∀ g ∈ l₂, g < 65536) →
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
public theorem glyphs_inj {a b : Array Nat} (ha : ∀ g ∈ a, g < 65536) (hb : ∀ g ∈ b, g < 65536)
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
public theorem render_not_inj : ∃ a b : Array ContentOp, a ≠ b ∧ render a = render b :=
  ⟨#[.fill Ir.Color.black 0 0 1 1],
    #[.paint (some { paint := .solid Ir.Color.black, evenOdd := false }) none none #[.rect 0 0 1 1]],
    fun h => by have := congrArg (·[0]?) h; simp at this, by
      change (ContentOp.fill Ir.Color.black 0 0 1 1).render =
        (ContentOp.paint (some { paint := .solid Ir.Color.black, evenOdd := false }) none none
          #[.rect 0 0 1 1]).render
      rw [paint_render_exact]
      simp [ContentOp.render, PathOp.render, fillState, strokeState, gsState, paintOp,
        pdfPaintFill, String.append_assoc] <;>
        rfl⟩

/-! ## Marked content: the line spec, balance, and the ink underneath -/

private theorem joinTail_append_singleton (a : List Line) (x : Line) :
    joinLines.joinTail (a ++ [x]) = joinLines.joinTail a ++ ("\n" ++ x.render) := by
  induction a with
  | nil => simp [joinLines.joinTail]
  | cons l rest ih => simp [joinLines.joinTail, ih, String.append_assoc]

private theorem termLines_append (a b : List Line) : termLines (a ++ b) = termLines a ++ termLines b := by
  induction a with
  | nil => simp [termLines]
  | cons l rest ih => simp [termLines, ih, String.append_assoc]

private theorem termLines_eq_joinTail (l : List Line) :
    "\n" ++ termLines l = joinLines.joinTail l ++ "\n" := by
  induction l with
  | nil => simp [termLines, joinLines.joinTail]
  | cons x rest ih =>
    simp only [termLines, joinLines.joinTail, String.append_assoc]
    rw [ih]

/-- The shape of a marked sequence and of the text object: an opening
line, a terminated body, a closing line — as joined lines. -/
private theorem open_body_close_eq (a : String) (l : List Line) (z : String) :
    a ++ "\n" ++ termLines l ++ z = a ++ (joinLines.joinTail l ++ ("\n" ++ z)) := by
  induction l generalizing a with
  | nil => simp [termLines, joinLines.joinTail, String.append_assoc]
  | cons x rest ih =>
    simp only [termLines, joinLines.joinTail]
    have := ih (a ++ "\n" ++ x.render)
    simp only [String.append_assoc] at this ⊢
    exact this

private theorem joinTail_append (a b : List Line) (hb : b ≠ []) :
    joinLines.joinTail (a ++ b) = joinLines.joinTail a ++ ("\n" ++ joinLines b) := by
  induction a with
  | nil =>
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hb
    simp [joinLines.joinTail, joinLines, String.append_assoc]
  | cons x rest ih => simp [joinLines.joinTail, ih, String.append_assoc]

private theorem joinLines_append (a b : List Line) (ha : a ≠ []) (hb : b ≠ []) :
    joinLines (a ++ b) = joinLines a ++ ("\n" ++ joinLines b) := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil ha
  simp [joinLines, joinTail_append _ _ hb, String.append_assoc]

/-- A non-empty line list closed by its line end is the joined lines
followed by one. -/
private theorem termLines_cons (l : Line) (rest : List Line) :
    termLines (l :: rest) = joinLines (l :: rest) ++ "\n" := by
  simp only [termLines, joinLines, String.append_assoc]
  rw [termLines_eq_joinTail]

private theorem TextOp.lines_ne_nil (o : TextOp) : o.lines ≠ [] := by
  cases o <;> simp [TextOp.lines]

private theorem ContentOp.lines_ne_nil (o : ContentOp) : o.lines ≠ [] := by
  cases o <;> simp [ContentOp.lines]

private theorem TextOp.linesList_append (a b : List TextOp) :
    TextOp.linesList (a ++ b) = TextOp.linesList a ++ TextOp.linesList b := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [TextOp.linesList, ih]

private theorem ContentOp.linesList_append (a b : List ContentOp) :
    ContentOp.linesList (a ++ b) = ContentOp.linesList a ++ ContentOp.linesList b := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [ContentOp.linesList, ih]

mutual

private theorem TextOp.render_lines : ∀ o : TextOp, o.render = joinLines o.lines
  | .scale p => by simp [TextOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .move x y => by simp [TextOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .font res size => by simp [TextOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .color c => by simp [TextOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .show items => by simp [TextOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .marked t body => by
    rw [TextOp.render, TextOp.lines, TextOp.renderLines_exact body.toList, joinLines,
      joinTail_append_singleton]
    simp only [Line.render]
    exact open_body_close_eq ..

private theorem TextOp.renderLines_exact : ∀ (l : List TextOp) (acc : String),
    TextOp.renderLines acc l = acc ++ termLines (TextOp.linesList l)
  | [], acc => by simp [TextOp.renderLines, TextOp.linesList, termLines]
  | o :: rest, acc => by
    have hl : termLines o.lines = o.render ++ "\n" := by
      obtain ⟨l, rest', h⟩ := List.exists_cons_of_ne_nil (TextOp.lines_ne_nil o)
      rw [h, termLines_cons, ← h, ← TextOp.render_lines o]
    rw [TextOp.renderLines, TextOp.renderLines_exact rest, TextOp.linesList]
    simp only [termLines_append, hl, String.append_assoc]

end

/-- **Every text operator renders as its lines joined**, a marked
sequence as its opening line, its body's lines, and its `EMC` line. -/
public theorem TextOp.render_lines_exact (o : TextOp) : o.render = joinLines o.lines :=
  TextOp.render_lines o

mutual

private theorem ContentOp.render_lines : ∀ o : ContentOp, o.render = joinLines o.lines
  | .fill c x y w h => by simp [ContentOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .paint fl st gs segs => by simp [ContentOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .shade res g => by simp [ContentOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .outline fl st segs => by simp [ContentOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .xobject m res kind body => by
    simp [ContentOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .group m gs clips body => by
    rw [ContentOp.render, ContentOp.lines, ContentOp.renderLines_exact body.toList, joinLines,
      joinTail_append_singleton]
    simp only [Line.render]
    exact open_body_close_eq ..
  | .image x y w h res => by simp [ContentOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .imageMissing x y w h => by
    simp [ContentOp.lines, joinLines, joinLines.joinTail, Line.render]
  | .text ops => by
    rw [ContentOp.render, ContentOp.lines, ← Array.foldl_toList,
      show ops.toList.foldl (fun acc op => acc ++ op.render ++ "\n") "BT\n"
        = TextOp.renderLines "BT\n" ops.toList from ?_,
      TextOp.renderLines_exact, joinLines, joinTail_append_singleton]
    · simp only [Line.render]
      rw [show ("BT\n" : String) = "BT" ++ "\n" from rfl]
      exact open_body_close_eq ..
    · generalize "BT\n" = acc
      induction ops.toList generalizing acc with
      | nil => rfl
      | cons o rest ih => simp only [List.foldl_cons, TextOp.renderLines, ih]
  | .marked t body => by
    rw [ContentOp.render, ContentOp.lines, ContentOp.renderLines_exact body.toList, joinLines,
      joinTail_append_singleton]
    simp only [Line.render]
    exact open_body_close_eq ..

private theorem ContentOp.renderLines_exact : ∀ (l : List ContentOp) (acc : String),
    ContentOp.renderLines acc l = acc ++ termLines (ContentOp.linesList l)
  | [], acc => by simp [ContentOp.renderLines, ContentOp.linesList, termLines]
  | o :: rest, acc => by
    have hl : termLines o.lines = o.render ++ "\n" := by
      obtain ⟨l, rest', h⟩ := List.exists_cons_of_ne_nil (ContentOp.lines_ne_nil o)
      rw [h, termLines_cons, ← h, ← ContentOp.render_lines o]
    rw [ContentOp.renderLines, ContentOp.renderLines_exact rest, ContentOp.linesList]
    simp only [termLines_append, hl, String.append_assoc]

end

/-- **Every page operation renders as its lines joined**: the text object
as `BT`, its operators' lines, `ET`; a marked sequence as its opening
line, its body's lines, and its `EMC` line. -/
public theorem ContentOp.render_lines_exact (o : ContentOp) : o.render = joinLines o.lines :=
  ContentOp.render_lines o

private theorem ContentOp.linesList_ne_nil (o : ContentOp) (rest : List ContentOp) :
    ContentOp.linesList (o :: rest) ≠ [] := by
  simp [ContentOp.linesList, ContentOp.lines_ne_nil]

private theorem renderList_eq_joinLines (l : List ContentOp) :
    renderList l = joinLines (ContentOp.linesList l) := by
  induction l with
  | nil => rfl
  | cons o rest ih =>
    cases rest with
    | nil =>
      simp only [renderList, ContentOp.linesList, List.append_nil]
      exact ContentOp.render_lines_exact o
    | cons p rest' =>
      have hl : ContentOp.linesList (o :: p :: rest') = o.lines ++ ContentOp.linesList (p :: rest') :=
        ContentOp.linesList.eq_2 ..
      rw [renderList, ih, ContentOp.render_lines_exact o, hl,
        joinLines_append _ _ (ContentOp.lines_ne_nil o) (ContentOp.linesList_ne_nil p rest')]
      simp

/-- **The stream is its lines joined.** `render`'s bytes are `lines`'
spelling: what opens and closes a marked-content sequence on the page is
decided on the typed line list, and this equation carries it to the
bytes. -/
public theorem render_lines_exact (ops : Array ContentOp) : render ops = joinLines (lines ops) := by
  rw [content_render_exact, lines, renderList_eq_joinLines]

mutual

private theorem TextOp.lines_balanced :
    ∀ o : TextOp, o.lines.countP Line.isOpen = o.lines.countP Line.isEmc
  | .scale _ => by simp [TextOp.lines, Line.isOpen, Line.isEmc]
  | .move _ _ => by simp [TextOp.lines, Line.isOpen, Line.isEmc]
  | .font _ _ => by simp [TextOp.lines, Line.isOpen, Line.isEmc]
  | .color _ => by simp [TextOp.lines, Line.isOpen, Line.isEmc]
  | .show _ => by simp [TextOp.lines, Line.isOpen, Line.isEmc]
  | .marked t body => by
    have := TextOp.linesList_balanced body.toList
    simp [TextOp.lines, Line.isOpen, Line.isEmc, List.countP_append, List.countP_cons, this]

private theorem TextOp.linesList_balanced : ∀ l : List TextOp,
    (TextOp.linesList l).countP Line.isOpen = (TextOp.linesList l).countP Line.isEmc
  | [] => rfl
  | o :: rest => by
    have h₁ := TextOp.lines_balanced o
    have h₂ := TextOp.linesList_balanced rest
    simp [TextOp.linesList, List.countP_append, h₁, h₂]

end

mutual

private theorem ContentOp.lines_balanced :
    ∀ o : ContentOp, o.lines.countP Line.isOpen = o.lines.countP Line.isEmc
  | .fill _ _ _ _ _ => by simp [ContentOp.lines, Line.isOpen, Line.isEmc]
  | .paint _ _ _ _ => by simp [ContentOp.lines, Line.isOpen, Line.isEmc]
  | .shade _ _ => by simp [ContentOp.lines, Line.isOpen, Line.isEmc]
  | .outline _ _ _ => by simp [ContentOp.lines, Line.isOpen, Line.isEmc]
  | .xobject _ _ _ _ => by simp [ContentOp.lines, Line.isOpen, Line.isEmc]
  | .group m gs clips body => by
    have := ContentOp.linesList_balanced body.toList
    simp [ContentOp.lines, Line.isOpen, Line.isEmc, List.countP_append, this]
  | .image _ _ _ _ _ => by simp [ContentOp.lines, Line.isOpen, Line.isEmc]
  | .imageMissing _ _ _ _ => by simp [ContentOp.lines, Line.isOpen, Line.isEmc]
  | .text ops => by
    have := TextOp.linesList_balanced ops.toList
    simp [ContentOp.lines, Line.isOpen, Line.isEmc, List.countP_append, this]
  | .marked t body => by
    have := ContentOp.linesList_balanced body.toList
    simp [ContentOp.lines, Line.isOpen, Line.isEmc, List.countP_append, List.countP_cons, this]

private theorem ContentOp.linesList_balanced : ∀ l : List ContentOp,
    (ContentOp.linesList l).countP Line.isOpen = (ContentOp.linesList l).countP Line.isEmc
  | [] => rfl
  | o :: rest => by
    have h₁ := ContentOp.lines_balanced o
    have h₂ := ContentOp.linesList_balanced rest
    simp [ContentOp.linesList, List.countP_append, h₁, h₂]

end

/-- **Every stream opens as many marked-content sequences as it closes**:
opening (`BDC`/`BMC`) and `EMC` lines pair off, whatever the operator array — the
executable form of "ill-nesting is unrepresentable", since `marked` is
the only constructor that spells either. Reaches the bytes through
`render_lines_exact`. -/
public theorem lines_marked_balanced (ops : Array ContentOp) :
    (lines ops).countP Line.isOpen = (lines ops).countP Line.isEmc :=
  ContentOp.linesList_balanced _

private theorem stripMarks_cons_open (t : MarkTag) (ls : List Line) :
    stripMarks (.open t :: ls) = stripMarks ls := by
  simp [stripMarks, Line.isOpen]

private theorem stripMarks_cons_op (s : String) (ls : List Line) :
    stripMarks (.op s :: ls) = .op s :: stripMarks ls := by
  simp [stripMarks, Line.isOpen, Line.isEmc]

private theorem stripMarks_append (a b : List Line) : stripMarks (a ++ b) = stripMarks a ++ stripMarks b :=
  List.filter_append ..

private theorem stripMarks_emc : stripMarks [.emc] = [] := by simp [stripMarks, Line.isEmc]

private theorem stripMarks_nil : stripMarks [] = [] := rfl

private theorem stripMarks_countP_open (ls : List Line) : (stripMarks ls).countP Line.isOpen = 0 := by
  rw [List.countP_eq_zero]
  intro l hl
  simp only [stripMarks, List.mem_filter, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hl
  simp [hl.2.1]

private theorem TextOp.inkList_append (a b : List TextOp) :
    TextOp.inkList (a ++ b) = TextOp.inkList a ++ TextOp.inkList b := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [TextOp.inkList, ih]

private theorem ContentOp.inkList_append (a b : List ContentOp) :
    ContentOp.inkList (a ++ b) = ContentOp.inkList a ++ ContentOp.inkList b := by
  induction a with
  | nil => rfl
  | cons o rest ih => simp [ContentOp.inkList, ih]

mutual

/-- The lines of an operator's ink are its lines with the marked-content
lines stripped. -/
private theorem TextOp.lines_ink : ∀ o : TextOp, TextOp.linesList o.ink = stripMarks o.lines
  | .scale p => by simp [TextOp.ink, TextOp.lines, TextOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .move x y => by
    simp [TextOp.ink, TextOp.lines, TextOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .font res size => by
    simp [TextOp.ink, TextOp.lines, TextOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .color c => by simp [TextOp.ink, TextOp.lines, TextOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .show items => by
    simp [TextOp.ink, TextOp.lines, TextOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .marked t body => by
    rw [TextOp.ink, TextOp.lines, TextOp.linesList_ink body.toList, stripMarks_cons_open,
      stripMarks_append, stripMarks_emc, List.append_nil]

private theorem TextOp.linesList_ink : ∀ l : List TextOp,
    TextOp.linesList (TextOp.inkList l) = stripMarks (TextOp.linesList l)
  | [] => rfl
  | o :: rest => by
    rw [TextOp.inkList, TextOp.linesList, TextOp.linesList_append, TextOp.lines_ink o,
      TextOp.linesList_ink rest, stripMarks_append]

end

mutual

private theorem ContentOp.lines_ink : ∀ o : ContentOp, ContentOp.linesList o.ink = stripMarks o.lines
  | .fill c x y w h => by
    simp [ContentOp.ink, ContentOp.lines, ContentOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .paint fl st gs segs => by
    simp [ContentOp.ink, ContentOp.lines, ContentOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .shade res g => by
    simp [ContentOp.ink, ContentOp.lines, ContentOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .outline fl st segs => by
    simp [ContentOp.ink, ContentOp.lines, ContentOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .xobject m res kind body => by
    simp [ContentOp.ink, ContentOp.lines, ContentOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .group m gs clips body => by
    rw [ContentOp.ink, ContentOp.linesList, ContentOp.linesList, List.append_nil, ContentOp.lines,
      ContentOp.lines, List.toList_toArray, ContentOp.linesList_ink body.toList, stripMarks_cons_op,
      stripMarks_append, stripMarks_cons_op, stripMarks_nil]
  | .image x y w h res => by
    simp [ContentOp.ink, ContentOp.lines, ContentOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .imageMissing x y w h => by
    simp [ContentOp.ink, ContentOp.lines, ContentOp.linesList, stripMarks_cons_op, stripMarks_nil]
  | .text ops => by
    rw [ContentOp.ink, ContentOp.linesList, ContentOp.linesList, List.append_nil, ContentOp.lines,
      ContentOp.lines, inkText, List.toList_toArray, TextOp.linesList_ink, stripMarks_cons_op,
      stripMarks_append, stripMarks_cons_op, stripMarks_nil]
  | .marked t body => by
    rw [ContentOp.ink, ContentOp.lines, ContentOp.linesList_ink body.toList, stripMarks_cons_open,
      stripMarks_append, stripMarks_emc, List.append_nil]

private theorem ContentOp.linesList_ink : ∀ l : List ContentOp,
    ContentOp.linesList (ContentOp.inkList l) = stripMarks (ContentOp.linesList l)
  | [] => rfl
  | o :: rest => by
    rw [ContentOp.inkList, ContentOp.linesList, ContentOp.linesList_append, ContentOp.lines_ink o,
      ContentOp.linesList_ink rest, stripMarks_append]

end

/-- **The ink's stream is the stream with its marked-content lines
removed.** `inkOps` drops every wrapper; on the bytes that is exactly a
strip of the opening and `EMC` lines (`render_lines_exact`) — the equation
the artifact acceptance's stripped-stream comparison executes. -/
public theorem inkOps_lines_exact (ops : Array ContentOp) : lines (inkOps ops) = stripMarks (lines ops) := by
  simp only [lines, inkOps, List.toList_toArray]
  exact ContentOp.linesList_ink _

public theorem render_inkOps_exact (ops : Array ContentOp) :
    render (inkOps ops) = joinLines (stripMarks (lines ops)) := by
  rw [render_lines_exact, inkOps_lines_exact]

/-! ### The text walk under `inkText` -/

private theorem inkText_append (a b : Array TextOp) : inkText (a ++ b) = inkText a ++ inkText b := by
  simp [inkText, TextOp.inkList_append]

private theorem inkText_push (ops : Array TextOp) (o : TextOp) :
    inkText (ops.push o) = inkText ops ++ o.ink.toArray := by
  simp [inkText, TextOp.inkList_append, TextOp.inkList]

private theorem inkText_push_marked (ops : Array TextOp) (t : MarkTag) (body : Array TextOp) :
    inkText (ops.push (.marked t body)) = inkText ops ++ inkText body := by
  simp [inkText, TextOp.inkList_append, TextOp.inkList, TextOp.ink]

/-- A state's ops seen through `inkText`: what the text walk decides that
the marking cannot change. -/
private def TextSt.plain (st : TextSt) : TextSt := { st with ops := inkText st.ops }

private theorem lineSt_plain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (og : Origin) (st : TextSt) (l : LineOut) :
    lineSt geom remap imgMap og st.plain l = lineSt geom remap imgMap og st l := by
  simp [lineSt, TextSt.plain]

/-- **Marking a line moves no ink**: the wrapped line and the plain line
agree on everything but the wrapper — whichever wrapper the origin chose,
and when the line's operators are empty and nothing is wrapped. -/
private theorem stepLine_plain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap tags st l).plain
      = (stepLinePlain geom remap imgMap tags st l).plain := by
  simp only [stepLine, stepLinePlain, TextSt.plain]
  have hempty : ∀ (a b : Array TextOp), b.isEmpty = true → inkText a = inkText (a ++ b) := by
    intro a b hb
    rw [Array.isEmpty_iff.mp hb, Array.append_empty]
  split
  · simp [inkText_push_marked, inkText_append]
  · split
    · rename_i he
      rw [hempty _ _ he]
    · simp [inkText_push_marked, inkText_append]
  · split
    · rename_i he
      rw [hempty _ _ he]
    · simp [inkText_push_marked, inkText_append]

private theorem stepLinePlain_resp (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) {st st' : TextSt} (h : st.plain = st'.plain) (l : LineOut) :
    (stepLinePlain geom remap imgMap tags st l).plain
      = (stepLinePlain geom remap imgMap tags st' l).plain := by
  have hl : lineSt geom remap imgMap (Origin.of tags l) st l
      = lineSt geom remap imgMap (Origin.of tags l) st' l := by
    rw [← lineSt_plain geom remap imgMap _ st, h, lineSt_plain]
  have ho : inkText st.ops = inkText st'.ops := congrArg TextSt.ops h
  simp only [stepLinePlain, TextSt.plain, hl, inkText_append, ho]

private theorem foldl_stepLinePlain_resp (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (ls : List LineOut) {st st' : TextSt}
    (h : st.plain = st'.plain) :
    (ls.foldl (stepLinePlain geom remap imgMap tags) st).plain
      = (ls.foldl (stepLinePlain geom remap imgMap tags) st').plain := by
  induction ls generalizing st st' with
  | nil => exact h
  | cons l rest ih => exact ih (stepLinePlain_resp geom remap imgMap tags h l)

/-- The marked walk and the plain walk agree under `inkText`, line by line. -/
private theorem foldl_stepLine_plain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (ls : List LineOut) (st : TextSt) :
    (ls.foldl (stepLine geom remap imgMap tags) st).plain
      = (ls.foldl (stepLinePlain geom remap imgMap tags) st).plain := by
  induction ls generalizing st with
  | nil => rfl
  | cons l rest ih =>
    simp only [List.foldl_cons]
    rw [ih, foldl_stepLinePlain_resp geom remap imgMap tags rest
      (stepLine_plain geom remap imgMap tags st l)]

/-! ### The plain walk pushes only leaves -/

private theorem op_plainOps (st : TextSt) (o : TextOp) (h : inkText st.ops = st.ops) (hl : o.ink = [o]) :
    inkText (st.op o).ops = (st.op o).ops := by
  simp [TextSt.op, inkText_push, h, hl]

private theorem closeTJ_plainOps (st : TextSt) (h : inkText st.ops = st.ops) :
    inkText st.closeTJ.ops = st.closeTJ.ops := by
  unfold TextSt.closeTJ
  split
  · exact h
  · exact op_plainOps st _ h (by simp [TextOp.ink])

private theorem moveTo_plainOps (st : TextSt) (y : Sp) (h : inkText st.ops = st.ops) :
    inkText (st.moveTo y).ops = (st.moveTo y).ops :=
  op_plainOps _ _ (closeTJ_plainOps st h) (by simp [TextOp.ink])

private theorem toPen_plainOps (st : TextSt) (c : Bool) (y : Sp) (h : inkText st.ops = st.ops) :
    inkText (st.toPen c y).ops = (st.toPen c y).ops := by
  unfold TextSt.toPen
  split
  · simp only []
    split
    · split
      · exact h
      · exact h
    · exact moveTo_plainOps st y h
  · exact moveTo_plainOps st y h

private theorem setFont_plainOps (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp)
    (h : inkText st.ops = st.ops) :
    inkText (st.setFont remap idx size).ops = (st.setFont remap idx size).ops := by
  unfold TextSt.setFont
  split
  · exact op_plainOps _ _ h (by simp [TextOp.ink])
  · exact h

private theorem setColor_plainOps (st : TextSt) (c : Ir.Color) (h : inkText st.ops = st.ops) :
    inkText (st.setColor c).ops = (st.setColor c).ops := by
  unfold TextSt.setColor
  split
  · exact op_plainOps _ _ h (by simp [TextOp.ink])
  · exact h

private theorem setFace_plainOps (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Sp) (c : Ir.Color)
    (h : inkText st.ops = st.ops) :
    inkText (st.setFace remap idx size c).ops = (st.setFace remap idx size c).ops :=
  setColor_plainOps _ _ (setFont_plainOps _ _ _ _ (closeTJ_plainOps _ h))

private theorem stepRun_plainOps (remap : Array Nat) (ls y : Sp) (st : TextSt) (idx : Nat) (c : Ir.Color)
    (w : Sp) (glyphs : Array (Nat × Char × Sp)) (ss raise : Sp) (h : inkText st.ops = st.ops) :
    inkText (stepRun remap ls y st idx c w glyphs ss raise).ops
      = (stepRun remap ls y st idx c w glyphs ss raise).ops := by
  unfold stepRun
  split
  · exact h
  · simp only [TextSt.pushRun]
    split <;> split
    all_goals first
      | exact setFace_plainOps _ _ _ _ _ (toPen_plainOps _ _ _ h)
      | exact toPen_plainOps _ _ _ h

private theorem stepSeg_plainOps (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp)
    (og : Origin) (st : TextSt) (seg : Seg) (h : inkText st.ops = st.ops) :
    inkText (stepSeg remap imgMap ls y og st seg).ops = (stepSeg remap imgMap ls y og st seg).ops := by
  cases seg with
  | rule | decoration => exact h
  | image => exact h
  | gap | decoratedGap => exact h
  | poly => exact h
  | run => exact stepRun_plainOps _ _ _ _ _ _ _ _ _ _ h

private theorem foldl_segs_plainOps (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Sp)
    (og : Origin) (segs : List Seg) (st : TextSt) (h : inkText st.ops = st.ops) :
    inkText (segs.foldl (stepSeg remap imgMap ls y og) st).ops
      = (segs.foldl (stepSeg remap imgMap ls y og) st).ops := by
  induction segs generalizing st with
  | nil => exact h
  | cons s rest ih => exact ih _ (stepSeg_plainOps _ _ _ _ _ _ _ h)

private theorem lineSt_plainOps (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (og : Origin) (st : TextSt) (l : LineOut) :
    inkText (lineSt geom remap imgMap og st l).ops = (lineSt geom remap imgMap og st l).ops := by
  unfold lineSt
  simp only []
  apply closeTJ_plainOps
  rw [← Array.foldl_toList]
  apply foldl_segs_plainOps
  split
  · exact op_plainOps _ _ rfl (by simp [TextOp.ink])
  · rfl

private theorem stepLinePlain_plainOps (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) (h : inkText st.ops = st.ops) :
    inkText (stepLinePlain geom remap imgMap tags st l).ops
      = (stepLinePlain geom remap imgMap tags st l).ops := by
  simp only [stepLinePlain, inkText_append, h, lineSt_plainOps]

private theorem foldl_stepLinePlain_plainOps (geom : Geom) (remap : Array Nat)
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ls : List LineOut) (st : TextSt)
    (h : inkText st.ops = st.ops) :
    inkText (ls.foldl (stepLinePlain geom remap imgMap tags) st).ops
      = (ls.foldl (stepLinePlain geom remap imgMap tags) st).ops := by
  induction ls generalizing st with
  | nil => exact h
  | cons l rest ih => exact ih _ (stepLinePlain_plainOps _ _ _ _ _ _ h)

/-! ### The theorems this layer owes -/

private theorem artifact_ink (k : Option ArtifactKind) (o : ContentOp) : (artifact k o).ink = o.ink := by
  simp [artifact, ContentOp.ink, ContentOp.inkList]

private theorem artifactBlock_ink (k : Option ArtifactKind) (ops : Array ContentOp) :
    ContentOp.inkList (artifactBlock k ops).toList = ContentOp.inkList ops.toList := by
  unfold artifactBlock
  split
  · rename_i h
    simp [Array.isEmpty_iff.mp h, ContentOp.inkList]
  · simp [ContentOp.inkList, ContentOp.ink]

private theorem mem_artifactBlock {k : Option ArtifactKind} {ops : Array ContentOp} {o : ContentOp}
    (h : o ∈ artifactBlock k ops) : o = .marked (.artifact k) ops := by
  unfold artifactBlock at h
  split at h
  · simp at h
  · simpa using h

private theorem inkList_map {α : Type} (f g : α → ContentOp) (l : List α) (h : ∀ a, (f a).ink = [g a]) :
    ContentOp.inkList (l.map f) = l.map g := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [ContentOp.inkList, h, ih]

private theorem imageOp_ink (i : ImgOut) : (imageOp i).ink = [imageOpPlain i] := by
  unfold imageOp imageOpPlain
  split <;> simp [artifact_ink, ContentOp.ink, ContentOp.inkList]

/-- The ink an open path group holds. -/
private def groupInk : Option (Option Nat × Array ContentOp) → List ContentOp
  | none => []
  | some (_, ops) => ContentOp.inkList ops.toList

private theorem flushGroup_ink (tags : Array (Option String)) (out : Array ContentOp)
    (cur : Option (Option Nat × Array ContentOp)) :
    ContentOp.inkList (flushGroup tags out cur).toList
      = ContentOp.inkList out.toList ++ (groupInk cur) := by
  cases cur with
  | none => simp [flushGroup, groupInk]
  | some g =>
    obtain ⟨lf, ops⟩ := g
    simp [flushGroup, groupInk, Array.toList_push, ContentOp.inkList_append, ContentOp.inkList,
      ContentOp.ink]

mutual

private theorem figureOnly_ink : ∀ (o : ContentOp), o.figureOnly = true → o.ink = [o]
  | .paint _ _ _ _, _ => rfl
  | .shade _ _, _ => rfl
  | .outline _ _ _, _ => rfl
  | .xobject _ _ _ _, _ => rfl
  | .group m gs clips body, h => by
    simp only [ContentOp.figureOnly] at h
    simp only [ContentOp.ink, figureOnlyList_ink body.toList h, Array.toArray_toList]
  | .fill _ _ _ _ _, h => by simp [ContentOp.figureOnly] at h
  | .text _, h => by simp [ContentOp.figureOnly] at h
  | .image _ _ _ _ _, h => by simp [ContentOp.figureOnly] at h
  | .imageMissing _ _ _ _, h => by simp [ContentOp.figureOnly] at h
  | .marked _ _, h => by simp [ContentOp.figureOnly] at h

private theorem figureOnlyList_ink : ∀ (l : List ContentOp), ContentOp.figureOnlyList l = true →
    ContentOp.inkList l = l
  | [], _ => rfl
  | o :: rest, h => by
    simp only [ContentOp.figureOnlyList, Bool.and_eq_true] at h
    simp only [ContentOp.inkList, figureOnly_ink o h.1, figureOnlyList_ink rest h.2,
      List.singleton_append]

end

private theorem inkPaint_ink (geom : Geom) (ix : GfxPdf.Request → Nat) (k : InkOut) :
    ContentOp.inkList (inkPaint geom ix k).toList = (inkPaint geom ix k).toList :=
  figureOnlyList_ink _ (figureOnly_of_mem _ (inkPaint_figureOnly geom ix k))

/-- Grouping a page's ink per picture moves no mark: the ink under the
groups is the inks' operators, in order. -/
private theorem inkGroupsList_ink (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tags : Array (Option String)) (inks : List InkOut)
    (out : Array ContentOp) (cur : Option (Option Nat × Array ContentOp)) :
    ContentOp.inkList (inkGroupsList geom ix tags out cur inks).toList
      = ContentOp.inkList out.toList ++ (groupInk cur)
        ++ inks.flatMap (fun k => (inkPaint geom ix k).toList) := by
  induction inks generalizing out cur with
  | nil => simp [inkGroupsList, flushGroup_ink]
  | cons k rest ih =>
    simp only [inkGroupsList]
    split
    · next he =>
      rw [ih]
      simp [Array.isEmpty_iff.mp he]
    · split
      · split
        · rw [ih]
          simp [groupInk, ContentOp.inkList_append, inkPaint_ink, List.append_assoc]
        · rw [ih, flushGroup_ink]
          simp [groupInk, inkPaint_ink, List.append_assoc]
      · rw [ih]
        simp [groupInk, inkPaint_ink, List.append_assoc]

private theorem inkGroups_ink (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tags : Array (Option String)) (inks : Array InkOut) :
    ContentOp.inkList (inkGroups geom ix tags inks).toList
      = inks.toList.flatMap (fun k => (inkPaint geom ix k).toList) := by
  unfold inkGroups
  rw [inkGroupsList_ink]
  simp [groupInk, ContentOp.inkList]

mutual

/-- Numbering the identifiers touches no ink. -/
private theorem TextOp.number_ink : ∀ (o : TextOp) (n : Nat), (TextOp.number n o).1.ink = o.ink
  | .scale _, _ => rfl
  | .move _ _, _ => rfl
  | .font _ _, _ => rfl
  | .color _, _ => rfl
  | .show _, _ => rfl
  | .marked (.artifact a) body, n => by
    have h := TextOp.numberList_ink body.toList n #[]
    simp only [TextOp.inkList, List.nil_append] at h
    simp [TextOp.number, TextOp.ink, h]
  | .marked (.content s m k) body, n => by
    have h := TextOp.numberList_ink body.toList (n + 1) #[]
    simp only [TextOp.inkList, List.nil_append] at h
    simp [TextOp.number, TextOp.ink, h]

private theorem TextOp.numberList_ink : ∀ (l : List TextOp) (n : Nat) (acc : Array TextOp),
    TextOp.inkList (TextOp.numberList n acc l).1.toList
      = TextOp.inkList acc.toList ++ (TextOp.inkList l)
  | [], n, acc => by simp [TextOp.numberList, TextOp.inkList]
  | o :: rest, n, acc => by
    rw [TextOp.numberList]
    rw [TextOp.numberList_ink rest, Array.toList_push, TextOp.inkList_append, TextOp.inkList,
      TextOp.inkList, TextOp.number_ink o n]
    simp [TextOp.inkList]

end

mutual

private theorem ContentOp.number_ink : ∀ (o : ContentOp) (n : Nat), (ContentOp.number n o).1.ink = o.ink
  | .fill _ _ _ _ _, _ => rfl
  | .paint _ _ _ _, _ => rfl
  | .shade _ _, _ => rfl
  | .outline _ _ _, _ => rfl
  | .xobject _ _ _ _, _ => rfl
  | .group m gs clips body, n => by
    have h := ContentOp.numberList_ink body.toList n #[]
    simp only [ContentOp.inkList, List.nil_append] at h
    simp [ContentOp.number, ContentOp.ink, h]
  | .image _ _ _ _ _, _ => rfl
  | .imageMissing _ _ _ _, _ => rfl
  | .text ops, n => by
    have h := TextOp.numberList_ink ops.toList n #[]
    simp only [TextOp.inkList, List.nil_append] at h
    simp [ContentOp.number, ContentOp.ink, inkText, h]
  | .marked (.artifact a) body, n => by
    have h := ContentOp.numberList_ink body.toList n #[]
    simp only [ContentOp.inkList, List.nil_append] at h
    simp [ContentOp.number, ContentOp.ink, h]
  | .marked (.content s m k) body, n => by
    have h := ContentOp.numberList_ink body.toList (n + 1) #[]
    simp only [ContentOp.inkList, List.nil_append] at h
    simp [ContentOp.number, ContentOp.ink, h]

private theorem ContentOp.numberList_ink : ∀ (l : List ContentOp) (n : Nat) (acc : Array ContentOp),
    ContentOp.inkList (ContentOp.numberList n acc l).1.toList
      = ContentOp.inkList acc.toList ++ (ContentOp.inkList l)
  | [], n, acc => by simp [ContentOp.numberList, ContentOp.inkList]
  | o :: rest, n, acc => by
    rw [ContentOp.numberList]
    rw [ContentOp.numberList_ink rest, Array.toList_push, ContentOp.inkList_append,
      ContentOp.inkList, ContentOp.inkList, ContentOp.number_ink o n]
    simp [ContentOp.inkList]

end

private theorem numberMarks_ink_list (ops : Array ContentOp) :
    ContentOp.inkList (numberMarks ops).toList = ContentOp.inkList ops.toList := by
  unfold numberMarks
  rw [ContentOp.numberList_ink]
  simp [ContentOp.inkList]

public theorem numberMarks_ink (ops : Array ContentOp) : inkOps (numberMarks ops) = inkOps ops := by
  unfold inkOps
  rw [numberMarks_ink_list]

/-- **Marking moves no ink.** The stream this layer builds, with every
marked-content wrapper removed, is the stream the writer built before the
layer existed (`contentOpsPlain`, the specification twin): same
operators, same order, same operands — so the same bytes
(`render_inkOps_exact`), and the strip of marked-content lines the
acceptance runs is this equation on the file. Both wrapper kinds are
covered: artifacts and structure content alike hide nothing, and the
identifier numbering rewrites tags only. A fact of the content stream,
not a projection of an IR statement: the IR never sees marked content. -/
public theorem mark_ink_exact (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (page : PageOut) :
    inkOps (contentOps geom remap widths imgMap tags ix page)
      = contentOpsPlain geom remap widths imgMap tags ix page := by
  unfold contentOps contentOpsPlain
  simp only [inkOps, Array.toList_append, ContentOp.inkList_append, numberMarks_ink_list]
  have hp := foldl_stepLine_plain geom remap imgMap tags page.lines.toList { widths }
  rw [Array.foldl_toList, Array.foldl_toList] at hp
  have hpo := foldl_stepLinePlain_plainOps geom remap imgMap tags page.lines.toList { widths } rfl
  rw [Array.foldl_toList] at hpo
  have hops : inkText (page.lines.foldl (stepLine geom remap imgMap tags) { widths }).ops
      = (page.lines.foldl (stepLinePlain geom remap imgMap tags) { widths }).ops := by
    rw [← hpo]; exact congrArg TextSt.ops hp
  have himg := congrArg TextSt.images hp
  have hrul := congrArg TextSt.rules hp
  have hpol := congrArg TextSt.polys hp
  simp only [TextSt.plain] at himg hrul hpol
  simp only [Array.toList_push, ContentOp.inkList_append,
    artifactBlock_ink, inkGroups_ink, Array.toList_map, Array.toList_append,
    ContentOp.inkList, ContentOp.ink, hops, himg, hrul, hpol, List.append_nil]
  rw [inkList_map _ (fun f => ContentOp.fill f.color (geom.bleed + f.x)
      (geom.bleed + geom.pageH - f.y - f.h) f.w f.h) _ (fun f => by simp [ContentOp.ink]),
    inkList_map _ imageOpPlain _ imageOp_ink,
    inkList_map _ (fun (t : Ir.Color × Sp × Sp × Sp × Sp) =>
      ContentOp.fill t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) _ (fun t => by simp [ContentOp.ink]),
    inkList_map _ polyOp _ (fun p => by simp [polyOp, ContentOp.ink])]
  apply Array.toList_inj.mp
  simp [Array.toList_append, Array.toList_push, Array.toList_map, Array.toList_flatMap]

/-! ### Every painting operator sits under a wrapper -/

private def TextOp.isMarked : TextOp → Bool
  | .marked _ _ => true
  | .scale _ => false
  | .move _ _ => false
  | .font _ _ => false
  | .color _ => false
  | .show _ => false

/-- A page-level operation the layer leaves nothing bare under: a wrapper,
or the text object with every operator of its own wrapped. -/
public def ContentOp.wrapped : ContentOp → Bool
  | .marked _ _ => true
  | .text ops => ops.all TextOp.isMarked
  | .fill _ _ _ _ _ => false
  | .paint _ _ _ _ => false
  | .shade _ _ => false
  | .outline _ _ _ => false
  | .group _ _ _ _ => false
  | .xobject _ _ _ _ => false
  | .image _ _ _ _ _ => false
  | .imageMissing _ _ _ _ => false

private theorem TextOp.number_marked (o : TextOp) (n : Nat) : (TextOp.number n o).1.isMarked = o.isMarked := by
  cases o with
  | marked t body => cases t <;> simp [TextOp.number, TextOp.isMarked]
  | _ => rfl

private theorem TextOp.numberList_marked (l : List TextOp) (n : Nat) (acc : Array TextOp)
    (ha : ∀ o ∈ acc, o.isMarked = true) (hl : ∀ o ∈ l, o.isMarked = true) :
    ∀ o ∈ (TextOp.numberList n acc l).1, o.isMarked = true := by
  induction l generalizing n acc with
  | nil => simpa [TextOp.numberList] using ha
  | cons o rest ih =>
    rw [TextOp.numberList]
    refine ih _ _ ?_ (fun o h => hl o (List.mem_cons_of_mem _ h))
    intro o' h
    simp only [Array.mem_push] at h
    rcases h with h | rfl
    · exact ha o' h
    · rw [TextOp.number_marked]
      exact hl o (List.mem_cons_self ..)

private theorem ContentOp.number_wrapped (o : ContentOp) (n : Nat) (h : o.wrapped = true) :
    (ContentOp.number n o).1.wrapped = true := by
  cases o with
  | text ops =>
    simp only [ContentOp.number, ContentOp.wrapped, Array.all_eq_true_iff_forall_mem] at h ⊢
    exact TextOp.numberList_marked ops.toList n #[] (by simp) (fun o h' => h o (Array.mem_def.mpr h'))
  | marked t body => cases t <;> simp [ContentOp.number, ContentOp.wrapped]
  | fill => exact absurd h (by simp [ContentOp.wrapped])
  | paint => exact absurd h (by simp [ContentOp.wrapped])
  | shade => exact absurd h (by simp [ContentOp.wrapped])
  | outline => exact absurd h (by simp [ContentOp.wrapped])
  | group => exact absurd h (by simp [ContentOp.wrapped])
  | xobject => exact absurd h (by simp [ContentOp.wrapped])
  | image => exact absurd h (by simp [ContentOp.wrapped])
  | imageMissing => exact absurd h (by simp [ContentOp.wrapped])

private theorem ContentOp.numberList_wrapped (l : List ContentOp) (n : Nat) (acc : Array ContentOp)
    (ha : ∀ o ∈ acc, o.wrapped = true) (hl : ∀ o ∈ l, o.wrapped = true) :
    ∀ o ∈ (ContentOp.numberList n acc l).1, o.wrapped = true := by
  induction l generalizing n acc with
  | nil => simpa [ContentOp.numberList] using ha
  | cons o rest ih =>
    rw [ContentOp.numberList]
    refine ih _ _ ?_ (fun o h => hl o (List.mem_cons_of_mem _ h))
    intro o' h
    simp only [Array.mem_push] at h
    rcases h with h | rfl
    · exact ha o' h
    · exact ContentOp.number_wrapped o n (hl o (List.mem_cons_self ..))

/-- Every operator the line walk puts on the text object is under a
wrapper: a line's operators are wrapped or, when empty, absent. -/
private theorem stepLine_marked (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut)
    (h : ∀ o ∈ st.ops, o.isMarked = true) :
    ∀ o ∈ (stepLine geom remap imgMap tags st l).ops, o.isMarked = true := by
  have push : ∀ t body o, o ∈ st.ops.push (.marked t body) → o.isMarked = true := by
    intro t body o ho
    simp only [Array.mem_push] at ho
    rcases ho with ho | rfl
    · exact h o ho
    · rfl
  intro o
  simp only [stepLine]
  split
  · exact push _ _ o
  · split
    · exact h o
    · exact push _ _ o
  · split
    · exact h o
    · exact push _ _ o

private theorem foldl_lines_marked (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (lines : List LineOut) (st : TextSt)
    (h : ∀ o ∈ st.ops, o.isMarked = true) :
    ∀ o ∈ (lines.foldl (stepLine geom remap imgMap tags) st).ops, o.isMarked = true := by
  induction lines generalizing st with
  | nil => exact h
  | cons l rest ih => exact ih _ (stepLine_marked geom remap imgMap tags st l h)

private theorem flushGroup_wrapped (tags : Array (Option String)) (out : Array ContentOp)
    (cur : Option (Option Nat × Array ContentOp)) (ho : ∀ o ∈ out, o.wrapped = true) :
    ∀ o ∈ flushGroup tags out cur, o.wrapped = true := by
  intro o h
  cases cur with
  | none => exact ho o h
  | some g =>
    simp only [flushGroup, Array.mem_push] at h
    rcases h with h | rfl
    · exact ho o h
    · rfl

private theorem imageOp_wrapped (i : ImgOut) : (imageOp i).wrapped = true := by
  unfold imageOp
  split <;> rfl

/-- **Every painting operator sits under exactly one wrapper.** At the top
of the stream every operation is a marked-content sequence or the text
object, and every operator of the text object is a marked-content
sequence: no fill, path, glyph run or image is bare — real content under
its structure type, everything else an artifact. The identifier half of
the statement is `numberMarks_mcids_exact`. -/
public theorem wrapped_covers (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (page : PageOut) :
    ∀ o ∈ contentOps geom remap widths imgMap tags ix page, o.wrapped = true := by
  unfold contentOps numberMarks
  intro o ho
  simp only [Array.mem_append] at ho
  rcases ho with (hf | hm) | hr
  · rw [mem_artifactBlock hf]; rfl
  · refine ContentOp.numberList_wrapped _ _ _ (by simp) ?_ o hm
    intro o ho
    simp only [Array.mem_toList_iff, Array.mem_append, Array.mem_push, Array.mem_map] at ho
    rcases ho with (hp | rfl) | ⟨i, _, rfl⟩
    · obtain ⟨t, body, rfl, _⟩ := inkGroups_shape geom ix tags page.inks o hp
      rfl
    · simp only [ContentOp.wrapped, Array.all_eq_true_iff_forall_mem]
      have := foldl_lines_marked geom remap imgMap tags page.lines.toList { widths } (by simp)
      rw [Array.foldl_toList] at this
      exact this
    · exact imageOp_wrapped i
  · rw [mem_artifactBlock hr]; rfl

/-- **No decoration is left bare** — the corollary `wrapped_covers`
projects: every fill and every placeholder box sits under a wrapper. -/
public theorem artifacts_covers (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (page : PageOut) :
    ∀ o ∈ contentOps geom remap widths imgMap tags ix page, o.decoration = false := by
  intro o ho
  have h := wrapped_covers geom remap widths imgMap tags ix page o ho
  cases o <;> simp_all [ContentOp.wrapped, ContentOp.decoration]

/-! ### Identifiers in stream order -/

/-- A content opener's identifier and leaf; nothing for an artifact or an
operator. -/
private def Line.contentOpen : Line → Option (Nat × Nat)
  | .open (.content _ m k) => some (m, k)
  | .open (.artifact _) => none
  | .op _ => none
  | .emc => none

public def Line.isPaginationOpen : Line → Bool
  | .open (.artifact (some .pagination)) => true
  | .open (.artifact (some .layout)) => false
  | .open (.artifact (some .page)) => false
  | .open (.artifact none) => false
  | .open (.content _ _ _) => false
  | .op _ => false
  | .emc => false

/-- The `(identifier, leaf)` pairs a stream's content openers carry, in
stream order. -/
public def contentOpens (ls : List Line) : List (Nat × Nat) := ls.filterMap Line.contentOpen

mutual

/-- The content openers under a text operator, without rendering them:
`TextOp.lines` spells every operator on the way to the same list
(`marksList_eq_contentOpens`), which on a rule-heavy page is a full render
paid a second time. -/
private def TextOp.marks (acc : Array (Nat × Nat)) : TextOp → Array (Nat × Nat)
  | .scale _ => acc
  | .move _ _ => acc
  | .font _ _ => acc
  | .color _ => acc
  | .show _ => acc
  | .marked (.artifact _) body => TextOp.marksList acc body.toList
  | .marked (.content _ m k) body => TextOp.marksList (acc.push (m, k)) body.toList

private def TextOp.marksList (acc : Array (Nat × Nat)) : List TextOp → Array (Nat × Nat)
  | [] => acc
  | o :: rest => TextOp.marksList (TextOp.marks acc o) rest

end

mutual

private def ContentOp.marks (acc : Array (Nat × Nat)) : ContentOp → Array (Nat × Nat)
  | .fill _ _ _ _ _ => acc
  | .paint _ _ _ _ => acc
  | .shade _ _ => acc
  | .outline _ _ _ => acc
  | .xobject _ _ _ _ => acc
  | .group _ _ _ body => ContentOp.marksList acc body.toList
  | .text ops => TextOp.marksList acc ops.toList
  | .image _ _ _ _ _ => acc
  | .imageMissing _ _ _ _ => acc
  | .marked (.artifact _) body => ContentOp.marksList acc body.toList
  | .marked (.content _ m k) body => ContentOp.marksList (acc.push (m, k)) body.toList

private def ContentOp.marksList (acc : Array (Nat × Nat)) : List ContentOp → Array (Nat × Nat)
  | [] => acc
  | o :: rest => ContentOp.marksList (ContentOp.marks acc o) rest

end

/-- The marked content of one page: its identifiers and the leaves they
paint, read off the typed stream — what the structure walk keys on. -/
public def pageMarks (ops : Array ContentOp) : Array (Nat × Nat) := ContentOp.marksList #[] ops.toList

private theorem contentOpens_append (a b : List Line) :
    contentOpens (a ++ b) = contentOpens a ++ contentOpens b := by
  simp [contentOpens, List.filterMap_append]

private theorem contentOpens_op (s : String) : contentOpens [.op s] = [] := rfl
private theorem contentOpens_emc : contentOpens [.emc] = [] := rfl
private theorem contentOpens_nil : contentOpens [] = [] := rfl

/-- Two adjacent ranges are one, however the second's start is spelled. -/
private theorem range'_append_of (s m s' n : Nat) (h : s' = s + m) :
    List.range' s m ++ List.range' s' n = List.range' s (m + n) := by
  subst h
  have := @List.range'_append s m n 1
  simpa only [Nat.one_mul] using this

private theorem TextOp.linesList_push (acc : Array TextOp) (o : TextOp) :
    TextOp.linesList (acc.push o).toList = TextOp.linesList acc.toList ++ o.lines := by
  rw [Array.toList_push, TextOp.linesList_append]
  simp [TextOp.linesList]

private theorem ContentOp.linesList_push (acc : Array ContentOp) (o : ContentOp) :
    ContentOp.linesList (acc.push o).toList = ContentOp.linesList acc.toList ++ o.lines := by
  rw [Array.toList_push, ContentOp.linesList_append]
  simp [ContentOp.linesList]

private theorem range'_cons_of (n m : Nat) (h : n + 1 ≤ m) :
    n :: List.range' (n + 1) (m - (n + 1)) = List.range' n (m - n) := by
  rw [show m - n = (m - (n + 1)) + 1 by omega]
  rfl

mutual

/-- The identifiers the numbering hands out are the run from `n` of the
count it returns, in stream order. -/
private theorem TextOp.number_mcids : ∀ (o : TextOp) (n : Nat),
    (contentOpens (TextOp.number n o).1.lines).map Prod.fst
      = List.range' n ((TextOp.number n o).2 - n)
    ∧ n ≤ (TextOp.number n o).2
  | .scale _, _ => by simp [TextOp.number, TextOp.lines, contentOpens, Line.contentOpen]
  | .move _ _, _ => by simp [TextOp.number, TextOp.lines, contentOpens, Line.contentOpen]
  | .font _ _, _ => by simp [TextOp.number, TextOp.lines, contentOpens, Line.contentOpen]
  | .color _, _ => by simp [TextOp.number, TextOp.lines, contentOpens, Line.contentOpen]
  | .show _, _ => by simp [TextOp.number, TextOp.lines, contentOpens, Line.contentOpen]
  | .marked (.artifact a) body, n => by
    have h := TextOp.numberList_mcids body.toList n #[]
    simp only [TextOp.linesList, contentOpens_nil, List.map_nil,
      List.nil_append] at h
    simp only [TextOp.number, TextOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen,
      List.filterMap_append, List.filterMap_nil, List.append_nil]
    exact h
  | .marked (.content s m k) body, n => by
    have h := TextOp.numberList_mcids body.toList (n + 1) #[]
    simp only [TextOp.linesList, contentOpens_nil, List.map_nil,
      List.nil_append] at h
    simp only [TextOp.number, TextOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen,
      List.filterMap_append, List.filterMap_nil, List.append_nil, List.map_cons]
    rw [← contentOpens, h.1, range'_cons_of _ _ h.2]
    exact ⟨rfl, by omega⟩

private theorem TextOp.numberList_mcids : ∀ (l : List TextOp) (n : Nat) (acc : Array TextOp),
    (contentOpens (TextOp.linesList (TextOp.numberList n acc l).1.toList)).map Prod.fst
      = (contentOpens (TextOp.linesList acc.toList)).map Prod.fst
        ++ List.range' n ((TextOp.numberList n acc l).2 - n)
    ∧ n ≤ (TextOp.numberList n acc l).2
  | [], n, acc => by simp [TextOp.numberList]
  | o :: rest, n, acc => by
    rw [TextOp.numberList]
    have ho := TextOp.number_mcids o n
    have ih := TextOp.numberList_mcids rest (TextOp.number n o).2 (acc.push (TextOp.number n o).1)
    rw [ih.1, TextOp.linesList_push, contentOpens_append, List.map_append, ho.1, List.append_assoc,
      range'_append_of _ _ _ _ (Nat.add_sub_cancel' ho.2).symm]
    refine ⟨?_, by omega⟩
    congr 2
    omega

end

mutual

private theorem ContentOp.number_mcids : ∀ (o : ContentOp) (n : Nat),
    (contentOpens (ContentOp.number n o).1.lines).map Prod.fst
      = List.range' n ((ContentOp.number n o).2 - n)
    ∧ n ≤ (ContentOp.number n o).2
  | .fill _ _ _ _ _, _ => by simp [ContentOp.number, ContentOp.lines, contentOpens, Line.contentOpen]
  | .paint _ _ _ _, _ => by simp [ContentOp.number, ContentOp.lines, contentOpens, Line.contentOpen]
  | .shade _ _, _ => by simp [ContentOp.number, ContentOp.lines, contentOpens, Line.contentOpen]
  | .outline _ _ _, _ => by simp [ContentOp.number, ContentOp.lines, contentOpens, Line.contentOpen]
  | .xobject _ _ _ _, _ => by
    simp [ContentOp.number, ContentOp.lines, contentOpens, Line.contentOpen]
  | .group m gs clips body, n => by
    have h := ContentOp.numberList_mcids body.toList n #[]
    simp only [ContentOp.linesList, contentOpens_nil, List.map_nil,
      List.nil_append] at h
    simp only [ContentOp.number, ContentOp.lines, contentOpens, List.filterMap_cons,
      Line.contentOpen, List.filterMap_append, List.filterMap_nil, List.append_nil]
    exact h
  | .image _ _ _ _ _, _ => by
    simp [ContentOp.number, ContentOp.lines, contentOpens, Line.contentOpen]
  | .imageMissing _ _ _ _, _ => by
    simp [ContentOp.number, ContentOp.lines, contentOpens, Line.contentOpen]
  | .text ops, n => by
    have h := TextOp.numberList_mcids ops.toList n #[]
    simp only [TextOp.linesList, contentOpens_nil, List.map_nil,
      List.nil_append] at h
    simp only [ContentOp.number, ContentOp.lines, contentOpens, List.filterMap_cons,
      Line.contentOpen, List.filterMap_append, List.filterMap_nil, List.append_nil]
    exact h
  | .marked (.artifact a) body, n => by
    have h := ContentOp.numberList_mcids body.toList n #[]
    simp only [ContentOp.linesList, contentOpens_nil, List.map_nil,
      List.nil_append] at h
    simp only [ContentOp.number, ContentOp.lines, contentOpens, List.filterMap_cons,
      Line.contentOpen, List.filterMap_append, List.filterMap_nil, List.append_nil]
    exact h
  | .marked (.content s m k) body, n => by
    have h := ContentOp.numberList_mcids body.toList (n + 1) #[]
    simp only [ContentOp.linesList, contentOpens_nil, List.map_nil,
      List.nil_append] at h
    simp only [ContentOp.number, ContentOp.lines, contentOpens, List.filterMap_cons,
      Line.contentOpen, List.filterMap_append, List.filterMap_nil, List.append_nil, List.map_cons]
    rw [← contentOpens, h.1, range'_cons_of _ _ h.2]
    exact ⟨rfl, by omega⟩

private theorem ContentOp.numberList_mcids : ∀ (l : List ContentOp) (n : Nat) (acc : Array ContentOp),
    (contentOpens (ContentOp.linesList (ContentOp.numberList n acc l).1.toList)).map Prod.fst
      = (contentOpens (ContentOp.linesList acc.toList)).map Prod.fst
        ++ List.range' n ((ContentOp.numberList n acc l).2 - n)
    ∧ n ≤ (ContentOp.numberList n acc l).2
  | [], n, acc => by simp [ContentOp.numberList]
  | o :: rest, n, acc => by
    rw [ContentOp.numberList]
    have ho := ContentOp.number_mcids o n
    have ih := ContentOp.numberList_mcids rest (ContentOp.number n o).2
      (acc.push (ContentOp.number n o).1)
    rw [ih.1, ContentOp.linesList_push, contentOpens_append, List.map_append, ho.1,
      List.append_assoc, range'_append_of _ _ _ _ (Nat.add_sub_cancel' ho.2).symm]
    refine ⟨?_, by omega⟩
    congr 2
    omega

end

mutual

private theorem TextOp.marks_eq_contentOpens : ∀ (o : TextOp) (acc : Array (Nat × Nat)),
    TextOp.marks acc o = acc ++ (contentOpens o.lines).toArray
  | .scale _, acc => by simp [TextOp.marks, TextOp.lines, contentOpens, Line.contentOpen]
  | .move _ _, acc => by simp [TextOp.marks, TextOp.lines, contentOpens, Line.contentOpen]
  | .font _ _, acc => by simp [TextOp.marks, TextOp.lines, contentOpens, Line.contentOpen]
  | .color _, acc => by simp [TextOp.marks, TextOp.lines, contentOpens, Line.contentOpen]
  | .show _, acc => by simp [TextOp.marks, TextOp.lines, contentOpens, Line.contentOpen]
  | .marked (.artifact a) body, acc => by
    rw [TextOp.marks, TextOp.marksList_eq_contentOpens body.toList]
    simp [TextOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen, List.filterMap_append]
  | .marked (.content s m k) body, acc => by
    rw [TextOp.marks, TextOp.marksList_eq_contentOpens body.toList]
    simp [TextOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen, List.filterMap_append]

private theorem TextOp.marksList_eq_contentOpens : ∀ (l : List TextOp) (acc : Array (Nat × Nat)),
    TextOp.marksList acc l = acc ++ (contentOpens (TextOp.linesList l)).toArray
  | [], acc => by simp [TextOp.marksList, TextOp.linesList, contentOpens]
  | o :: rest, acc => by
    rw [TextOp.marksList, TextOp.marksList_eq_contentOpens rest, TextOp.marks_eq_contentOpens o,
      TextOp.linesList, contentOpens_append]
    simp

end

mutual

private theorem ContentOp.marks_eq_contentOpens : ∀ (o : ContentOp) (acc : Array (Nat × Nat)),
    ContentOp.marks acc o = acc ++ (contentOpens o.lines).toArray
  | .fill _ _ _ _ _, acc => by simp [ContentOp.marks, ContentOp.lines, contentOpens, Line.contentOpen]
  | .paint _ _ _ _, acc => by simp [ContentOp.marks, ContentOp.lines, contentOpens, Line.contentOpen]
  | .shade _ _, acc => by simp [ContentOp.marks, ContentOp.lines, contentOpens, Line.contentOpen]
  | .outline _ _ _, acc => by simp [ContentOp.marks, ContentOp.lines, contentOpens, Line.contentOpen]
  | .xobject _ _ _ _, acc => by
    simp [ContentOp.marks, ContentOp.lines, contentOpens, Line.contentOpen]
  | .group m gs clips body, acc => by
    rw [ContentOp.marks, ContentOp.marksList_eq_contentOpens body.toList]
    simp [ContentOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen,
      List.filterMap_append]
  | .image _ _ _ _ _, acc => by
    simp [ContentOp.marks, ContentOp.lines, contentOpens, Line.contentOpen]
  | .imageMissing _ _ _ _, acc => by
    simp [ContentOp.marks, ContentOp.lines, contentOpens, Line.contentOpen]
  | .text ops, acc => by
    rw [ContentOp.marks, TextOp.marksList_eq_contentOpens ops.toList]
    simp [ContentOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen,
      List.filterMap_append]
  | .marked (.artifact a) body, acc => by
    rw [ContentOp.marks, ContentOp.marksList_eq_contentOpens body.toList]
    simp [ContentOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen,
      List.filterMap_append]
  | .marked (.content s m k) body, acc => by
    rw [ContentOp.marks, ContentOp.marksList_eq_contentOpens body.toList]
    simp [ContentOp.lines, contentOpens, List.filterMap_cons, Line.contentOpen,
      List.filterMap_append]

private theorem ContentOp.marksList_eq_contentOpens : ∀ (l : List ContentOp) (acc : Array (Nat × Nat)),
    ContentOp.marksList acc l = acc ++ (contentOpens (ContentOp.linesList l)).toArray
  | [], acc => by simp [ContentOp.marksList, ContentOp.linesList, contentOpens]
  | o :: rest, acc => by
    rw [ContentOp.marksList, ContentOp.marksList_eq_contentOpens rest,
      ContentOp.marks_eq_contentOpens o, ContentOp.linesList, contentOpens_append]
    simp

end

/-- The page's marks are the content openers of its lines, in order. -/
public theorem pageMarks_eq_contentOpens (ops : Array ContentOp) :
    pageMarks ops = (contentOpens (lines ops)).toArray := by
  unfold pageMarks lines
  rw [ContentOp.marksList_eq_contentOpens]
  simp

/-- **`numberMarks_mcids_exact`**: a numbered stream's marked-content
identifiers, in stream order, are exactly `0, 1, …, n−1` — unique per page
(§14.7.5.1), with no gap, however the construction nested them. -/
public theorem numberMarks_mcids_exact (ops : Array ContentOp) :
    (pageMarks (numberMarks ops)).toList.map Prod.fst = List.range (pageMarks (numberMarks ops)).size := by
  have h := ContentOp.numberList_mcids ops.toList 0 #[]
  simp only [ContentOp.linesList, contentOpens_nil, List.map_nil,
    List.nil_append, Nat.sub_zero] at h
  rw [pageMarks_eq_contentOpens]
  unfold numberMarks lines
  have hl := congrArg List.length h.1
  rw [List.length_map, List.length_range'] at hl
  rw [List.toList_toArray, List.size_toArray, hl, h.1, List.range_eq_range']

/-- A block of fills and filled paths opens no content sequence. -/
private theorem fillBlock_contentOpens (k : Option ArtifactKind) (fills : Array ContentOp)
    (hf : ∀ o ∈ fills, (∃ c x y w h, o = ContentOp.fill c x y w h) ∨
      ∃ fl st gs segs, o = ContentOp.paint fl st gs segs) :
    contentOpens (ContentOp.linesList (artifactBlock k fills).toList) = [] := by
  have hl : ∀ (l : List ContentOp), (∀ o ∈ l, (∃ c x y w h, o = ContentOp.fill c x y w h) ∨
      ∃ fl st gs segs, o = ContentOp.paint fl st gs segs) →
      contentOpens (ContentOp.linesList l) = [] := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons o rest ih =>
      intro h
      rw [ContentOp.linesList]
      rcases h o (List.mem_cons_self ..) with ⟨c, x, y, w, hh, rfl⟩ | ⟨fl, st, gs, segs, rfl⟩ <;>
        simp only [ContentOp.lines, contentOpens_append, contentOpens_op, List.nil_append] <;>
        exact ih (fun o ho => h o (List.mem_cons_of_mem _ ho))
  unfold artifactBlock
  split
  · rfl
  · simp only [ContentOp.linesList, ContentOp.lines,
      List.append_nil, contentOpens, List.filterMap_cons, Line.contentOpen, List.filterMap_append,
      List.filterMap_nil]
    rw [← contentOpens, hl fills.toList (fun o ho => hf o (Array.mem_toList_iff.mp ho))]

/-- **`mcids_partition_covers`** (the `_covers` statement): every painting
operator of a page is under exactly one wrapper (`wrapped_covers`), and the
identifiers its content wrappers carry are `0 … n−1` in stream order —
the two fill blocks around the numbered middle carry none. -/
public theorem mcids_partition_covers (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (page : PageOut) :
    (∀ o ∈ contentOps geom remap widths imgMap tags ix page, o.wrapped = true)
    ∧ (pageMarks (contentOps geom remap widths imgMap tags ix page)).toList.map Prod.fst
        = List.range (pageMarks (contentOps geom remap widths imgMap tags ix page)).size := by
  refine ⟨wrapped_covers geom remap widths imgMap tags ix page, ?_⟩
  unfold contentOps
  have hA := fillBlock_contentOpens none (page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h)
    (fun o ho => by
      simp only [Array.mem_map] at ho
      obtain ⟨f, _, rfl⟩ := ho
      exact Or.inl ⟨_, _, _, _, _, rfl⟩)
  have hC := fillBlock_contentOpens (some .layout)
    (((page.lines.foldl (stepLine geom remap imgMap tags) { widths }).rules.map
      fun (c, x, y, w, h) => ContentOp.fill c x y w h) ++
      (page.lines.foldl (stepLine geom remap imgMap tags) { widths }).polys.map polyOp)
    (fun o ho => by
      simp only [Array.mem_append, Array.mem_map] at ho
      rcases ho with ⟨t, _, rfl⟩ | ⟨p, _, rfl⟩
      · exact Or.inl ⟨_, _, _, _, _, rfl⟩
      · exact Or.inr ⟨_, _, _, _, rfl⟩)
  have hmid : ∀ (a m c : Array ContentOp),
      contentOpens (ContentOp.linesList a.toList) = [] →
      contentOpens (ContentOp.linesList c.toList) = [] →
      pageMarks ((a ++ m) ++ c) = pageMarks m := by
    intro a m c ha hc
    rw [pageMarks_eq_contentOpens, pageMarks_eq_contentOpens]
    unfold lines
    rw [Array.toList_append, Array.toList_append, ContentOp.linesList_append,
      ContentOp.linesList_append, contentOpens_append, contentOpens_append, ha, hc]
    simp
  rw [hmid _ _ _ hA hC]
  exact numberMarks_mcids_exact _

/-! ### Furniture -/

/-- The pagination artifacts at the top of a text object. -/
public def textArtifacts (ops : Array TextOp) : Nat :=
  (TextOp.linesList ops.toList).countP Line.isPaginationOpen

private theorem stripMarks_countP_pagination (ls : List Line) :
    (stripMarks ls).countP Line.isPaginationOpen = 0 := by
  rw [List.countP_eq_zero]
  intro l hl
  simp only [stripMarks, List.mem_filter, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hl
  cases l with
  | op s => simp [Line.isPaginationOpen]
  | emc => simp [Line.isPaginationOpen]
  | «open» t => simp [Line.isOpen] at hl

private theorem lineSt_textArtifacts (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (og : Origin) (st : TextSt) (l : LineOut) :
    textArtifacts (lineSt geom remap imgMap og st l).ops = 0 := by
  have h := lineSt_plainOps geom remap imgMap og st l
  unfold textArtifacts
  rw [← h, inkText, List.toList_toArray, TextOp.linesList_ink, stripMarks_countP_pagination]

/-- A line is furniture exactly when its origin says so. -/
public theorem Origin.of_furniture_iff (tags : Array (Option String)) (l : LineOut) :
    Origin.of tags l = .furniture ↔ l.furniture = true := by
  unfold Origin.of
  split
  · simp [*]
  · rename_i hf
    simp only [Bool.not_eq_true] at hf
    simp only [hf, Bool.false_eq_true, iff_false]
    split
    · split <;> simp
    · simp

private theorem stepLine_textArtifacts (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    textArtifacts (stepLine geom remap imgMap tags st l).ops
      = textArtifacts st.ops + (if l.furniture then 1 else 0) := by
  unfold textArtifacts
  have hpush : ∀ og t, (TextOp.linesList (st.ops.push (.marked t
      (lineSt geom remap imgMap og st l).ops)).toList).countP Line.isPaginationOpen
      = (TextOp.linesList st.ops.toList).countP Line.isPaginationOpen
        + (if (Line.open t).isPaginationOpen then 1 else 0) := by
    intro og t
    have h0 := lineSt_textArtifacts geom remap imgMap og st l
    unfold textArtifacts at h0
    rw [TextOp.linesList_push, List.countP_append, TextOp.lines, List.countP_cons,
      List.countP_append, h0]
    simp [Line.isPaginationOpen]
  simp only [stepLine]
  generalize hog : Origin.of tags l = og
  cases og with
  | furniture =>
    have hf := (Origin.of_furniture_iff tags l).mp hog
    dsimp only
    rw [hpush]
    simp [hf, furnitureTag, Line.isPaginationOpen]
  | unattributed =>
    have hf : l.furniture = false := by
      cases hfl : l.furniture with
      | false => rfl
      | true =>
        have := (Origin.of_furniture_iff tags l).mpr hfl
        rw [hog] at this
        cases this
    dsimp only
    split
    · simp [hf]
    · rw [hpush]
      simp [hf, Line.isPaginationOpen]
  | leaf k tag =>
    have hf : l.furniture = false := by
      cases hfl : l.furniture with
      | false => rfl
      | true =>
        have := (Origin.of_furniture_iff tags l).mpr hfl
        rw [hog] at this
        cases this
    dsimp only
    split
    · simp [hf]
    · rw [hpush]
      simp [hf, Line.isPaginationOpen]

/-- **Every furniture line is one pagination artifact, and no flow line
is any.** The text object `contentOps` ships carries exactly one
pagination wrapper per line the furniture pass laid — the count is the
census the artifact acceptance reads. -/
public theorem furniture_covers (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (lines : Array LineOut) :
    textArtifacts (lines.foldl (stepLine geom remap imgMap tags) {}).ops
      = (lines.filter (·.furniture)).size := by
  have h : ∀ (ls : List LineOut) (st : TextSt),
      textArtifacts (ls.foldl (stepLine geom remap imgMap tags) st).ops
        = textArtifacts st.ops + (ls.filter (·.furniture)).length := by
    intro ls
    induction ls with
    | nil => intro st; simp
    | cons l rest ih =>
      intro st
      simp only [List.foldl_cons, ih, stepLine_textArtifacts, List.filter_cons]
      split <;> simp <;> omega
  rw [← Array.foldl_toList, h, ← Array.length_toList, Array.toList_filter]
  simp [textArtifacts, TextOp.linesList]

end LeanTex.Core.Pdf
