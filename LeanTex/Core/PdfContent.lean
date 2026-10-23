module

public import LeanTex.Core.Dim
public import LeanTex.Core.Layout
public import LeanTex.Core.PdfOps
public import LeanTex.Core.GfxPdf
import LeanTex.Core.PdfText

/-! A page's content stream as typed operators: the layout walk that builds them and the pure
renderer that spells them. -/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Layout

private def pushGid (acc : String) (g : Nat) : String :=
  (((acc.push (Hex.spell true (g / 4096))).push (Hex.spell true (g / 256))).push
    (Hex.spell true (g / 16))).push (Hex.spell true g)

public def gidHex (g : Nat) : String := pushGid "" g

private theorem pushGid_eq (acc : String) (g : Nat) : pushGid acc g = acc ++ gidHex g := by
  simp only [pushGid, gidHex, String.push_eq_append, String.empty_append, String.append_assoc]

/-- The line that opens a marked sequence: the tag and its properties before `BDC`, or the tag
alone before `BMC` (§14.6.1). -/
public def MarkTag.opener : MarkTag → String
  | .artifact none => "/Artifact BMC"
  | .artifact (some .pagination) => "/Artifact << /Type /Pagination >> BDC"
  | .artifact (some .layout) => "/Artifact << /Type /Layout >> BDC"
  | .artifact (some .page) => "/Artifact << /Type /Page >> BDC"
  | .content s mcid _ => s!"/{s} << /MCID {mcid} >> BDC"
  | .span s =>
    "/Span << /ActualText " ++ String.ofList ((PdfRead.textStringBytes s).map Char.ofNat) ++ " >> BDC"

/-- What a line's ink stands for: running furniture, a structure leaf under its holder's type, or ink no leaf owns. -/
public inductive Origin where
  | furniture
  | unattributed
  | leaf (k : Nat) (tag : String)
  deriving Repr, BEq, Inhabited

/-- A line's origin, `tags` giving each leaf's holder type or `none`. -/
public def Origin.of (tags : Array (Option String)) (l : LineOut) : Origin :=
  if l.furniture then .furniture else
  match l.leaf with
  | some k =>
    match (tags[k]?).join with
    | some s => .leaf k s
    | none => .unattributed
  | none => .unattributed

/-- The tag an origin's operators sit under, its identifier a placeholder until `numberMarks`. -/
public def Origin.mark : Origin → MarkTag
  | .furniture => .artifact (some .pagination)
  | .unattributed => .artifact none
  | .leaf k tag => .content tag 0 k

public def PathOp.render : PathOp → String
  | .moveTo x y => s!"{x.toBpString} {y.toBpString} m "
  | .lineTo x y => s!"{x.toBpString} {y.toBpString} l "
  | .curveTo x1 y1 x2 y2 x3 y3 =>
    s!"{x1.toBpString} {y1.toBpString} {x2.toBpString} {y2.toBpString} \
{x3.toBpString} {y3.toBpString} c "
  | .close => "h "
  | .rect x y w h => s!"{x.toBpString} {y.toBpString} {w.toBpString} {h.toBpString} re "

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

/-- One text operator without its final line end; a marked sequence puts each operator on a line of
its own. -/
public def TextOp.render : TextOp → String
  | .scale p => s!"{p / 10}.{p % 10} Tz"
  | .move x y => s!"1 0 0 1 {x.toBpString} {y.toBpString} Tm"
  | .font res size => s!"/F{res + 1} {size.toBpString} Tf"
  | .color c => c.pdfFill
  | .show items => (items.foldl (fun acc it => acc ++ it.render) "[") ++ "] TJ"
  | .marked t body => TextOp.renderLines (t.opener ++ "\n") body.toList ++ "EMC"

private def TextOp.renderLines (acc : String) : List TextOp → String
  | [] => acc
  | o :: rest => TextOp.renderLines (acc ++ o.render ++ "\n") rest

end

private def pdfPaintFill : PdfPaint → String
  | .solid c => c.pdfFill
  | .pattern res _ => s!"/Pattern cs /P{res + 1} scn"

private def pdfPaintStroke : PdfPaint → String
  | .solid c => c.pdfStroke
  | .pattern res _ => s!"/Pattern CS /P{res + 1} SCN"

private def capCode : Gfx.Cap → Nat
  | .butt => 0
  | .round => 1
  | .square => 2

private def joinCode : Gfx.Join → Nat
  | .miter => 0
  | .round => 1
  | .bevel => 2

private def dashSpelling (d : Array Length) (p : Length) : String :=
  "[" ++ " ".intercalate (d.toList.map Length.toBpString) ++ "] " ++ p.toBpString ++ " d "

private def fillState : Option PaintFill → String
  | some f => pdfPaintFill f.paint ++ " "
  | none => ""

private def strokeState : Option PaintStroke → String
  | some st =>
    s!"{pdfPaintStroke st.paint} {st.width.toBpString} w " ++
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

private def paintOp : Option PaintFill → Option PaintStroke → String
  | some f, some _ => if f.evenOdd then "B*" else "B"
  | none, some _ => "S"
  | some f, none => if f.evenOdd then "f*" else "f"
  | none, none => "n"

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

private def xobjectName (res : Nat) : XKind → String
  | .raster _ => s!"/Ri{res + 1}"
  | .symbol => s!"/Fm{res + 1}"
  | .group => s!"/Fm{res + 1}"
  | .stamp _ _ _ => s!"/Fm{res + 1}"

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
    s!"q {c.pdfFill} {x.toBpString} {y.toBpString} {w.toBpString} {h.toBpString} re f Q"
  | .paint fl st gs segs =>
    let head := "q " ++ gsState gs ++ fillState fl ++ (strokeState st)
    let body := segs.foldl (fun acc seg => acc ++ seg.render) head
    body ++ paintOp fl st ++ " Q"
  | .text ops => (ops.foldl (fun acc op => acc ++ op.render ++ "\n") "BT\n") ++ "ET"
  | .image x y w h res =>
    s!"q {w.toBpString} 0 0 {h.toBpString} {x.toBpString} {y.toBpString} cm /Im{res + 1} Do Q"
  | .imageMissing x y w h =>
    -- A neutral grey hairline box marks where the figure would stand.
    s!"q 0.62 0.62 0.66 RG 0.75 w {x.toBpString} {y.toBpString} {w.toBpString} \
{h.toBpString} re S Q"
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

private def ContentOp.renderLines (acc : String) : List ContentOp → String
  | [] => acc
  | o :: rest => ContentOp.renderLines (acc ++ o.render ++ "\n") rest

end

private def renderStep : Option String → ContentOp → Option String
  | none, op => some op.render
  | some s, op => some (s ++ "\n" ++ op.render)

/-- The stream: operations one per line. -/
public def render (ops : Array ContentOp) : String := (ops.foldl renderStep none).getD ""

/-- An image the text walk gathered for painting after `ET`: its box, its XObject when it loaded,
and its line's origin. -/
public structure ImgOut where
  x : Length
  y : Length
  w : Length
  h : Length
  res : Option Nat
  origin : Origin
  /-- The store entry the image is, when it loaded one. -/
  store : Option Nat := none
  deriving Repr, BEq, Inhabited

private def widthμOf (upem units : Nat) : Int := ((units * 1000000 + upem / 2) / upem : Nat)

public def pdfWidthμ (font : Font) (g : Nat) : Int :=
  widthμOf font.unitsPerEm (font.widths[g]?.getD 0)

/-- The embedded faces' `/W` widths in millionths of the em, by layout face index; other faces have none. -/
public def widthTable (fonts : Array Font) (keep : Array Nat) : Array (Array Int) :=
  fonts.mapIdx fun k f => if keep.contains k then f.widths.map (widthμOf f.unitsPerEm) else #[]


/-- The viewer's pen in the open `TJ` array, as the writer computes it from what it wrote (§9.4.4). -/
public structure Pen where
  xm : Int
  y : Length
  adv : Int
  deriving Repr, BEq, Inhabited

/-- The text object's walk state; rules and images gather here and paint after `ET`. -/
public structure TextSt where
  ops : Array TextOp := #[]
  items : Array TextItem := #[]
  font : Int := -1
  size : Length := -Length.quantum
  color : Ir.Color := Ir.Color.black
  tz : Int := 0
  x : Length := 0
  pen : Option Pen := none
  widths : Array (Array Int) := #[]
  rules : Array (Ir.Color × Length × Length × Length × Length) := #[]
  /-- The marks the lines carried (`Ir.Decoration.isMark`), in page coordinates, painted under the
  text after the page's fills. -/
  marks : Array (Ir.Color × Length × Length × Length × Length) := #[]
  /-- The filled polygons the lines carried, in page coordinates. -/
  polys : Array (Ir.Color × Array (Length × Length)) := #[]
  images : Array ImgOut := #[]
  /-- The line's operators showing the hyphen the breaker set at its end. -/
  hyphens : Array Nat := #[]

private def TextSt.op (st : TextSt) (o : TextOp) : TextSt := { st with ops := st.ops.push o }

private def TextSt.closeTJ (st : TextSt) : TextSt :=
  if st.items.isEmpty then st else { st with ops := st.ops.push (.show st.items), items := #[] }

@[inline] private def roundDiv (neg : Bool) (num den : Nat) : Int :=
  if den == 0 then 0 else
    let q : Nat := (2 * num + den) / (2 * den)
    if neg then -(q : Int) else q

private def penTarget (sm tz xm : Int) (x : Length) : Int :=
  let den : Nat := bpUnits * sm.toNat * (1000 + tz).toNat
  let pos : Nat := (x * (1000 : Int)).units.toNat + bpUnits * (-xm).toNat
  let neg : Nat := bpUnits * xm.toNat + (-x * (1000 : Int)).units.toNat
  if neg ≤ pos then roundDiv false ((pos - neg) * 1000000000) den
  else roundDiv true ((neg - pos) * 1000000000) den

@[inline] private def runOffset (sm : Int) (P : Length) : Int :=
  roundDiv (P < 0) (P * (1000000000 : Int)).units.natAbs (bpUnits * sm.natAbs)

/-- The `TJ` number that brings a pen `d` millionths past its target to within half a thousandth. -/
@[inline] public def nudge (d : Int) : Int := (d + 500) / 1000

public theorem nudge_between (d : Int) :
    -500 ≤ d - 1000 * nudge d ∧ d - 1000 * nudge d ≤ 499 := by
  unfold nudge
  omega

private def TextSt.moveTo (st : TextSt) (runY : Length) : TextSt :=
  { st.closeTJ.op (.move st.x runY) with
    pen := some { xm := st.x.toBpMilli, y := runY, adv := 0 } }

private def TextSt.toPen (st : TextSt) (changes : Bool) (runY : Length) : TextSt :=
  match st.pen with
  | some p =>
    let n := nudge (p.adv - penTarget st.size.toBpMilli st.tz p.xm st.x)
    if !st.items.isEmpty && !changes && p.y == runY && n.natAbs ≤ 32000 then
      if n == 0 then st
      else { st with items := st.items.push (.adjust n),
                     pen := some { p with adv := p.adv - 1000 * n } }
    else st.moveTo runY
  | none => st.moveTo runY

private def TextSt.setFont (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Length) : TextSt :=
  if st.font != (idx : Int) || st.size != size then
    { st.op (.font (remap[idx]?.getD 0) size) with font := idx, size := size }
  else st

private def TextSt.setColor (st : TextSt) (color : Ir.Color) : TextSt :=
  if st.color != color then { st.op (.color color) with color := color } else st

private def TextSt.setFace (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Length)
    (color : Ir.Color) : TextSt :=
  ((st.closeTJ).setFont remap idx size).setColor color

/-- A run's string being placed: its glyph ids and numbers, the pen, and the laid-out advance reached. -/
public structure PlaceSt where
  gids : Array Nat
  nums : Array Int
  adv : Int
  P : Length

/-- One glyph of a run onto its string: the number that brings the pen to its layout position,
then the glyph. -/
@[inline] public def placeStep (wμ : Nat → Int) (tgt : Length → Int) (st : PlaceSt) :
    Nat × Char × Length → PlaceSt
  | (g, _, a) =>
    let n := nudge (st.adv - tgt st.P)
    ⟨st.gids.push g, st.nums.push n, st.adv - 1000 * n + wμ g, st.P + a⟩

/-- `placeStep`'s string as a list: each glyph with the number set before it. -/
public def placeSpec (wμ : Nat → Int) (tgt : Length → Int) :
    Int → Length → List (Nat × Char × Length) → List (Nat × Int)
  | _, _, [] => []
  | adv, P, (g, _, a) :: rest =>
    let n := nudge (adv - tgt P)
    (g, n) :: placeSpec wμ tgt (adv - 1000 * n + wμ g) (P + a) rest

/-- Where a viewer's pen stands as each glyph of a kerned string begins (§9.4.4). -/
public def penStarts (wμ : Nat → Int) : Int → List (Nat × Int) → List Int
  | _, [] => []
  | p, (g, n) :: rest => (p - 1000 * n) :: penStarts wμ (p - 1000 * n + wμ g) rest

/-- Each glyph's laid-out advance from the run's start. -/
public def glyphStarts : Length → List (Nat × Char × Length) → List Length
  | _, [] => []
  | P, (_, _, a) :: rest => P :: glyphStarts (P + a) rest

public theorem placeStep_fold_exact (wμ : Nat → Int) (tgt : Length → Int) (gs : List (Nat × Char × Length))
    (ga : Array Nat) (na : Array Int) (adv : Int) (P : Length) :
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

public theorem placeSpec_glyphs_id (wμ : Nat → Int) (tgt : Length → Int) (gs : List (Nat × Char × Length))
    (adv : Int) (P : Length) : (placeSpec wμ tgt adv P gs).map (·.1) = gs.map (·.1) := by
  induction gs generalizing adv P with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp [placeSpec, ih]

public theorem place_glyphs_id (wμ : Nat → Int) (tgt : Length → Int) (glyphs : Array (Nat × Char × Length))
    (adv : Int) : (glyphs.foldl (placeStep wμ tgt) ⟨#[], #[], adv, 0⟩).gids = glyphs.map (·.1) := by
  apply Array.toList_inj.mp
  rw [Array.toList_map, ← Array.foldl_toList, (placeStep_fold_exact ..).1]
  simpa using placeSpec_glyphs_id wμ tgt glyphs.toList adv 0

public theorem placeSpec_length_exact (wμ : Nat → Int) (tgt : Length → Int) (gs : List (Nat × Char × Length))
    (adv : Int) (P : Length) : (penStarts wμ adv (placeSpec wμ tgt adv P gs)).length = gs.length := by
  induction gs generalizing adv P with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp [placeSpec, penStarts, ih]

public theorem glyphStarts_length_exact (P : Length) (gs : List (Nat × Char × Length)) :
    (glyphStarts P gs).length = gs.length := by
  induction gs generalizing P with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨g, c, a⟩ := x
    simp [glyphStarts, ih]

public theorem place_between (wμ : Nat → Int) (tgt : Length → Int) (adv : Int) (P : Length)
    (gs : List (Nat × Char × Length)) :
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

private def runItem (gids : Array Nat) (nums : Array Int) : TextItem :=
  if nums.all (· == 0) then .glyphs gids else .kerned gids nums

private def TextSt.pushRun (st : TextSt) (item : TextItem) (w : Length) (pen : Pen) : TextSt :=
  { st with items := st.items.push item, x := st.x + w, pen := some pen }

private def stepRun (remap : Array Nat) (lineSize ypdf : Length) (st : TextSt) (idx : Nat)
    (color : Ir.Color) (w : Length) (glyphs : Array (Nat × Char × Length)) (segSize raise : Length) :
    TextSt :=
  if glyphs.isEmpty then { st with x := st.x + w } else
  let runY := ypdf + raise
  let size := if segSize == 0 then lineSize else segSize
  let changes := st.font != (idx : Int) || st.size != size || st.color != color
  let st := st.toPen changes runY
  let st := if changes then st.setFace remap idx size color else st
  let p := st.pen.getD { xm := st.x.toBpMilli, y := runY, adv := 0 }
  let sm := st.size.toBpMilli
  let t0 := penTarget sm st.tz p.xm st.x
  let wf := st.widths.getD idx #[]
  -- Reserved at full length, so the fold never regrows its arrays.
  let r := glyphs.foldl (placeStep (wf.getD · 0) (fun P => t0 + runOffset sm P))
    ⟨Array.mkEmpty glyphs.size, Array.mkEmpty glyphs.size, p.adv, 0⟩
  st.pushRun (runItem r.gids r.nums) w { p with adv := r.adv }

/-- Whether a run is the hyphen the breaker set at a line end. -/
@[expose] public def lineHyphen (attr : Attribution) (glyphs : Array (Nat × Char × Length)) : Bool :=
  attr == .hyphen && !glyphs.isEmpty

/-- A line-end hyphen's run as a `TJ` of its own, its operator's place noted. -/
private def stepHyphen (remap : Array Nat) (lineSize ypdf : Length) (st : TextSt) (idx : Nat)
    (color : Ir.Color) (w : Length) (glyphs : Array (Nat × Char × Length)) (segSize raise : Length) :
    TextSt :=
  let s := (stepRun remap lineSize ypdf st.closeTJ idx color w glyphs segSize raise).closeTJ
  { s with hyphens := s.hyphens.push (s.ops.size - 1) }

private def stepSeg (remap : Array Nat) (imgMap : Array (Option Nat)) (lineSize ypdf : Length)
    (og : Origin) (st : TextSt) : Seg → TextSt
  | .rule w thickness raise color _ =>
    { st with rules := st.rules.push (color, st.x, ypdf + raise, w, thickness), x := st.x + w }
  | .decoration kind w thickness raise color _ =>
    let r := (color, st.x, ypdf + raise, w, thickness)
    { st with rules := if kind.isMark then st.rules else st.rules.push r
              marks := if kind.isMark then st.marks.push r else st.marks, x := st.x + w }
  | .poly pts color =>
    { st with polys := st.polys.push (color, pts.map fun (px, py) => (st.x + px, ypdf + py)) }
  | .image idx w h _ raise _ =>
    { st with images := st.images.push { x := st.x, y := ypdf + raise, w, h,
                                         res := idx.bind fun k => imgMap[k]?.getD none,
                                         origin := og, store := idx },
              x := st.x + w }
  | .gap w _ | .decoratedGap w _ _ => { st with x := st.x + w }
  | .run idx color _ w glyphs segSize _ _ raise _ attr =>
    if lineHyphen attr glyphs then
      stepHyphen remap lineSize ypdf st idx color w glyphs segSize raise
    else stepRun remap lineSize ypdf st idx color w glyphs segSize raise

private def lineSt (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat)) (og : Origin)
    (st : TextSt) (l : LineOut) : TextSt :=
  let ypdf := geom.bleed + geom.pageH - l.y
  let st : TextSt := { st with ops := #[], hyphens := #[] }
  let st := if l.expand != st.tz then { st.op (.scale (1000 + l.expand)) with tz := l.expand }
    else st
  let st := { st with x := geom.bleed + l.x, pen := none }
  (l.segs.foldl (stepSeg remap imgMap l.size ypdf og) st).closeTJ

private def polyPath (pts : Array (Length × Length)) : Array PathOp :=
  match pts.toList with
  | [] => #[]
  | (x, y) :: rest =>
    (rest.foldl (fun acc (x, y) => acc.push (.lineTo x y)) #[.moveTo x y]).push .close

private def polyOp (p : Ir.Color × Array (Length × Length)) : ContentOp :=
  .paint (some { paint := .solid p.1, evenOdd := false }) none none (polyPath p.2)

private def furnitureTag : MarkTag := .artifact (some .pagination)

/-- The text a line-end hyphen reads as: a soft hyphen, a break no word holds. -/
@[expose] public def generatedHyphen : String := String.singleton (Char.ofNat 0xAD)

/-- A line's operators with each one showing a generated hyphen under a span reading as one. -/
@[expose] public def markHyphens (ops : Array TextOp) (hyphens : Array Nat) : Array TextOp :=
  if hyphens.isEmpty then ops
  else ops.mapIdx fun i o => if hyphens.contains i then .marked (.span generatedHyphen) #[o] else o

/-- One line onto the text object, under the wrapper its origin names, a generated hyphen under a
span; a line with no operators adds nothing unless it is furniture, which is wrapped whatever it
holds. -/
public def stepLine (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) : TextSt :=
  let og := Origin.of tags l
  let s := lineSt geom remap imgMap og st l
  let body := markHyphens s.ops s.hyphens
  match og with
  | .furniture => { s with ops := st.ops.push (.marked furnitureTag body) }
  | .unattributed =>
    { s with ops := if s.ops.isEmpty then st.ops else st.ops.push (.marked (.artifact none) body) }
  | .leaf k tag =>
    { s with ops := if s.ops.isEmpty then st.ops
                    else st.ops.push (.marked (.content tag 0 k) body) }

private def stepLinePlain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) : TextSt :=
  let s := lineSt geom remap imgMap (Origin.of tags l) st l
  { s with ops := st.ops ++ s.ops }

/-- The page's PDF space from layout coordinates: x from the medium's left
edge (the bleed), y up from its bottom. -/
@[expose] public def pageIso (geom : Geom) : Gfx.Iso :=
  { flipY := true, dx := geom.bleed, dy := geom.bleed + geom.pageH }

/-- A page line's picture label key, when the page may set it inside its picture. -/
public def _root_.LeanTex.Core.Layout.LineOut.labelKey? (l : LineOut) : Option (Nat × Nat) :=
  if l.furniture then none else l.pictureLabel.map (·.origin)

/-- The label keys a page's inks set among their ink, in paint order: each
ink's top-level labels, in node order. -/
public def inkLabelKeys (inks : Array InkOut) : List (Nat × Nat) :=
  inks.toList.flatMap fun k => k.fig.nodes.toList.flatMap fun n => n.label?.toList

/-- Whether a page sets its pictures' labels inside their pictures: top-level labels, no symbols,
and no key set twice. -/
public def routesLabels (inks : Array InkOut) : Bool :=
  inks.all (fun k => k.fig.labelsTop && k.fig.symbols.isEmpty) && decide (inkLabelKeys inks).Nodup

/-- Whether a page line paints inside its picture's sequence. -/
public def heldBy (route : Bool) (keys : List (Nat × Nat)) (l : LineOut) : Bool :=
  route && match l.labelKey? with
    | some k => keys.contains k
    | none => false

/-- A segment with its glyphs taken out: a run advances as it did and paints
nothing; every other segment stands. -/
public def _root_.LeanTex.Core.Layout.Seg.withoutGlyphs : Seg → Seg
  | .run idx color link w _ size m decs raise ground attr =>
    .run idx color link w #[] size m decs raise ground attr
  | .gap w word => .gap w word
  | .decoratedGap w word decs => .decoratedGap w word decs
  | .decoration kind w t raise color fl => .decoration kind w t raise color fl
  | .rule w t raise color fl => .rule w t raise color fl
  | .image store w h i r fl => .image store w h i r fl
  | .poly pts color => .poly pts color

/-- A line with its glyphs taken out, its rules, images and polygons kept. -/
public def _root_.LeanTex.Core.Layout.LineOut.withoutGlyphs (l : LineOut) : LineOut :=
  { l with segs := l.segs.map Layout.Seg.withoutGlyphs }

/-- The lines the text object walks: every page line, a held one without
its glyphs. -/
public def bodyLines (page : PageOut) : Array LineOut :=
  let held := heldBy (routesLabels page.inks) (inkLabelKeys page.inks)
  page.lines.map fun l => if held l then l.withoutGlyphs else l

/-- The text a label key's held lines set, as a text object in its own saved state, or nothing. -/
public def labelText (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (held : List LineOut)
    (k : Nat × Nat) : Option (Array TextOp) :=
  match held.filter (·.labelKey? == some k) with
  | [] => none
  | ls => some (ls.foldl (stepLinePlain geom remap imgMap tags) { widths }).ops

/-- The label setter of a page: the text of each key its held lines carry,
or nothing on a page that routes none. -/
public structure LabelSetter where
  text : (Nat × Nat) → Option (Array TextOp)

/-- A page's label setter, its held lines read once. -/
public def pageLabels (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (page : PageOut) :
    LabelSetter :=
  if routesLabels page.inks then
    ⟨labelText geom remap widths imgMap tags
      (page.lines.toList.filter (heldBy true (inkLabelKeys page.inks)))⟩
  else ⟨fun _ => none⟩

/-- A picture's ink as operators in the page's PDF space, each label set where its node stands. -/
@[expose] public def inkPaint (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tx : (Nat × Nat) → Option (Array TextOp)) (k : InkOut) : Array ContentOp :=
  GfxPdf.emit ix (fun _ key => (tx key).toArray.map GfxPdf.textGroup)
    ((pageIso geom).compose k.place) k.fig

private def artifact (kind : Option ArtifactKind) (o : ContentOp) : ContentOp :=
  .marked (.artifact kind) #[o]

private def artifactBlock (kind : Option ArtifactKind) (ops : Array ContentOp) : Array ContentOp :=
  if ops.isEmpty then #[] else #[.marked (.artifact kind) ops]

/-- A drawn figure as pages paint it: its body, spelled once as a shared form, and its box. -/
public structure FigForm where
  body : Array ContentOp
  box : Gfx.Box
  deriving Repr, BEq, Inhabited

/-- The exact matrix that sets a figure's box onto an image's rectangle `(x, y, w, h)`. -/
@[expose] public def figPlace (x y w h : Length) (box : Gfx.Box) : Gfx.Affine :=
  let bw := box.2.1 - box.1.1
  let bh := box.2.2 - box.1.2
  let sx : Rat := if bw == 0 then 1 else w.toRat / bw.toRat
  let sy : Rat := if bh == 0 then 1 else h.toRat / bh.toRat
  ⟨sx, 0, 0, sy, x.toRat - box.1.1.toRat * sx, y.toRat - box.1.2.toRat * sy⟩

/-- The figure an image places, when its store entry is a drawn figure. -/
@[expose] public def figOf (figs : Array (Option FigForm)) (i : ImgOut) : Option FigForm :=
  i.store.bind fun k => (figs[k]?).join

/-- A drawn figure on the page: its form under the matrix that sets its
box onto the image's rectangle. -/
@[expose] public def figOp (ix : GfxPdf.Request → Nat) (i : ImgOut) (f : FigForm) : ContentOp :=
  .xobject (some (figPlace i.x i.y i.w i.h f.box)) (ix (.form .symbol f.body)) .symbol f.body

private def imageOp (ix : GfxPdf.Request → Nat) (figs : Array (Option FigForm)) (i : ImgOut) :
    ContentOp :=
  match figOf figs i with
  | some f => .marked i.origin.mark #[figOp ix i f]
  | none =>
    match i.res with
    | some n => .marked i.origin.mark #[.image i.x i.y i.w i.h n]
    | none => artifact (some .layout) (.imageMissing i.x i.y i.w i.h)

private def imageOpPlain (ix : GfxPdf.Request → Nat) (figs : Array (Option FigForm)) (i : ImgOut) :
    ContentOp :=
  match figOf figs i with
  | some f => figOp ix i f
  | none =>
    match i.res with
    | some n => .image i.x i.y i.w i.h n
    | none => .imageMissing i.x i.y i.w i.h

/-- One face's stretch of a shaped run as text operators, each glyph placed by the viewer's arithmetic. -/
public def figureStretchOps (remap : Array Nat) (widths : Array (Array Int)) (color : Ir.Color)
    (size : Length) (face : Nat) (glyphs : Array (Nat × Char × Length)) (x0 : Length) : Array TextOp :=
  let sm := size.toBpMilli
  let wf := widths.getD face #[]
  let r := glyphs.foldl (placeStep (wf.getD · 0) (fun P => runOffset sm P))
    ⟨Array.mkEmpty glyphs.size, Array.mkEmpty glyphs.size, 0, 0⟩
  #[.font (remap[face]?.getD 0) size, .color color, .move x0 0, .show #[runItem r.gids r.nums]]

/-- A shaped run's glyphs split into one-face stretches, each with its start. -/
public def figureStretches (glyphs : Array (Nat × Nat × Char × Length)) :
    Array (Nat × Array (Nat × Char × Length) × Length) := Id.run do
  let mut out : Array (Nat × Array (Nat × Char × Length) × Length) := #[]
  let mut cur : Option (Nat × Array (Nat × Char × Length) × Length) := none
  for h : k in [0:glyphs.size] do
    let (f, g, c, x) := glyphs[k]
    let next : Length := match glyphs[k + 1]? with
      | some (_, _, _, nx) => nx - x
      | none => 0
    match cur with
    | some (cf, gs, x0) =>
      if cf == f then cur := some (cf, gs.push (g, c, next), x0)
      else
        out := out.push (cf, gs, x0)
        cur := some (f, #[(g, c, next)], x)
    | none => cur := some (f, #[(g, c, next)], x)
  match cur with
  | some c => return out.push c
  | none => return out

/-- A shaped run of an imported figure as one text object under the run's frame; a run with no
solid fill paints nothing. -/
public def shapedOps (remap : Array Nat) (widths : Array (Array Int)) (ix : GfxPdf.Request → Nat)
    (fr : GfxPdf.Frame) (s : Gfx.Shaped) : Array ContentOp :=
  match s.fill with
  | some { paint := .solid c, alpha, .. } =>
    let tops := (figureStretches s.glyphs).flatMap fun (face, gs, x0) =>
      figureStretchOps remap widths c s.size face gs x0
    let gs : Option ExtG := if alpha = Gfx.Alpha.opaque then none
      else some { res := ix (.extG alpha Gfx.Alpha.opaque), fill := alpha, stroke := Gfx.Alpha.opaque }
    if tops.isEmpty then #[] else #[.group (some (fr.lift s.xf)) gs #[] #[.text tops]]
  | _ => #[]

/-- An imported figure as its form's body: the box as an unpainted path, then the figure's
operators, clipped when it clips. -/
public def figureBody (remap : Array Nat) (widths : Array (Array Int)) (ix : GfxPdf.Request → Nat)
    (fig : Gfx.Figure Gfx.Shaped) : Array ContentOp :=
  let ((x0, y0), (x1, y1)) := fig.box
  let boxPath : Array PathOp := #[.rect x0 y0 (x1 - x0) (y1 - y0)]
  let ops := GfxPdf.emit ix (shapedOps remap widths ix) { flipY := false, dx := 0, dy := 0 } fig
  let painted := if fig.clipToBox then #[ContentOp.group none none #[(boxPath, .nonzero)] ops] else ops
  #[ContentOp.paint none none none boxPath] ++ painted

private def groupTag (tags : Array (Option String)) : Option Nat → MarkTag
  | some k =>
    match (tags[k]?).join with
    | some s => .content s 0 k
    | none => .artifact none
  | none => .artifact none

private def flushGroup (tags : Array (Option String)) (out : Array ContentOp) :
    Option (Option Nat × Array ContentOp) → Array ContentOp
  | none => out
  | some (lf, ops) => out.push (.marked (groupTag tags lf) ops)

private def inkGroupsList (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tx : (Nat × Nat) → Option (Array TextOp)) (tags : Array (Option String))
    (out : Array ContentOp) (cur : Option (Option Nat × Array ContentOp)) :
    List InkOut → Array ContentOp
  | [] => flushGroup tags out cur
  | k :: rest =>
    let ops := inkPaint geom ix tx k
    if ops.isEmpty then inkGroupsList geom ix tx tags out cur rest
    else match cur with
      | some (lf, acc) =>
        if lf == k.leaf then inkGroupsList geom ix tx tags out (some (lf, acc ++ ops)) rest
        else inkGroupsList geom ix tx tags (flushGroup tags out cur) (some (k.leaf, ops)) rest
      | none => inkGroupsList geom ix tx tags out (some (k.leaf, ops)) rest

private def inkGroups (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tx : (Nat × Nat) → Option (Array TextOp)) (tags : Array (Option String))
    (inks : Array InkOut) : Array ContentOp :=
  inkGroupsList geom ix tx tags #[] none inks.toList

mutual

private def TextOp.number (n : Nat) : TextOp → TextOp × Nat
  | o@(.scale _) => (o, n)
  | o@(.move _ _) => (o, n)
  | o@(.font _ _) => (o, n)
  | o@(.color _) => (o, n)
  | o@(.show _) => (o, n)
  | .marked (.artifact a) body =>
    let r := TextOp.numberList n #[] body.toList
    (.marked (.artifact a) r.1, r.2)
  | .marked (.span a) body =>
    let r := TextOp.numberList n #[] body.toList
    (.marked (.span a) r.1, r.2)
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
  | .marked (.span a) body =>
    let r := ContentOp.numberList n #[] body.toList
    (.marked (.span a) r.1, r.2)
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

/-- One page's operations: fills, the lines' marks, picture paths with their labels, the text
object, images, then rules, each painting operator under one wrapper. -/
public def contentOps (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (figs : Array (Option FigForm)) (page : PageOut) : Array ContentOp :=
  let fills := page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h
  let paths := inkGroups geom ix (pageLabels geom remap widths imgMap tags page).text tags page.inks
  let st := (bodyLines page).foldl (stepLine geom remap imgMap tags) { widths }
  let images := st.images.map (imageOp ix figs)
  let rules := st.rules.map fun (c, x, y, w, h) => ContentOp.fill c x y w h
  let marks := st.marks.map fun (c, x, y, w, h) => ContentOp.fill c x y w h
  let front := page.front.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h
  let middle := numberMarks ((paths.push (.text st.ops)) ++ images)
  ((artifactBlock none fills ++ artifactBlock (some .layout) marks) ++ middle) ++
    artifactBlock (some .layout) ((rules ++ st.polys.map polyOp) ++ front)

/-- `contentOps` with no marked content. -/
public def contentOpsPlain (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (figs : Array (Option FigForm)) (page : PageOut) : Array ContentOp :=
  let fills := page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h
  let paths :=
    page.inks.flatMap (inkPaint geom ix (pageLabels geom remap widths imgMap tags page).text)
  let st := (bodyLines page).foldl (stepLinePlain geom remap imgMap tags) { widths }
  let images := st.images.map (imageOpPlain ix figs)
  let rules := st.rules.map fun (c, x, y, w, h) => ContentOp.fill c x y w h
  let marks := st.marks.map fun (c, x, y, w, h) => ContentOp.fill c x y w h
  let front := page.front.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h
  let body := ((fills ++ marks) ++ paths).push (.text st.ops)
  (body ++ images) ++ ((rules ++ st.polys.map polyOp) ++ front)

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

/-- The glyph census of a text-operator sequence. -/
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

mutual

/-- The glyph runs a text operator shows under a span reading as a generated hyphen. -/
public def TextOp.spanRuns : TextOp → List (Array Nat)
  | .scale _ => []
  | .move _ _ => []
  | .font _ _ => []
  | .color _ => []
  | .show _ => []
  | .marked (.span a) body =>
    if a = generatedHyphen then TextOp.runsList body.toList else TextOp.spanRunsList body.toList
  | .marked (.artifact _) body => TextOp.spanRunsList body.toList
  | .marked (.content _ _ _) body => TextOp.spanRunsList body.toList

public def TextOp.spanRunsList : List TextOp → List (Array Nat)
  | [] => []
  | o :: rest =>
    let tail := TextOp.spanRunsList rest
    o.spanRuns ++ tail

end

mutual

/-- The glyph runs a page stream's operator shows under a generated-hyphen span; a form's content is
its own stream. -/
public def ContentOp.spanRuns : ContentOp → List (Array Nat)
  | .fill _ _ _ _ _ => []
  | .paint _ _ _ _ => []
  | .shade _ _ => []
  | .outline _ _ _ => []
  | .group _ _ _ body => ContentOp.spanRunsList body.toList
  | .xobject _ _ _ _ => []
  | .text ops => TextOp.spanRunsList ops.toList
  | .image _ _ _ _ _ => []
  | .imageMissing _ _ _ _ => []
  | .marked _ body => ContentOp.spanRunsList body.toList

public def ContentOp.spanRunsList : List ContentOp → List (Array Nat)
  | [] => []
  | o :: rest =>
    let tail := ContentOp.spanRunsList rest
    o.spanRuns ++ tail

end

/-- Every glyph run a page stream shows as a generated hyphen, in stream order. -/
public def spanRunsOf (ops : Array ContentOp) : List (Array Nat) :=
  ops.toList.flatMap ContentOp.spanRuns

/-- The glyph run a segment ships as the hyphen the breaker set at a line end. -/
public def segHyphenRuns : Seg → List (Array Nat)
  | .run _ _ _ _ glyphs _ _ _ _ _ attr =>
    if lineHyphen attr glyphs then [glyphs.map (·.1)] else []
  | .gap _ _ | .decoratedGap _ _ _ => []
  | .rule _ _ _ _ _ | .decoration _ _ _ _ _ _ => []
  | .image _ _ _ _ _ _ => []
  | .poly _ _ => []

/-- One line of a content stream as the renderer lays it: an operator, a sequence opener, or an `EMC`. -/
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

/-- Lines joined by their separators, the stream `render` spells. -/
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

private def termLines : List Line → String
  | [] => ""
  | l :: rest =>
    let tail := termLines rest
    l.render ++ "\n" ++ tail

mutual

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

/-- A decoration leaf: a fill or a placeholder box. -/
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

/-- The glyph run a segment ships: a run's glyph ids, none for a kern. -/
public def segRuns : Seg → List (Array Nat)
  | .run _ _ _ _ glyphs _ _ _ _ _ _ => if glyphs.isEmpty then [] else [glyphs.map (·.1)]
  | .gap _ _ | .decoratedGap _ _ _ => []
  | .rule _ _ _ _ _ | .decoration _ _ _ _ _ _ => []
  | .image _ _ _ _ _ _ => []
  | .poly _ _ => []

/-- The shipped glyph census of a page: every run's glyphs, line by line in segment order. -/
public def pageRuns (page : PageOut) : List (Array Nat) :=
  page.lines.toList.flatMap fun l => l.segs.toList.flatMap segRuns

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

mutual

/-- An operator a figure paints with: a path, a shading, a saved state or an XObject over figure
operators, carrying no glyph run and no marked content. -/
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

private theorem emitOne_figureOnly {L : Type} (ix : GfxPdf.Request → Nat)
    (labelOps : GfxPdf.Frame → L → Array ContentOp)
    (hl : ∀ fr l, ∀ o ∈ labelOps fr l, o.figureOnly = true)
    (outlines : Array (Array Gfx.Subpath)) (bodyOps : Array (Array ContentOp))
    (hb : ∀ b ∈ bodyOps, ∀ o ∈ b, o.figureOnly = true) :
    ∀ (n : Gfx.Node L) (fr : GfxPdf.Frame) (acc : Array ContentOp),
      (∀ o ∈ acc, o.figureOnly = true) →
      ∀ o ∈ GfxPdf.emitOne ix labelOps outlines bodyOps fr acc n,
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
    · exact emitList_figureOnly ix labelOps hl outlines bodyOps hb kids.toList fr acc ha o ho
    · split at ho
      · simp only [Array.mem_push] at ho
        rcases ho with ho | rfl
        · exact ha o ho
        · exact figureOnly_of_mem _ (emitList_figureOnly ix labelOps hl outlines bodyOps hb
            kids.toList _ #[] (by simp))
      · simp only [Array.mem_push] at ho
        rcases ho with ho | rfl
        · exact ha o ho
        · simp only [ContentOp.figureOnly, ContentOp.figureOnlyList, Bool.and_true]
          exact figureOnly_of_mem _ (emitList_figureOnly ix labelOps hl outlines bodyOps hb
            kids.toList _ #[] (by simp))
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
  | .label l, fr, acc, ha => by
    intro o ho
    simp only [GfxPdf.emitOne, Array.mem_append] at ho
    rcases ho with ho | ho
    · exact ha o ho
    · exact hl fr l o ho
  | .words _, fr, acc, ha => by
    intro o ho
    simp only [GfxPdf.emitOne] at ho
    exact ha o ho

private theorem emitList_figureOnly {L : Type} (ix : GfxPdf.Request → Nat)
    (labelOps : GfxPdf.Frame → L → Array ContentOp)
    (hl : ∀ fr l, ∀ o ∈ labelOps fr l, o.figureOnly = true)
    (outlines : Array (Array Gfx.Subpath)) (bodyOps : Array (Array ContentOp))
    (hb : ∀ b ∈ bodyOps, ∀ o ∈ b, o.figureOnly = true) :
    ∀ (xs : List (Gfx.Node L)) (fr : GfxPdf.Frame) (acc : Array ContentOp),
      (∀ o ∈ acc, o.figureOnly = true) →
      ∀ o ∈ GfxPdf.emitList ix labelOps outlines bodyOps fr acc xs,
        o.figureOnly = true
  | [], _, _, ha => ha
  | n :: rest, fr, acc, ha => by
    simp only [GfxPdf.emitList]
    exact emitList_figureOnly ix labelOps hl outlines bodyOps hb rest fr _
      (emitOne_figureOnly ix labelOps hl outlines bodyOps hb n fr acc ha)

end

private theorem emit_figureOnly {L : Type} (ix : GfxPdf.Request → Nat)
    (labelOps : GfxPdf.Frame → L → Array ContentOp)
    (hl : ∀ fr l, ∀ o ∈ labelOps fr l, o.figureOnly = true) (place : Gfx.Iso) (fig : Gfx.Figure L) :
    ∀ o ∈ GfxPdf.emit ix labelOps place fig, o.figureOnly = true := by
  unfold GfxPdf.emit
  refine emitList_figureOnly ix labelOps hl _ _ ?_ _ _ #[] (by simp)
  intro b hb o ho
  unfold GfxPdf.bodyOpsOf at hb
  simp only [Array.mem_map] at hb
  obtain ⟨body, _, rfl⟩ := hb
  exact emitList_figureOnly ix labelOps hl _ #[] (by simp) _ _ #[] (by simp) o ho

mutual

private theorem emitOne_labelOps_irrel {L : Type} (ix : GfxPdf.Request → Nat)
    (lo₁ lo₂ : GfxPdf.Frame → L → Array ContentOp) (outlines : Array (Array Gfx.Subpath))
    (bodyOps : Array (Array ContentOp)) :
    ∀ (n : Gfx.Node L) (fr : GfxPdf.Frame) (acc : Array ContentOp), n.labelFree = true →
      GfxPdf.emitOne ix lo₁ outlines bodyOps fr acc n =
        GfxPdf.emitOne ix lo₂ outlines bodyOps fr acc n
  | .draw .., _, _, _ => rfl
  | .group xf clips alpha kids, fr, acc, hf => by
    simp only [Gfx.Node.labelFree] at hf
    have ih := fun fr' acc' =>
      emitList_labelOps_irrel ix lo₁ lo₂ outlines bodyOps kids.toList fr' acc' hf
    simp only [GfxPdf.emitOne, ih]
  | .use .., _, _, _ => rfl
  | .stamp .., _, _, _ => rfl
  | .image .., _, _, _ => rfl
  | .label _, _, _, hf => by simp [Gfx.Node.labelFree] at hf
  | .words _, _, _, _ => rfl

private theorem emitList_labelOps_irrel {L : Type} (ix : GfxPdf.Request → Nat)
    (lo₁ lo₂ : GfxPdf.Frame → L → Array ContentOp) (outlines : Array (Array Gfx.Subpath))
    (bodyOps : Array (Array ContentOp)) :
    ∀ (xs : List (Gfx.Node L)) (fr : GfxPdf.Frame) (acc : Array ContentOp),
      Gfx.Node.labelFreeList xs = true →
      GfxPdf.emitList ix lo₁ outlines bodyOps fr acc xs =
        GfxPdf.emitList ix lo₂ outlines bodyOps fr acc xs
  | [], _, _, _ => rfl
  | n :: rest, fr, acc, hf => by
    simp only [Gfx.Node.labelFreeList, Bool.and_eq_true] at hf
    simp only [GfxPdf.emitList]
    rw [emitOne_labelOps_irrel ix lo₁ lo₂ outlines bodyOps n fr acc hf.1]
    exact emitList_labelOps_irrel ix lo₁ lo₂ outlines bodyOps rest fr _ hf.2

end

private def PicOp (o : ContentOp) : Prop :=
  o.figureOnly = true ∨ ∃ t, o = GfxPdf.textGroup t ∧ inkText t = t

private def InkSetter (tx : (Nat × Nat) → Option (Array TextOp)) (k : InkOut) : Prop :=
  (∀ key, tx key = none) ∨
    ((k.fig.labelsTop = true ∧ k.fig.symbols = #[]) ∧ ∀ key t, tx key = some t → inkText t = t)

private theorem inkPaint_picOps (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tx : (Nat × Nat) → Option (Array TextOp)) (k : InkOut) (h : InkSetter tx k) :
    ∀ o ∈ inkPaint geom ix tx k, PicOp o := by
  rcases h with hnone | ⟨⟨htop, hsym⟩, ht⟩
  · have hlo : (fun (_ : GfxPdf.Frame) (key : Nat × Nat) => (tx key).toArray.map GfxPdf.textGroup)
        = fun _ _ => #[] := by
      funext _ key
      simp [hnone key]
    intro o ho
    unfold inkPaint at ho
    rw [hlo] at ho
    exact Or.inl (emit_figureOnly ix (fun _ _ => #[]) (by simp) _ k.fig o ho)
  · intro o ho
    unfold inkPaint GfxPdf.emit at ho
    rw [GfxPdf.emitList_flatMap] at ho
    have hb : GfxPdf.bodyOpsOf ix (fun _ key => (tx key).toArray.map GfxPdf.textGroup) k.fig = #[] := by
      simp [GfxPdf.bodyOpsOf, Gfx.Figure.bodies, hsym]
    rw [hb] at ho
    simp only [List.mem_toArray, List.mem_flatMap, Array.mem_toList_iff] at ho
    obtain ⟨n, hn, ho⟩ := ho
    have hnt : n.topOk = true := by
      simp only [Gfx.Figure.labelsTop, Bool.and_eq_true, Array.all_eq_true'] at htop
      exact htop.1 n hn
    by_cases hlab : ∃ l, n = .label l
    · obtain ⟨key, rfl⟩ := hlab
      simp only [GfxPdf.emitOne, Array.empty_append] at ho
      cases htx : tx key with
      | none => simp [htx] at ho
      | some t =>
        simp only [htx, Option.toArray_some, List.map_toArray, List.map_cons, List.map_nil,
          List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ho
        exact Or.inr ⟨t, ho, ht key t htx⟩
    · have hf := Gfx.Node.labelFree_of_topOk n hnt fun l he => hlab ⟨l, he⟩
      rw [emitOne_labelOps_irrel ix _ (fun _ _ => #[]) _ _ n _ #[] hf] at ho
      exact Or.inl (emitOne_figureOnly ix (fun _ _ => #[]) (by simp) _ #[] (by simp) n _ #[]
        (by simp) o ho)

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

private theorem moveTo_runs (st : TextSt) (y : Length) : (st.moveTo y).runs = st.runs := by
  have h := op_runs st.closeTJ (.move st.x y) rfl
  rw [closeTJ_runs] at h
  exact h

private theorem toPen_runs (st : TextSt) (c : Bool) (y : Length) : (st.toPen c y).runs = st.runs := by
  unfold TextSt.toPen
  split
  · simp only []
    split
    · split
      · rfl
      · simp [TextSt.runs, TextItem.runs]
    · exact moveTo_runs st y
  · exact moveTo_runs st y

private theorem setFont_runs (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Length) :
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

private theorem setFace_runs (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Length) (c : Ir.Color) :
    (st.setFace remap idx size c).runs = st.runs := by
  unfold TextSt.setFace
  rw [setColor_runs, setFont_runs, closeTJ_runs]

private theorem runItem_runs (gids : Array Nat) (nums : Array Int) : (runItem gids nums).runs = [gids] := by
  unfold runItem
  split <;> rfl

private theorem pushRun_runs (st : TextSt) (i : TextItem) (w : Length) (p : Pen) :
    (st.pushRun i w p).runs = st.runs ++ i.runs := by
  simp [TextSt.pushRun, TextSt.runs]

private theorem stepRun_runs (remap : Array Nat) (ls y : Length) (st : TextSt) (idx : Nat) (c : Ir.Color)
    (w : Length) (glyphs : Array (Nat × Char × Length)) (ss raise : Length) :
    (stepRun remap ls y st idx c w glyphs ss raise).runs
      = st.runs ++ (if glyphs.isEmpty then [] else [glyphs.map (·.1)]) := by
  unfold stepRun
  split
  · simp [TextSt.runs]
  · simp only [pushRun_runs, runItem_runs, Array.mkEmpty_eq, place_glyphs_id]
    congr 1
    simp only [apply_ite TextSt.runs, setFace_runs, toPen_runs, ite_self]

private theorem stepHyphen_runs (remap : Array Nat) (ls y : Length) (st : TextSt) (idx : Nat)
    (c : Ir.Color) (w : Length) (glyphs : Array (Nat × Char × Length)) (ss raise : Length) :
    (stepHyphen remap ls y st idx c w glyphs ss raise).runs
      = st.runs ++ (if glyphs.isEmpty then [] else [glyphs.map (·.1)]) := by
  have h1 := closeTJ_runs (stepRun remap ls y st.closeTJ idx c w glyphs ss raise)
  have h2 := stepRun_runs remap ls y st.closeTJ idx c w glyphs ss raise
  have h3 := closeTJ_runs st
  have e : (stepHyphen remap ls y st idx c w glyphs ss raise).runs =
      (stepRun remap ls y st.closeTJ idx c w glyphs ss raise).closeTJ.runs := rfl
  rw [e, h1, h2, h3]

private theorem stepSeg_runs (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Length) (og : Origin)
    (st : TextSt) (seg : Seg) : (stepSeg remap imgMap ls y og st seg).runs = st.runs ++ segRuns seg := by
  cases seg with
  | rule | decoration => simp [stepSeg, TextSt.runs, segRuns]
  | image => simp [stepSeg, TextSt.runs, segRuns]
  | gap | decoratedGap => simp [stepSeg, TextSt.runs, segRuns]
  | poly => simp [stepSeg, TextSt.runs, segRuns]
  | run =>
    simp only [stepSeg]
    split
    · exact stepHyphen_runs ..
    · exact stepRun_runs ..

private theorem foldl_segs_runs (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Length)
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

private theorem flatMap_mapIdx_same {β : Type} (g : TextOp → List β) :
    ∀ (l : List TextOp) (F : Nat → TextOp → TextOp), (∀ i o, g (F i o) = g o) →
      (l.mapIdx F).flatMap g = l.flatMap g
  | [], _, _ => rfl
  | o :: rest, F, hF => by
    rw [List.mapIdx_cons, List.flatMap_cons, List.flatMap_cons, hF,
      flatMap_mapIdx_same g rest (fun i => F (i + 1)) (fun i => hF (i + 1))]

private theorem mapIdx_id_of {α : Type} : ∀ (l : List α) (f : Nat → α → α), (∀ i o, f i o = o) →
    l.mapIdx f = l
  | [], _, _ => rfl
  | o :: rest, f, hf => by
    rw [List.mapIdx_cons, hf, mapIdx_id_of rest (fun i => f (i + 1)) (fun i => hf (i + 1))]

private theorem markHyphens_eq (ops : Array TextOp) (hs : Array Nat) :
    markHyphens ops hs =
      ops.mapIdx fun i o => if hs.contains i then .marked (.span generatedHyphen) #[o] else o := by
  unfold markHyphens
  split
  · next h =>
    apply Array.toList_inj.mp
    rw [Array.toList_mapIdx, mapIdx_id_of]
    intro i o
    have : hs = #[] := Array.isEmpty_iff.mp h
    simp [this]
  · rfl

private theorem markHyphens_flatMap {β : Type} (g : TextOp → List β)
    (hg : ∀ o, g (.marked (.span generatedHyphen) #[o]) = g o) (ops : Array TextOp) (hs : Array Nat) :
    (markHyphens ops hs).toList.flatMap g = ops.toList.flatMap g := by
  rw [markHyphens_eq, Array.toList_mapIdx]
  apply flatMap_mapIdx_same g
  intro i o
  split
  · exact hg o
  · rfl

private theorem markHyphens_runs (ops : Array TextOp) (hs : Array Nat) :
    (markHyphens ops hs).toList.flatMap TextOp.runs = ops.toList.flatMap TextOp.runs :=
  markHyphens_flatMap TextOp.runs (fun o => by simp [TextOp.runs, TextOp.runsList]) ops hs

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
  · simp [Array.toList_push, List.flatMap_append, TextOp.runs, TextOp.runsList_eq, markHyphens_runs, hs,
      List.append_assoc]
  · split
    · rename_i he
      simp [(hempty he).1, (hempty he).2]
    · simp [Array.toList_push, List.flatMap_append, TextOp.runs, TextOp.runsList_eq, markHyphens_runs, hs,
        List.append_assoc]
  · split
    · rename_i he
      simp [(hempty he).1, (hempty he).2]
    · simp [Array.toList_push, List.flatMap_append, TextOp.runs, TextOp.runsList_eq, markHyphens_runs, hs,
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
  | cons l _ ih => exact ih _ (stepLine_items ..)

/-- The store index an image segment places, as a one-entry list. -/
public def segStores : Seg → List (Option Nat)
  | .image idx _ _ _ _ _ => [idx]
  | .run .. | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .poly .. => []

/-- Every image a page's lines place, by store index, in order. -/
public def pageStores (page : PageOut) : List (Option Nat) :=
  page.lines.toList.flatMap fun l => l.segs.toList.flatMap segStores

private def TextSt.stores (st : TextSt) : List (Option Nat) := st.images.toList.map (·.store)

private theorem closeTJ_images (st : TextSt) : st.closeTJ.images = st.images := by
  unfold TextSt.closeTJ
  split <;> rfl

private theorem moveTo_images (st : TextSt) (y : Length) : (st.moveTo y).images = st.images := by
  simp [TextSt.moveTo, TextSt.op, closeTJ_images]

private theorem toPen_images (st : TextSt) (changes : Bool) (y : Length) :
    (st.toPen changes y).images = st.images := by
  unfold TextSt.toPen
  split
  · dsimp only
    split
    · split <;> rfl
    · exact moveTo_images _ _
  · exact moveTo_images _ _

private theorem setFace_images (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Length)
    (c : Ir.Color) : (st.setFace remap idx size c).images = st.images := by
  unfold TextSt.setFace TextSt.setColor TextSt.setFont
  split <;> split <;> simp [TextSt.op, closeTJ_images]

private theorem stepRun_images (remap : Array Nat) (ls y : Length) (st : TextSt) (idx : Nat) (c : Ir.Color)
    (w : Length) (glyphs : Array (Nat × Char × Length)) (ss raise : Length) :
    (stepRun remap ls y st idx c w glyphs ss raise).images = st.images := by
  unfold stepRun
  split
  · rfl
  · dsimp only
    simp only [TextSt.pushRun, apply_ite TextSt.images, setFace_images, toPen_images, ite_self]

private theorem stepSeg_stores (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Length)
    (og : Origin) (st : TextSt) (seg : Seg) :
    (stepSeg remap imgMap ls y og st seg).stores = st.stores ++ segStores seg := by
  cases seg with
  | image idx w h _ _ => simp [stepSeg, TextSt.stores, segStores]
  | run =>
    simp only [stepSeg]
    split
    · simp [stepHyphen, TextSt.stores, segStores, stepRun_images, closeTJ_images]
    · simp [TextSt.stores, segStores, stepRun_images]
  | rule | decoration | gap | decoratedGap | poly => simp [stepSeg, TextSt.stores, segStores]

private theorem foldl_segs_stores (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Length)
    (og : Origin) (segs : List Seg) (st : TextSt) :
    (segs.foldl (stepSeg remap imgMap ls y og) st).stores = st.stores ++ segs.flatMap segStores := by
  induction segs generalizing st with
  | nil => simp
  | cons s rest ih => simp [ih, stepSeg_stores, List.append_assoc]

private theorem lineSt_stores (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (og : Origin) (st : TextSt) (l : LineOut) :
    (lineSt geom remap imgMap og st l).stores = st.stores ++ l.segs.toList.flatMap segStores := by
  unfold lineSt
  simp only []
  have h : ∀ t : TextSt, t.closeTJ.stores = t.stores := fun t => by
    simp [TextSt.stores, closeTJ_images]
  rw [h, ← Array.foldl_toList, foldl_segs_stores]
  congr 1
  split <;> simp [TextSt.stores, TextSt.op]

private theorem stepLine_stores (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap tags st l).stores = st.stores ++ l.segs.toList.flatMap segStores := by
  unfold stepLine
  have hs := lineSt_stores geom remap imgMap (Origin.of tags l) st l
  dsimp only
  split <;> simpa [TextSt.stores] using hs

private theorem foldl_lines_stores (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (lines : List LineOut) (st : TextSt) :
    (lines.foldl (stepLine geom remap imgMap tags) st).stores
      = st.stores ++ lines.flatMap (fun l => l.segs.toList.flatMap segStores) := by
  induction lines generalizing st with
  | nil => simp
  | cons l rest ih => simp [ih, stepLine_stores, List.append_assoc]

/-- The glyph runs a drawn figure's form paints, for an image's store index. -/
public def figStoreRuns (figs : Array (Option FigForm)) (k : Option Nat) : List (Array Nat) :=
  match k.bind fun k => (figs[k]?).join with
  | some f => runsOf f.body
  | none => []

/-- The glyph runs a page's drawn figures paint, in placement order. -/
public def figureRuns (figs : Array (Option FigForm)) (page : PageOut) : List (Array Nat) :=
  (pageStores page).flatMap (figStoreRuns figs)

private theorem imageOp_runs (ix : GfxPdf.Request → Nat) (figs : Array (Option FigForm)) (i : ImgOut) :
    (imageOp ix figs i).runs = figStoreRuns figs i.store := by
  unfold imageOp figStoreRuns
  cases hf : figOf figs i with
  | some f =>
    have hb : (i.store.bind fun k => (figs[k]?).join) = some f := hf
    simp only [hb, figOp, ContentOp.runs, ContentOp.runsList, List.append_nil, runsOf,
      ContentOp.runsList_eq]
  | none =>
    have hb : (i.store.bind fun k => (figs[k]?).join) = none := hf
    simp only [hb]
    split <;> simp [artifact, ContentOp.runs, ContentOp.runsList]

private theorem inkGroupsList_shape (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tx : (Nat × Nat) → Option (Array TextOp))
    (tags : Array (Option String)) (inks : List InkOut) (hk : ∀ k ∈ inks, InkSetter tx k)
    (out : Array ContentOp)
    (cur : Option (Option Nat × Array ContentOp))
    (hc : ∀ g ∈ cur, ∀ o ∈ g.2, PicOp o)
    (ho : ∀ o ∈ out, ∃ t body, o = .marked t body ∧ ∀ b ∈ body, PicOp b) :
    ∀ o ∈ inkGroupsList geom ix tx tags out cur inks,
      ∃ t body, o = .marked t body ∧ ∀ b ∈ body, PicOp b := by
  have hflush : ∀ (out : Array ContentOp) (cur : Option (Option Nat × Array ContentOp)),
      (∀ g ∈ cur, ∀ o ∈ g.2, PicOp o) →
      (∀ o ∈ out, ∃ t body, o = .marked t body ∧ ∀ b ∈ body, PicOp b) →
      ∀ o ∈ flushGroup tags out cur, ∃ t body, o = .marked t body ∧ ∀ b ∈ body, PicOp b := by
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
    have hrest : ∀ k' ∈ rest, InkSetter tx k' := fun k' h => hk k' (List.mem_cons_of_mem _ h)
    simp only [inkGroupsList]
    have hkk := inkPaint_picOps geom ix tx k (hk k (List.mem_cons_self ..))
    split
    · exact ih hrest out cur hc ho
    · split
      · rename_i lf acc
        split
        · apply ih hrest
          · intro g hg o h
            simp only [Option.mem_def, Option.some.injEq] at hg
            subst hg
            simp only [Array.mem_append] at h
            rcases h with h | h
            · exact hc _ rfl o h
            · exact hkk o h
          · exact ho
        · apply ih hrest
          · intro g hg o h
            simp only [Option.mem_def, Option.some.injEq] at hg
            subst hg
            exact hkk o h
          · exact hflush out _ hc ho
      · apply ih hrest
        · intro g hg o h
          simp only [Option.mem_def, Option.some.injEq] at hg
          subst hg
          exact hkk o h
        · exact ho

private theorem inkGroups_shape (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tx : (Nat × Nat) → Option (Array TextOp)) (tags : Array (Option String))
    (inks : Array InkOut) (hk : ∀ k ∈ inks, InkSetter tx k) :
    ∀ o ∈ inkGroups geom ix tx tags inks,
      ∃ t body, o = .marked t body ∧ ∀ b ∈ body, PicOp b :=
  inkGroupsList_shape geom ix tx tags inks.toList (fun k h => hk k (Array.mem_toList_iff.mp h))
    #[] none (by simp) (by simp)

private theorem artifactBlock_runs (k : Option ArtifactKind) (ops : Array ContentOp) :
    (artifactBlock k ops).toList.flatMap ContentOp.runs = ops.toList.flatMap ContentOp.runs := by
  unfold artifactBlock
  split
  · rename_i h
    simp [Array.isEmpty_iff.mp h]
  · simp [ContentOp.runs, ContentOp.runsList_eq]

mutual

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
  | .marked (.span a) body, n => by
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
  | [], _, acc => by simp [TextOp.numberList]
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
  | .marked (.span a) body, n => by
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
  | [], _, acc => by simp [ContentOp.numberList]
  | o :: rest, n, acc => by
    rw [ContentOp.numberList]
    simp [ContentOp.numberList_runs rest, Array.toList_push, ContentOp.number_runs o n]

end

private theorem numberMarks_runs_list (ops : Array ContentOp) :
    (numberMarks ops).toList.flatMap ContentOp.runs = ops.toList.flatMap ContentOp.runs := by
  unfold numberMarks
  rw [ContentOp.numberList_runs]
  simp

public theorem gidHex_toList (g : Nat) :
    (gidHex g).toList = [Hex.spell true (g / 4096), Hex.spell true (g / 256),
      Hex.spell true (g / 16), Hex.spell true g] := by
  simp [gidHex, pushGid, String.toList_push]

public theorem gidHex_inj {g₁ g₂ : Nat} (h₁ : g₁ < 65536) (h₂ : g₂ < 65536)
    (h : gidHex g₁ = gidHex g₂) : g₁ = g₂ := by
  have hl := congrArg String.toList h
  rw [gidHex_toList, gidHex_toList] at hl
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨e1, e2, e3, e4⟩ := hl
  have := Hex.spell_inj e1
  have := Hex.spell_inj e2
  have := Hex.spell_inj e3
  have := Hex.spell_inj e4
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

public theorem glyphs_inj {a b : Array Nat} (ha : ∀ g ∈ a, g < 65536) (hb : ∀ g ∈ b, g < 65536)
    (h : (TextItem.glyphs a).render = (TextItem.glyphs b).render) : a = b := by
  rw [glyphs_render_exact, glyphs_render_exact] at h
  have h := (String.append_left_inj _).mp h
  have h := (String.append_right_inj _).mp h
  exact Array.toList_inj.mp (join_gidHex_inj _ _ (fun g hg => ha g (Array.mem_toList_iff.mp hg))
    (fun g hg => hb g (Array.mem_toList_iff.mp hg)) h)

public theorem render_not_inj : ∃ a b : Array ContentOp, a ≠ b ∧ render a = render b :=
  ⟨#[.fill Ir.Color.black 0 0 (bp 1) (bp 1)],
    #[.paint (some { paint := .solid Ir.Color.black, evenOdd := false }) none none #[.rect 0 0 (bp 1) (bp 1)]],
    fun h => by have := congrArg (·[0]?) h; simp at this, by
      change (ContentOp.fill Ir.Color.black 0 0 (bp 1) (bp 1)).render =
        (ContentOp.paint (some { paint := .solid Ir.Color.black, evenOdd := false }) none none
          #[.rect 0 0 (bp 1) (bp 1)]).render
      rw [paint_render_exact]
      simp [ContentOp.render, PathOp.render, fillState, strokeState, gsState, paintOp,
        pdfPaintFill, String.append_assoc]
      rfl⟩

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

public theorem inkOps_lines_exact (ops : Array ContentOp) : lines (inkOps ops) = stripMarks (lines ops) := by
  simp only [lines, inkOps, List.toList_toArray]
  exact ContentOp.linesList_ink _

public theorem render_inkOps_exact (ops : Array ContentOp) :
    render (inkOps ops) = joinLines (stripMarks (lines ops)) := by
  rw [render_lines_exact, inkOps_lines_exact]

private theorem inkText_append (a b : Array TextOp) : inkText (a ++ b) = inkText a ++ inkText b := by
  simp [inkText, TextOp.inkList_append]

private theorem inkText_push (ops : Array TextOp) (o : TextOp) :
    inkText (ops.push o) = inkText ops ++ o.ink.toArray := by
  simp [inkText, TextOp.inkList_append, TextOp.inkList]

private theorem inkText_push_marked (ops : Array TextOp) (t : MarkTag) (body : Array TextOp) :
    inkText (ops.push (.marked t body)) = inkText ops ++ inkText body := by
  simp [inkText, TextOp.inkList_append, TextOp.inkList, TextOp.ink]

private theorem TextOp.inkList_eq (l : List TextOp) : TextOp.inkList l = l.flatMap TextOp.ink := by
  induction l with
  | nil => rfl
  | cons o rest ih => simp [TextOp.inkList, ih]

private theorem markHyphens_inkText (ops : Array TextOp) (hs : Array Nat) :
    inkText (markHyphens ops hs) = inkText ops := by
  unfold inkText
  rw [TextOp.inkList_eq, TextOp.inkList_eq,
    markHyphens_flatMap TextOp.ink (fun o => by simp [TextOp.ink, TextOp.inkList]) ops hs]

private def TextSt.plain (st : TextSt) : TextSt := { st with ops := inkText st.ops }

private theorem lineSt_plain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (og : Origin) (st : TextSt) (l : LineOut) :
    lineSt geom remap imgMap og st.plain l = lineSt geom remap imgMap og st l := by
  simp [lineSt, TextSt.plain]

private theorem stepLine_plain (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap tags st l).plain
      = (stepLinePlain geom remap imgMap tags st l).plain := by
  simp only [stepLine, stepLinePlain, TextSt.plain]
  have hempty : ∀ (a b : Array TextOp), b.isEmpty = true → inkText a = inkText (a ++ b) := by
    intro a b hb
    rw [Array.isEmpty_iff.mp hb, Array.append_empty]
  split
  · simp [inkText_push_marked, inkText_append, markHyphens_inkText]
  · split
    · rename_i he
      rw [hempty _ _ he]
    · simp [inkText_push_marked, inkText_append, markHyphens_inkText]
  · split
    · rename_i he
      rw [hempty _ _ he]
    · simp [inkText_push_marked, inkText_append, markHyphens_inkText]

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
  | cons l _ ih => exact ih (stepLinePlain_resp geom remap imgMap tags h l)

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

private theorem op_plainOps (st : TextSt) (o : TextOp) (h : inkText st.ops = st.ops) (hl : o.ink = [o]) :
    inkText (st.op o).ops = (st.op o).ops := by
  simp [TextSt.op, inkText_push, h, hl]

private theorem closeTJ_plainOps (st : TextSt) (h : inkText st.ops = st.ops) :
    inkText st.closeTJ.ops = st.closeTJ.ops := by
  unfold TextSt.closeTJ
  split
  · exact h
  · exact op_plainOps st _ h (by simp [TextOp.ink])

private theorem moveTo_plainOps (st : TextSt) (y : Length) (h : inkText st.ops = st.ops) :
    inkText (st.moveTo y).ops = (st.moveTo y).ops :=
  op_plainOps _ _ (closeTJ_plainOps st h) (by simp [TextOp.ink])

private theorem toPen_plainOps (st : TextSt) (c : Bool) (y : Length) (h : inkText st.ops = st.ops) :
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

private theorem setFont_plainOps (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Length)
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

private theorem setFace_plainOps (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Length) (c : Ir.Color)
    (h : inkText st.ops = st.ops) :
    inkText (st.setFace remap idx size c).ops = (st.setFace remap idx size c).ops :=
  setColor_plainOps _ _ (setFont_plainOps _ _ _ _ (closeTJ_plainOps _ h))

private theorem stepRun_plainOps (remap : Array Nat) (ls y : Length) (st : TextSt) (idx : Nat) (c : Ir.Color)
    (w : Length) (glyphs : Array (Nat × Char × Length)) (ss raise : Length) (h : inkText st.ops = st.ops) :
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

private theorem stepSeg_plainOps (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Length)
    (og : Origin) (st : TextSt) (seg : Seg) (h : inkText st.ops = st.ops) :
    inkText (stepSeg remap imgMap ls y og st seg).ops = (stepSeg remap imgMap ls y og st seg).ops := by
  cases seg with
  | rule | decoration => exact h
  | image => exact h
  | gap | decoratedGap => exact h
  | poly => exact h
  | run =>
    simp only [stepSeg]
    split
    · exact closeTJ_plainOps _ (stepRun_plainOps _ _ _ _ _ _ _ _ _ _ (closeTJ_plainOps _ h))
    · exact stepRun_plainOps _ _ _ _ _ _ _ _ _ _ h

private theorem foldl_segs_plainOps (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Length)
    (og : Origin) (segs : List Seg) (st : TextSt) (h : inkText st.ops = st.ops) :
    inkText (segs.foldl (stepSeg remap imgMap ls y og) st).ops
      = (segs.foldl (stepSeg remap imgMap ls y og) st).ops := by
  induction segs generalizing st with
  | nil => exact h
  | cons s _ ih => exact ih _ (stepSeg_plainOps _ _ _ _ _ _ _ h)

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
  | cons l _ ih => exact ih _ (stepLinePlain_plainOps _ _ _ _ _ _ h)

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

private theorem imageOp_ink (ix : GfxPdf.Request → Nat) (figs : Array (Option FigForm)) (i : ImgOut) :
    (imageOp ix figs i).ink = [imageOpPlain ix figs i] := by
  unfold imageOp imageOpPlain
  split
  · simp [figOp, ContentOp.ink, ContentOp.inkList]
  · split <;> simp [artifact_ink, ContentOp.ink, ContentOp.inkList]

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

private theorem inkList_self (l : List ContentOp) (h : ∀ o ∈ l, o.ink = [o]) :
    ContentOp.inkList l = l := by
  induction l with
  | nil => rfl
  | cons o rest ih =>
    simp only [ContentOp.inkList, h o (List.mem_cons_self ..),
      ih fun o' h' => h o' (List.mem_cons_of_mem _ h'), List.singleton_append]

private theorem picOp_ink (o : ContentOp) (h : PicOp o) : o.ink = [o] := by
  rcases h with h | ⟨t, rfl, ht⟩
  · exact figureOnly_ink o h
  · simp only [GfxPdf.textGroup, ContentOp.ink, ContentOp.inkList, List.append_nil]
    simp [inkText] at ht
    simp [inkText, ht]

private theorem inkPaint_ink (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tx : (Nat × Nat) → Option (Array TextOp)) (k : InkOut) (h : InkSetter tx k) :
    ContentOp.inkList (inkPaint geom ix tx k).toList = (inkPaint geom ix tx k).toList :=
  inkList_self _ fun o ho => picOp_ink o (inkPaint_picOps geom ix tx k h o (Array.mem_toList_iff.mp ho))

private theorem inkGroupsList_ink (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tx : (Nat × Nat) → Option (Array TextOp))
    (tags : Array (Option String)) (inks : List InkOut) (hk : ∀ k ∈ inks, InkSetter tx k)
    (out : Array ContentOp) (cur : Option (Option Nat × Array ContentOp)) :
    ContentOp.inkList (inkGroupsList geom ix tx tags out cur inks).toList
      = ContentOp.inkList out.toList ++ (groupInk cur)
        ++ inks.flatMap (fun k => (inkPaint geom ix tx k).toList) := by
  induction inks generalizing out cur with
  | nil => simp [inkGroupsList, flushGroup_ink]
  | cons k rest ih =>
    have hrest : ∀ k' ∈ rest, InkSetter tx k' := fun k' h => hk k' (List.mem_cons_of_mem _ h)
    have hkk := inkPaint_ink geom ix tx k (hk k (List.mem_cons_self ..))
    simp only [inkGroupsList]
    split
    · next he =>
      rw [ih hrest]
      simp [Array.isEmpty_iff.mp he]
    · split
      · split
        · rw [ih hrest]
          simp [groupInk, ContentOp.inkList_append, hkk, List.append_assoc]
        · rw [ih hrest, flushGroup_ink]
          simp [groupInk, hkk, List.append_assoc]
      · rw [ih hrest]
        simp [groupInk, hkk, List.append_assoc]

private theorem inkGroups_ink (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tx : (Nat × Nat) → Option (Array TextOp))
    (tags : Array (Option String)) (inks : Array InkOut) (hk : ∀ k ∈ inks, InkSetter tx k) :
    ContentOp.inkList (inkGroups geom ix tx tags inks).toList
      = inks.toList.flatMap (fun k => (inkPaint geom ix tx k).toList) := by
  unfold inkGroups
  rw [inkGroupsList_ink geom ix tx tags inks.toList (fun k h => hk k (Array.mem_toList_iff.mp h))]
  simp [groupInk, ContentOp.inkList]

mutual

private theorem TextOp.ink_runs : ∀ o : TextOp, TextOp.runsList o.ink = o.runs
  | .scale _ => rfl
  | .move _ _ => rfl
  | .font _ _ => rfl
  | .color _ => rfl
  | .show _ => by simp [TextOp.ink, TextOp.runsList, TextOp.runs]
  | .marked _ body => by
    simp only [TextOp.ink, TextOp.runs]
    exact TextOp.inkList_runs body.toList

private theorem TextOp.inkList_runs : ∀ l : List TextOp,
    TextOp.runsList (TextOp.inkList l) = TextOp.runsList l
  | [] => rfl
  | o :: rest => by
    simp only [TextOp.inkList, TextOp.runsList]
    rw [TextOp.runsList_eq, List.flatMap_append, ← TextOp.runsList_eq, ← TextOp.runsList_eq,
      TextOp.ink_runs o, TextOp.inkList_runs rest]

end

mutual

private theorem ContentOp.ink_runs : ∀ o : ContentOp, ContentOp.runsList o.ink = o.runs
  | .fill .. => rfl
  | .paint .. => rfl
  | .shade .. => rfl
  | .outline .. => rfl
  | .xobject .. => by simp [ContentOp.ink, ContentOp.runsList]
  | .group m gs clips body => by
    simp only [ContentOp.ink, ContentOp.runsList, ContentOp.runs,
      List.append_nil]
    exact ContentOp.inkList_runs body.toList
  | .text ops => by
    simp only [ContentOp.ink, ContentOp.runsList, ContentOp.runs, List.append_nil, inkText]
    rw [← TextOp.runsList_eq, ← TextOp.runsList_eq, TextOp.inkList_runs]
  | .image .. => rfl
  | .imageMissing .. => rfl
  | .marked _ body => by
    simp only [ContentOp.ink, ContentOp.runs]
    exact ContentOp.inkList_runs body.toList

private theorem ContentOp.inkList_runs : ∀ l : List ContentOp,
    ContentOp.runsList (ContentOp.inkList l) = ContentOp.runsList l
  | [] => rfl
  | o :: rest => by
    simp only [ContentOp.inkList, ContentOp.runsList]
    rw [ContentOp.runsList_eq, List.flatMap_append, ← ContentOp.runsList_eq,
      ← ContentOp.runsList_eq, ContentOp.ink_runs o, ContentOp.inkList_runs rest]

end

private theorem runsOf_inkOps (ops : Array ContentOp) : runsOf (inkOps ops) = runsOf ops := by
  unfold runsOf inkOps
  rw [← ContentOp.runsList_eq, ← ContentOp.runsList_eq, List.toList_toArray,
    ContentOp.inkList_runs]

/-- A page line's glyph runs, segment by segment. -/
public def _root_.LeanTex.Core.Layout.LineOut.glyphRuns (l : LineOut) : List (Array Nat) :=
  l.segs.toList.flatMap segRuns

/-- A page's glyph runs in the order its content stream paints them: each picture's labels where
the picture paints them, then every other line. -/
public def paintRuns (page : PageOut) : List (Array Nat) :=
  let keys := inkLabelKeys page.inks
  let route := routesLabels page.inks
  let held := page.lines.toList.filter (heldBy route keys)
  (if route then keys.flatMap fun k => (held.filter (·.labelKey? == some k)).flatMap Layout.LineOut.glyphRuns
   else []) ++
    (page.lines.toList.filter fun l => !heldBy route keys l).flatMap Layout.LineOut.glyphRuns

/-- A page's lines in the order its content stream paints their glyphs. -/
public def paintLines (page : PageOut) : List LineOut :=
  let keys := inkLabelKeys page.inks
  let route := routesLabels page.inks
  let held := page.lines.toList.filter (heldBy route keys)
  (if route then keys.flatMap fun k => held.filter (·.labelKey? == some k) else []) ++
    page.lines.toList.filter fun l => !heldBy route keys l

public theorem paintRuns_lines_exact (page : PageOut) :
    paintRuns page = (paintLines page).flatMap Layout.LineOut.glyphRuns := by
  simp only [paintRuns, paintLines]
  by_cases h : routesLabels page.inks = true <;>
    simp [h, List.flatMap_append, List.flatMap_assoc]

private theorem withoutGlyphs_runs (l : LineOut) : l.withoutGlyphs.glyphRuns = [] := by
  simp only [Layout.LineOut.glyphRuns, LineOut.withoutGlyphs, Array.toList_map, List.flatMap_map]
  apply List.flatMap_eq_nil_iff.mpr
  intro s _
  cases s <;> simp [Layout.Seg.withoutGlyphs, segRuns]

private theorem flatMap_ite_filter {α β : Type} (p : α → Bool) (f : α → List β) (l : List α) :
    l.flatMap (fun a => if p a then [] else f a) = (l.filter fun a => !p a).flatMap f := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    by_cases h : p a
    · rw [List.flatMap_cons, List.filter_cons]
      simp [h, ih]
    · rw [List.flatMap_cons, List.filter_cons]
      simp [h, ih]

private theorem bodyLines_runs (page : PageOut) :
    (bodyLines page).toList.flatMap Layout.LineOut.glyphRuns =
      (page.lines.toList.filter fun l =>
        !heldBy (routesLabels page.inks) (inkLabelKeys page.inks) l).flatMap Layout.LineOut.glyphRuns := by
  unfold bodyLines
  simp only [Array.toList_map, List.flatMap_map]
  have := flatMap_ite_filter (heldBy (routesLabels page.inks) (inkLabelKeys page.inks))
    Layout.LineOut.glyphRuns page.lines.toList
  rw [← this]
  apply Gfx.flatMap_congr_mem
  intro l _
  split
  · exact withoutGlyphs_runs l
  · rfl

private theorem withoutGlyphs_stores (l : LineOut) :
    l.withoutGlyphs.segs.toList.flatMap segStores = l.segs.toList.flatMap segStores := by
  simp only [LineOut.withoutGlyphs, Array.toList_map, List.flatMap_map]
  apply Gfx.flatMap_congr_mem
  intro s _
  cases s <;> rfl

private theorem bodyLines_stores (page : PageOut) :
    (bodyLines page).toList.flatMap (fun l => l.segs.toList.flatMap segStores) = pageStores page := by
  unfold bodyLines pageStores
  simp only [Array.toList_map, List.flatMap_map]
  apply Gfx.flatMap_congr_mem
  intro l _
  split
  · exact withoutGlyphs_stores l
  · rfl

private theorem stepLinePlain_runs (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) (h : st.items = #[]) :
    (stepLinePlain geom remap imgMap tags st l).runs = st.runs ++ l.glyphRuns ∧
      (stepLinePlain geom remap imgMap tags st l).items = #[] := by
  have hs := lineSt_runs geom remap imgMap (Origin.of tags l) st l
  have hi := lineSt_items geom remap imgMap (Origin.of tags l) st l
  simp only [TextSt.runs, h, hi, Array.toList_empty, List.flatMap_nil, List.append_nil,
    List.nil_append] at hs
  refine ⟨?_, hi⟩
  simp only [stepLinePlain, TextSt.runs, hi, h, Array.toList_append, List.flatMap_append, hs,
    Array.toList_empty, List.flatMap_nil, List.append_nil, Layout.LineOut.glyphRuns]

private theorem foldl_stepLinePlain_runs (geom : Geom) (remap : Array Nat)
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ls : List LineOut)
    (st : TextSt) (h : st.items = #[]) :
    (ls.foldl (stepLinePlain geom remap imgMap tags) st).runs = st.runs ++ ls.flatMap Layout.LineOut.glyphRuns ∧
      (ls.foldl (stepLinePlain geom remap imgMap tags) st).items = #[] := by
  induction ls generalizing st with
  | nil => simp [h]
  | cons l rest ih =>
    obtain ⟨hr, hi⟩ := stepLinePlain_runs geom remap imgMap tags st l h
    obtain ⟨hr', hi'⟩ := ih _ hi
    refine ⟨?_, hi'⟩
    simp [hr', hr, List.append_assoc]

private theorem labelText_runs (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (held : List LineOut)
    (k : Nat × Nat) :
    (labelText geom remap widths imgMap tags held k).toList.flatMap
        (fun t => TextOp.runsList t.toList) =
      (held.filter (·.labelKey? == some k)).flatMap Layout.LineOut.glyphRuns := by
  unfold labelText
  generalize held.filter (·.labelKey? == some k) = ls
  cases ls with
  | nil => rfl
  | cons l rest =>
    obtain ⟨hr, hi⟩ := foldl_stepLinePlain_runs geom remap imgMap tags (l :: rest) { widths } rfl
    simp only [TextSt.runs, hi, Array.toList_empty, List.flatMap_nil, List.append_nil,
      List.nil_append] at hr
    simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      TextOp.runsList_eq]
    exact hr

private theorem labelText_plain (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (held : List LineOut)
    (k : Nat × Nat) (t : Array TextOp) (h : labelText geom remap widths imgMap tags held k = some t) :
    inkText t = t := by
  unfold labelText at h
  generalize held.filter (·.labelKey? == some k) = ls at h
  cases ls with
  | nil => cases h
  | cons l rest =>
    cases h
    exact foldl_stepLinePlain_plainOps geom remap imgMap tags (l :: rest) { widths } rfl

private theorem pageLabels_setter (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (page : PageOut) :
    ∀ k ∈ page.inks, InkSetter (pageLabels geom remap widths imgMap tags page).text k := by
  intro k hk
  unfold pageLabels
  by_cases hr : routesLabels page.inks = true
  · right
    simp only [hr, ↓reduceIte]
    have hall := hr
    simp only [routesLabels, Bool.and_eq_true, Array.all_eq_true', decide_eq_true_eq] at hall
    have hk' := hall.1 k hk
    simp only [Array.isEmpty_iff] at hk'
    exact ⟨hk', fun key t ht => labelText_plain _ _ _ _ _ _ key t ht⟩
  · left
    intro key
    simp [hr]

private theorem inkPaint_runs_none (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tx : (Nat × Nat) → Option (Array TextOp)) (k : InkOut) (h : ∀ key, tx key = none) :
    ContentOp.runsList (inkPaint geom ix tx k).toList = [] := by
  rw [ContentOp.runsList_eq]
  apply List.flatMap_eq_nil_iff.mpr
  intro o ho
  rcases inkPaint_picOps geom ix tx k (Or.inl h) o (Array.mem_toList_iff.mp ho) with hf | ⟨t, rfl, _⟩
  · exact figureOnly_runs o hf
  · exfalso
    have hlo : (fun (_ : GfxPdf.Frame) (key : Nat × Nat) => (tx key).toArray.map GfxPdf.textGroup)
        = fun _ _ => #[] := by
      funext _ key
      simp [h key]
    unfold inkPaint at ho
    rw [hlo] at ho
    have := emit_figureOnly ix (fun _ _ => #[]) (by simp) _ k.fig _ (Array.mem_toList_iff.mp ho)
    simp [GfxPdf.textGroup, ContentOp.figureOnly, ContentOp.figureOnlyList] at this

private theorem inkPaint_runs_top (geom : Geom) (ix : GfxPdf.Request → Nat)
    (tx : (Nat × Nat) → Option (Array TextOp)) (k : InkOut)
    (htop : k.fig.labelsTop = true) (hsym : k.fig.symbols = #[]) :
    ContentOp.runsList (inkPaint geom ix tx k).toList =
      (k.fig.nodes.toList.flatMap fun n => n.label?.toList).flatMap
        fun key => (tx key).toList.flatMap fun t => TextOp.runsList t.toList := by
  unfold inkPaint GfxPdf.emit
  rw [GfxPdf.emitList_flatMap]
  have hb : GfxPdf.bodyOpsOf ix (fun _ key => (tx key).toArray.map GfxPdf.textGroup) k.fig = #[] := by
    simp [GfxPdf.bodyOpsOf, Gfx.Figure.bodies, hsym]
  rw [hb, ContentOp.runsList_eq, List.toList_toArray, List.flatMap_assoc, List.flatMap_assoc]
  apply Gfx.flatMap_congr_mem
  intro n hn
  have hnt : n.topOk = true := by
    simp only [Gfx.Figure.labelsTop, Bool.and_eq_true, Array.all_eq_true'] at htop
    exact htop.1 n (Array.mem_toList_iff.mp hn)
  by_cases hlab : ∃ l, n = .label l
  · obtain ⟨key, rfl⟩ := hlab
    cases htx : tx key with
    | none => simp [GfxPdf.emitOne, htx, Gfx.Node.label?]
    | some t =>
      simp [GfxPdf.emitOne, htx, Gfx.Node.label?, GfxPdf.textGroup, ContentOp.runs,
        ContentOp.runsList, TextOp.runsList_eq]
  · have hf := Gfx.Node.labelFree_of_topOk n hnt fun l he => hlab ⟨l, he⟩
    have hl : n.label? = none := by
      cases n with
      | label l => exact absurd rfl fun h => hlab ⟨l, h⟩
      | draw | group | use | stamp | image | words => rfl
    rw [hl, emitOne_labelOps_irrel ix _ (fun _ _ => #[]) _ _ n _ #[] hf]
    simp only [Option.toList_none, List.flatMap_nil]
    apply List.flatMap_eq_nil_iff.mpr
    intro o ho
    exact figureOnly_runs o (emitOne_figureOnly ix (fun _ _ => #[]) (by simp) _ #[] (by simp) n _ #[]
      (by simp) o (Array.mem_toList_iff.mp ho))

public theorem contentOps_text (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (figs : Array (Option FigForm)) (page : PageOut) :
    runsOf (contentOps geom remap widths imgMap tags ix figs page) =
      paintRuns page ++ figureRuns figs page := by
  have hset := pageLabels_setter geom remap widths imgMap tags page
  have hpaths : (inkGroups geom ix (pageLabels geom remap widths imgMap tags page).text tags
      page.inks).toList.flatMap ContentOp.runs =
        (if routesLabels page.inks then (inkLabelKeys page.inks).flatMap fun k =>
          ((page.lines.toList.filter (heldBy (routesLabels page.inks) (inkLabelKeys page.inks))).filter
            (·.labelKey? == some k)).flatMap Layout.LineOut.glyphRuns
         else []) := by
    have h1 := runsOf_inkOps
      (inkGroups geom ix (pageLabels geom remap widths imgMap tags page).text tags page.inks)
    unfold runsOf inkOps at h1
    rw [List.toList_toArray] at h1
    rw [← h1, inkGroups_ink geom ix _ tags page.inks hset, List.flatMap_assoc]
    by_cases hr : routesLabels page.inks = true
    · have hall := hr
      simp only [routesLabels, Bool.and_eq_true, Array.all_eq_true', decide_eq_true_eq] at hall
      simp only [hr, ↓reduceIte]
      unfold inkLabelKeys
      rw [List.flatMap_assoc]
      apply Gfx.flatMap_congr_mem
      intro k hk
      have hk' := hall.1 k (Array.mem_toList_iff.mp hk)
      simp only [Array.isEmpty_iff] at hk'
      rw [← ContentOp.runsList_eq, inkPaint_runs_top geom ix _ k hk'.1 hk'.2]
      apply Gfx.flatMap_congr_mem
      intro key _
      unfold pageLabels
      simp only [hr, ↓reduceIte]
      exact labelText_runs geom remap widths imgMap tags _ key
    · simp only [hr, Bool.false_eq_true, ↓reduceIte]
      apply List.flatMap_eq_nil_iff.mpr
      intro k _
      rw [← ContentOp.runsList_eq]
      apply inkPaint_runs_none
      intro key
      unfold pageLabels
      simp [hr]
  unfold contentOps
  unfold runsOf
  simp only [Array.toList_append, List.flatMap_append, artifactBlock_runs, numberMarks_runs_list]
  simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Array.toList_map, List.flatMap_map, imageOp_runs]
  simp only [ContentOp.runs, polyOp, flatMap_nil_fun, List.append_nil, List.nil_append]
  rw [hpaths]
  have hr := foldl_lines_runs geom remap imgMap tags (bodyLines page).toList { widths }
  have hi := foldl_lines_items geom remap imgMap tags (bodyLines page).toList { widths } rfl
  have hs := foldl_lines_stores geom remap imgMap tags (bodyLines page).toList { widths }
  rw [Array.foldl_toList] at hr hi hs
  simp only [TextSt.runs, hi, Array.toList_empty, List.flatMap_nil, List.append_nil,
    List.nil_append] at hr
  simp only [TextSt.stores] at hs
  have hr' : ((bodyLines page).foldl (stepLine geom remap imgMap tags) { widths }).ops.toList.flatMap
      TextOp.runs = (bodyLines page).toList.flatMap Layout.LineOut.glyphRuns := hr
  have himg : (((bodyLines page).foldl (stepLine geom remap imgMap tags) { widths }).images.toList.flatMap
      fun i => figStoreRuns figs i.store) = figureRuns figs page := by
    rw [← List.flatMap_map (f := ImgOut.store) (g := figStoreRuns figs), hs]
    simp [figureRuns, bodyLines_stores]
  rw [hr', bodyLines_runs page, himg]
  simp [paintRuns, List.append_assoc]

private theorem flatMap_filter_key_perm {α κ : Type} [BEq κ] [LawfulBEq κ] (g : α → Option κ) :
    ∀ (K : List κ) (L : List α), K.Nodup → (∀ x ∈ L, ∃ k ∈ K, g x = some k) →
      (K.flatMap fun k => L.filter fun x => g x == some k).Perm L := by
  intro K
  induction K with
  | nil =>
    intro L _ hL
    have : L = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
      obtain ⟨k, hk, _⟩ := hL x hx
      simp at hk
    subst this
    exact List.Perm.refl _
  | cons k rest ih =>
    intro L hn hL
    rw [List.nodup_cons] at hn
    let L₂ := L.filter fun x => !(g x == some k)
    have hrest : (rest.flatMap fun k' => L.filter fun x => g x == some k') =
        rest.flatMap fun k' => L₂.filter fun x => g x == some k' := by
      apply Gfx.flatMap_congr_mem
      intro k' hk'
      simp only [L₂, List.filter_filter]
      apply List.filter_congr
      intro x _
      by_cases hx : g x = some k'
      · have hne : k' ≠ k := fun he => hn.1 (he ▸ hk')
        simp [hx, hne]
      · simp [hx]
    have hL₂ : ∀ x ∈ L₂, ∃ k' ∈ rest, g x = some k' := by
      intro x hx
      simp only [L₂, List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hx
      obtain ⟨k', hk', hg⟩ := hL x hx.1
      rcases List.mem_cons.mp hk' with rfl | hk''
      · exact absurd hg hx.2
      · exact ⟨k', hk'', hg⟩
    rw [List.flatMap_cons, hrest]
    exact ((ih L₂ hn.2 hL₂).append_left _).trans (List.filter_append_perm _ L)

public theorem paintRuns_text (page : PageOut) : (paintRuns page).Perm (pageRuns page) := by
  unfold paintRuns pageRuns
  by_cases hr : routesLabels page.inks = true
  · simp only [hr, ↓reduceIte]
    have hall := hr
    simp only [routesLabels, Bool.and_eq_true, Array.all_eq_true', decide_eq_true_eq] at hall
    let held := page.lines.toList.filter (heldBy true (inkLabelKeys page.inks))
    have hkeys : ∀ x ∈ held, ∃ k ∈ inkLabelKeys page.inks, x.labelKey? = some k := by
      intro x hx
      simp only [held, List.mem_filter, heldBy, Bool.true_and] at hx
      cases hk : x.labelKey? with
      | none => simp [hk] at hx
      | some k =>
        simp only [hk] at hx
        exact ⟨k, List.contains_iff_mem.mp hx.2, rfl⟩
    have hp := flatMap_filter_key_perm LineOut.labelKey? (inkLabelKeys page.inks) held hall.2 hkeys
    rw [← List.flatMap_assoc]
    have hsplit := List.filter_append_perm (heldBy true (inkLabelKeys page.inks)) page.lines.toList
    refine ((hp.flatMap_right Layout.LineOut.glyphRuns).append_right _).trans ?_
    rw [← List.flatMap_append]
    exact hsplit.flatMap_right _
  · simp only [hr, Bool.false_eq_true, ↓reduceIte, heldBy, Bool.false_and, Bool.not_false,
      List.nil_append]
    rw [List.filter_eq_self.mpr (fun _ _ => rfl)]
    exact List.Perm.of_eq rfl

mutual

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
  | .marked (.span a) body, n => by
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
  | [], _, acc => by simp [TextOp.numberList, TextOp.inkList]
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
  | .marked (.span a) body, n => by
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
  | [], _, acc => by simp [ContentOp.numberList, ContentOp.inkList]
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

public theorem mark_ink_exact (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (figs : Array (Option FigForm)) (page : PageOut) :
    inkOps (contentOps geom remap widths imgMap tags ix figs page)
      = contentOpsPlain geom remap widths imgMap tags ix figs page := by
  have hset := pageLabels_setter geom remap widths imgMap tags page
  unfold contentOps contentOpsPlain
  simp only [inkOps, Array.toList_append, ContentOp.inkList_append, numberMarks_ink_list]
  have hp := foldl_stepLine_plain geom remap imgMap tags (bodyLines page).toList { widths }
  rw [Array.foldl_toList, Array.foldl_toList] at hp
  have hpo := foldl_stepLinePlain_plainOps geom remap imgMap tags (bodyLines page).toList
    { widths } rfl
  rw [Array.foldl_toList] at hpo
  have hops : inkText ((bodyLines page).foldl (stepLine geom remap imgMap tags) { widths }).ops
      = ((bodyLines page).foldl (stepLinePlain geom remap imgMap tags) { widths }).ops := by
    rw [← hpo]; exact congrArg TextSt.ops hp
  have himg := congrArg TextSt.images hp
  have hrul := congrArg TextSt.rules hp
  have hmrk := congrArg TextSt.marks hp
  have hpol := congrArg TextSt.polys hp
  simp only [TextSt.plain] at himg hrul hmrk hpol
  simp only [Array.toList_push, ContentOp.inkList_append,
    artifactBlock_ink, inkGroups_ink geom ix _ tags page.inks hset, Array.toList_map,
    Array.toList_append, ContentOp.inkList, ContentOp.ink, hops, himg, hrul, hmrk, hpol,
    List.append_nil]
  rw [inkList_map _ (fun f => ContentOp.fill f.color (geom.bleed + f.x)
      (geom.bleed + geom.pageH - f.y - f.h) f.w f.h) _ (fun f => by simp [ContentOp.ink]),
    inkList_map _ (imageOpPlain ix figs) _ (imageOp_ink ix figs),
    inkList_map _ (fun (t : Ir.Color × Length × Length × Length × Length) =>
      ContentOp.fill t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) _ (fun t => by simp [ContentOp.ink]),
    inkList_map _ (fun (t : Ir.Color × Length × Length × Length × Length) =>
      ContentOp.fill t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) _ (fun t => by simp [ContentOp.ink]),
    inkList_map _ polyOp _ (fun p => by simp [polyOp, ContentOp.ink]),
    inkList_map _ (fun f => ContentOp.fill f.color (geom.bleed + f.x)
      (geom.bleed + geom.pageH - f.y - f.h) f.w f.h) _ (fun f => by simp [ContentOp.ink])]
  apply Array.toList_inj.mp
  simp [Array.toList_append, Array.toList_push, Array.toList_map, Array.toList_flatMap]

private def TextOp.isMarked : TextOp → Bool
  | .marked _ _ => true
  | .scale _ => false
  | .move _ _ => false
  | .font _ _ => false
  | .color _ => false
  | .show _ => false

/-- A page-level operation with nothing bare under it: a wrapper, or the text object with every
operator of its own wrapped. -/
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
  | cons l _ ih => exact ih _ (stepLine_marked geom remap imgMap tags st l h)

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

private theorem imageOp_wrapped (ix : GfxPdf.Request → Nat) (figs : Array (Option FigForm))
    (i : ImgOut) : (imageOp ix figs i).wrapped = true := by
  unfold imageOp
  split
  · rfl
  · split <;> rfl

public theorem wrapped_covers (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (figs : Array (Option FigForm)) (page : PageOut) :
    ∀ o ∈ contentOps geom remap widths imgMap tags ix figs page, o.wrapped = true := by
  unfold contentOps numberMarks
  intro o ho
  simp only [Array.mem_append] at ho
  rcases ho with ((hf | hk) | hm) | hr
  · rw [mem_artifactBlock hf]; rfl
  · rw [mem_artifactBlock hk]; rfl
  · refine ContentOp.numberList_wrapped _ _ _ (by simp) ?_ o hm
    intro o ho
    simp only [Array.mem_toList_iff, Array.mem_append, Array.mem_push, Array.mem_map] at ho
    rcases ho with (hp | rfl) | ⟨i, _, rfl⟩
    · obtain ⟨t, body, rfl, _⟩ := inkGroups_shape geom ix _ tags page.inks
        (pageLabels_setter geom remap widths imgMap tags page) o hp
      rfl
    · simp only [ContentOp.wrapped, Array.all_eq_true_iff_forall_mem]
      have := foldl_lines_marked geom remap imgMap tags (bodyLines page).toList { widths }
        (by simp)
      rw [Array.foldl_toList] at this
      exact this
    · exact imageOp_wrapped ix figs i
  · rw [mem_artifactBlock hr]; rfl

public theorem artifacts_covers (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (figs : Array (Option FigForm)) (page : PageOut) :
    ∀ o ∈ contentOps geom remap widths imgMap tags ix figs page, o.decoration = false := by
  intro o ho
  have h := wrapped_covers geom remap widths imgMap tags ix figs page o ho
  cases o <;> simp_all [ContentOp.wrapped, ContentOp.decoration]

private def Line.contentOpen : Line → Option (Nat × Nat)
  | .open (.content _ m k) => some (m, k)
  | .open (.artifact _) => none
  | .open (.span _) => none
  | .op _ => none
  | .emc => none

public def Line.isPaginationOpen : Line → Bool
  | .open (.artifact (some .pagination)) => true
  | .open (.artifact (some .layout)) => false
  | .open (.artifact (some .page)) => false
  | .open (.artifact none) => false
  | .open (.content _ _ _) => false
  | .open (.span _) => false
  | .op _ => false
  | .emc => false

/-- The `(identifier, leaf)` pairs a stream's content openers carry, in stream order. -/
public def contentOpens (ls : List Line) : List (Nat × Nat) := ls.filterMap Line.contentOpen

mutual

private def TextOp.marks (acc : Array (Nat × Nat)) : TextOp → Array (Nat × Nat)
  | .scale _ => acc
  | .move _ _ => acc
  | .font _ _ => acc
  | .color _ => acc
  | .show _ => acc
  | .marked (.artifact _) body => TextOp.marksList acc body.toList
  | .marked (.span _) body => TextOp.marksList acc body.toList
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
  | .marked (.span _) body => ContentOp.marksList acc body.toList
  | .marked (.content _ m k) body => ContentOp.marksList (acc.push (m, k)) body.toList

private def ContentOp.marksList (acc : Array (Nat × Nat)) : List ContentOp → Array (Nat × Nat)
  | [] => acc
  | o :: rest => ContentOp.marksList (ContentOp.marks acc o) rest

end

/-- The marked content of one page: its identifiers and the leaves they paint. -/
public def pageMarks (ops : Array ContentOp) : Array (Nat × Nat) := ContentOp.marksList #[] ops.toList

private theorem contentOpens_append (a b : List Line) :
    contentOpens (a ++ b) = contentOpens a ++ contentOpens b := by
  simp [contentOpens, List.filterMap_append]

private theorem contentOpens_op (s : String) : contentOpens [.op s] = [] := rfl
private theorem contentOpens_emc : contentOpens [.emc] = [] := rfl
private theorem contentOpens_nil : contentOpens [] = [] := rfl

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
  | .marked (.span a) body, n => by
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
  | .marked (.span a) body, n => by
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
  | .marked (.span a) body, acc => by
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
  | .marked (.span a) body, acc => by
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

public theorem pageMarks_eq_contentOpens (ops : Array ContentOp) :
    pageMarks ops = (contentOpens (lines ops)).toArray := by
  unfold pageMarks lines
  rw [ContentOp.marksList_eq_contentOpens]
  simp

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

public theorem mcids_partition_covers (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (figs : Array (Option FigForm)) (page : PageOut) :
    (∀ o ∈ contentOps geom remap widths imgMap tags ix figs page, o.wrapped = true)
    ∧ (pageMarks (contentOps geom remap widths imgMap tags ix figs page)).toList.map Prod.fst
        = List.range (pageMarks (contentOps geom remap widths imgMap tags ix figs page)).size := by
  refine ⟨wrapped_covers geom remap widths imgMap tags ix figs page, ?_⟩
  unfold contentOps
  have hA := fillBlock_contentOpens none (page.fills.map fun f =>
    ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h)
    (fun o ho => by
      simp only [Array.mem_map] at ho
      obtain ⟨f, _, rfl⟩ := ho
      exact Or.inl ⟨_, _, _, _, _, rfl⟩)
  have hC := fillBlock_contentOpens (some .layout)
    (((((bodyLines page).foldl (stepLine geom remap imgMap tags) { widths }).rules.map
      fun (c, x, y, w, h) => ContentOp.fill c x y w h) ++
      ((bodyLines page).foldl (stepLine geom remap imgMap tags) { widths }).polys.map polyOp) ++
      page.front.map fun f =>
        ContentOp.fill f.color (geom.bleed + f.x) (geom.bleed + geom.pageH - f.y - f.h) f.w f.h)
    (fun o ho => by
      simp only [Array.mem_append, Array.mem_map] at ho
      rcases ho with (⟨t, _, rfl⟩ | ⟨p, _, rfl⟩) | ⟨f, _, rfl⟩
      · exact Or.inl ⟨_, _, _, _, _, rfl⟩
      · exact Or.inr ⟨_, _, _, _, rfl⟩
      · exact Or.inl ⟨_, _, _, _, _, rfl⟩)
  have hK := fillBlock_contentOpens (some .layout)
    (((bodyLines page).foldl (stepLine geom remap imgMap tags) { widths }).marks.map
      fun (c, x, y, w, h) => ContentOp.fill c x y w h)
    (fun o ho => by
      simp only [Array.mem_map] at ho
      obtain ⟨t, _, rfl⟩ := ho
      exact Or.inl ⟨_, _, _, _, _, rfl⟩)
  have hmid : ∀ (a k m c : Array ContentOp),
      contentOpens (ContentOp.linesList a.toList) = [] →
      contentOpens (ContentOp.linesList k.toList) = [] →
      contentOpens (ContentOp.linesList c.toList) = [] →
      pageMarks (((a ++ k) ++ m) ++ c) = pageMarks m := by
    intro a k m c ha hk hc
    rw [pageMarks_eq_contentOpens, pageMarks_eq_contentOpens]
    unfold lines
    rw [Array.toList_append, Array.toList_append, Array.toList_append, ContentOp.linesList_append,
      ContentOp.linesList_append, ContentOp.linesList_append, contentOpens_append,
      contentOpens_append, contentOpens_append, ha, hk, hc]
    simp
  rw [hmid _ _ _ _ hA hK hC]
  exact numberMarks_mcids_exact _

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

private theorem TextOp.linesList_eq (l : List TextOp) : TextOp.linesList l = l.flatMap TextOp.lines := by
  induction l with
  | nil => rfl
  | cons o rest ih => simp [TextOp.linesList, ih]

private theorem markHyphens_textArtifacts (ops : Array TextOp) (hs : Array Nat) :
    textArtifacts (markHyphens ops hs) = textArtifacts ops := by
  unfold textArtifacts
  rw [TextOp.linesList_eq, TextOp.linesList_eq, List.countP_eq_length_filter,
    List.countP_eq_length_filter, List.filter_flatMap, List.filter_flatMap,
    markHyphens_flatMap (fun o => o.lines.filter Line.isPaginationOpen)
      (fun o => by simp [TextOp.lines, TextOp.linesList, Line.isPaginationOpen]) ops hs]

private theorem stepLine_textArtifacts (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    textArtifacts (stepLine geom remap imgMap tags st l).ops
      = textArtifacts st.ops + (if l.furniture then 1 else 0) := by
  unfold textArtifacts
  have hpush : ∀ og t, (TextOp.linesList (st.ops.push (.marked t
      (markHyphens (lineSt geom remap imgMap og st l).ops
        (lineSt geom remap imgMap og st l).hyphens))).toList).countP Line.isPaginationOpen
      = (TextOp.linesList st.ops.toList).countP Line.isPaginationOpen
        + (if (Line.open t).isPaginationOpen then 1 else 0) := by
    intro og t
    have h0 := lineSt_textArtifacts geom remap imgMap og st l
    unfold textArtifacts at h0
    have hm := markHyphens_textArtifacts (lineSt geom remap imgMap og st l).ops
      (lineSt geom remap imgMap og st l).hyphens
    unfold textArtifacts at hm
    rw [TextOp.linesList_push, List.countP_append, TextOp.lines, List.countP_cons,
      List.countP_append, hm, h0]
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
      split <;> simp; omega
  rw [← Array.foldl_toList, h, ← Array.length_toList, Array.toList_filter]
  simp [textArtifacts, TextOp.linesList]

/-! ### Generated hyphens -/

/-- `st'` holds `st`'s operators and hyphen places, then operators showing nothing as a hyphen. -/
private def HExt (st st' : TextSt) : Prop :=
  (∃ ext : Array TextOp, st'.ops = st.ops ++ ext ∧ ∀ o ∈ ext, o.spanRuns = []) ∧
    st'.hyphens = st.hyphens

private theorem HExt.refl (st : TextSt) : HExt st st := ⟨⟨#[], by simp, by simp⟩, rfl⟩

private theorem HExt.trans {a b c : TextSt} (h1 : HExt a b) (h2 : HExt b c) : HExt a c := by
  obtain ⟨⟨e1, he1, hs1⟩, hh1⟩ := h1
  obtain ⟨⟨e2, he2, hs2⟩, hh2⟩ := h2
  refine ⟨⟨e1 ++ e2, by rw [he2, he1, Array.append_assoc], ?_⟩, by rw [hh2, hh1]⟩
  intro o ho
  rcases Array.mem_append.mp ho with h | h
  · exact hs1 o h
  · exact hs2 o h

private theorem HExt.ofEq {a b : TextSt} (hops : b.ops = a.ops) (hh : b.hyphens = a.hyphens) :
    HExt a b := ⟨⟨#[], by simp [hops], by simp⟩, hh⟩

private theorem HExt.push (st : TextSt) (o : TextOp) (h : o.spanRuns = []) :
    HExt st { st with ops := st.ops.push o } :=
  ⟨⟨#[o], by simp, by simpa using h⟩, rfl⟩

private theorem closeTJ_hext (st : TextSt) : HExt st st.closeTJ := by
  unfold TextSt.closeTJ
  split
  · exact HExt.refl st
  · exact HExt.push st _ rfl

private theorem op_hext (st : TextSt) (o : TextOp) (h : o.spanRuns = []) : HExt st (st.op o) :=
  HExt.push st o h

private theorem moveTo_hext (st : TextSt) (y : Length) : HExt st (st.moveTo y) :=
  (closeTJ_hext st).trans (op_hext st.closeTJ (.move st.x y) rfl)

private theorem toPen_hext (st : TextSt) (c : Bool) (y : Length) : HExt st (st.toPen c y) := by
  unfold TextSt.toPen
  split
  · dsimp only
    split
    · split
      · exact HExt.refl st
      · exact HExt.ofEq rfl rfl
    · exact moveTo_hext st y
  · exact moveTo_hext st y

private theorem setFace_hext (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Length)
    (c : Ir.Color) : HExt st (st.setFace remap idx size c) := by
  unfold TextSt.setFace TextSt.setColor TextSt.setFont
  have h1 := closeTJ_hext st
  split <;> split
  · exact (h1.trans (op_hext _ _ rfl)).trans (op_hext _ _ rfl)
  · exact h1.trans (op_hext _ _ rfl)
  · exact h1.trans (op_hext _ _ rfl)
  · exact h1

/-- `st'` holds `st`'s operators, then operators showing no glyph, with no pending `TJ` item. -/
private def HFresh (st st' : TextSt) : Prop :=
  (∃ ext : Array TextOp, st'.ops = st.ops ++ ext ∧ ∀ o ∈ ext, o.spanRuns = [] ∧ o.runs = []) ∧
    st'.items = #[] ∧ st'.hyphens = st.hyphens

private theorem HFresh.trans {a b c : TextSt} (h1 : HFresh a b) (h2 : HFresh b c) : HFresh a c := by
  obtain ⟨⟨e1, he1, hs1⟩, -, hh1⟩ := h1
  obtain ⟨⟨e2, he2, hs2⟩, hi2, hh2⟩ := h2
  refine ⟨⟨e1 ++ e2, by rw [he2, he1, Array.append_assoc], ?_⟩, hi2, by rw [hh2, hh1]⟩
  intro o ho
  rcases Array.mem_append.mp ho with h | h
  · exact hs1 o h
  · exact hs2 o h

private theorem HFresh.refl (st : TextSt) (h : st.items = #[]) : HFresh st st :=
  ⟨⟨#[], by simp, by simp⟩, h, rfl⟩

private theorem closeTJ_fresh (st : TextSt) (h : st.items = #[]) : st.closeTJ = st := by
  unfold TextSt.closeTJ
  simp [h]

private theorem op_fresh (st : TextSt) (o : TextOp) (h : st.items = #[]) (hs : o.spanRuns = [])
    (hr : o.runs = []) : HFresh st (st.op o) :=
  ⟨⟨#[o], by simp [TextSt.op], by simp [hs, hr]⟩, h, rfl⟩

private theorem toPen_fresh (st : TextSt) (c : Bool) (y : Length) (h : st.items = #[]) :
    HFresh st (st.toPen c y) := by
  have hm : HFresh st (st.moveTo y) := by
    unfold TextSt.moveTo
    rw [closeTJ_fresh st h]
    exact op_fresh st _ h rfl rfl
  unfold TextSt.toPen
  split
  · dsimp only
    rw [ite_eq_right (by simp [h])]
    exact hm
  · exact hm

private theorem setFace_fresh (st : TextSt) (remap : Array Nat) (idx : Nat) (size : Length)
    (c : Ir.Color) (h : st.items = #[]) : HFresh st (st.setFace remap idx size c) := by
  unfold TextSt.setFace TextSt.setColor TextSt.setFont
  rw [closeTJ_fresh st h]
  split <;> split
  · exact (op_fresh st _ h rfl rfl).trans (op_fresh _ _ h rfl rfl)
  · exact op_fresh st _ h rfl rfl
  · exact op_fresh st _ h rfl rfl
  · exact HFresh.refl st h

/-- A run set from no pending `TJ` item leaves its glyphs as the one item pending. -/
private theorem stepRun_fresh (remap : Array Nat) (ls y : Length) (st : TextSt) (idx : Nat)
    (c : Ir.Color) (w : Length) (glyphs : Array (Nat × Char × Length)) (ss raise : Length)
    (h : st.items = #[]) (hg : glyphs.isEmpty = false) :
    ∃ ext item, (stepRun remap ls y st idx c w glyphs ss raise).ops = st.ops ++ ext ∧
      (∀ o ∈ ext, o.spanRuns = [] ∧ o.runs = []) ∧
      (stepRun remap ls y st idx c w glyphs ss raise).items = #[item] ∧
      item.runs = [glyphs.map (·.1)] ∧
      (stepRun remap ls y st idx c w glyphs ss raise).hyphens = st.hyphens := by
  unfold stepRun
  rw [ite_eq_right (by simp [hg])]
  dsimp only
  generalize (st.font != (idx : Int) || st.size != (if ss == 0 then ls else ss) || st.color != c) = ch
  have h1 := toPen_fresh st ch (y + raise) h
  have h2 : HFresh st (if ch then (st.toPen ch (y + raise)).setFace remap idx
      (if ss == 0 then ls else ss) c else st.toPen ch (y + raise)) := by
    split
    · exact h1.trans (setFace_fresh _ _ _ _ _ h1.2.1)
    · exact h1
  generalize (if ch then (st.toPen ch (y + raise)).setFace remap idx
      (if ss == 0 then ls else ss) c else st.toPen ch (y + raise)) = s2 at h2 ⊢
  obtain ⟨⟨ext, he, hq⟩, hi, hh⟩ := h2
  simp only [TextSt.pushRun, hi, he, hh, List.push_toArray, List.nil_append]
  refine ⟨ext, _, rfl, hq, rfl, ?_, ?_⟩
  · rw [runItem_runs]
    simp only [Array.mkEmpty_eq]
    rw [place_glyphs_id]
  · trivial

private theorem stepRun_hext (remap : Array Nat) (ls y : Length) (st : TextSt) (idx : Nat)
    (c : Ir.Color) (w : Length) (glyphs : Array (Nat × Char × Length)) (ss raise : Length) :
    HExt st (stepRun remap ls y st idx c w glyphs ss raise) := by
  unfold stepRun
  split
  · exact HExt.ofEq rfl rfl
  · dsimp only
    generalize (st.font != (idx : Int) || st.size != (if ss == 0 then ls else ss) || st.color != c) = ch
    have h2 : HExt st (if ch then (st.toPen ch (y + raise)).setFace remap idx
        (if ss == 0 then ls else ss) c else st.toPen ch (y + raise)) := by
      split
      · exact (toPen_hext st ch _).trans (setFace_hext _ _ _ _ _)
      · exact toPen_hext st ch _
    generalize (if ch then (st.toPen ch (y + raise)).setFace remap idx
        (if ss == 0 then ls else ss) c else st.toPen ch (y + raise)) = s2 at h2 ⊢
    exact h2.trans (HExt.ofEq rfl rfl)

private theorem TextOp.spanRunsList_eq (l : List TextOp) :
    TextOp.spanRunsList l = l.flatMap TextOp.spanRuns := by
  induction l with
  | nil => rfl
  | cons o rest ih => simp [TextOp.spanRunsList, ih]

private theorem markHyphens_append (ops ext : Array TextOp) (hs : Array Nat)
    (h : ∀ i ∈ hs, i < ops.size) : markHyphens (ops ++ ext) hs = markHyphens ops hs ++ ext := by
  apply Array.toList_inj.mp
  simp only [markHyphens_eq, Array.toList_mapIdx, Array.toList_append, List.mapIdx_append]
  congr 1
  apply mapIdx_id_of
  intro i o
  have : i + ops.size ∉ hs := fun hm => by have := h _ hm; omega
  simp [this]

/-- A line's operators so far show `acc` as generated hyphens, its hyphen places in range. -/
private def HJ (st : TextSt) (acc : List (Array Nat)) : Prop :=
  TextOp.spanRunsList (markHyphens st.ops st.hyphens).toList = acc ∧ ∀ i ∈ st.hyphens, i < st.ops.size

private theorem HJ.hext {st st' : TextSt} {acc : List (Array Nat)} (hj : HJ st acc) (he : HExt st st') :
    HJ st' acc := by
  obtain ⟨hs, hlt⟩ := hj
  obtain ⟨⟨ext, he, hq⟩, hh⟩ := he
  refine ⟨?_, ?_⟩
  · rw [he, hh, markHyphens_append _ _ _ hlt, Array.toList_append, TextOp.spanRunsList_eq,
      List.flatMap_append, ← TextOp.spanRunsList_eq, hs]
    rw [List.flatMap_eq_nil_iff.mpr (fun o ho => hq o (Array.mem_toList_iff.mp ho)), List.append_nil]
  · intro i hi
    rw [he, Array.size_append]
    have := hlt i (hh ▸ hi)
    omega

private theorem mapIdx_congr_lt {α : Type} : ∀ (l : List α) (f g : Nat → α → α),
    (∀ i < l.length, ∀ o, f i o = g i o) → l.mapIdx f = l.mapIdx g
  | [], _, _, _ => rfl
  | o :: rest, f, g, h => by
    rw [List.mapIdx_cons, List.mapIdx_cons, h 0 (by simp) o,
      mapIdx_congr_lt rest (fun i => f (i + 1)) (fun i => g (i + 1))
        (fun i hi o => h (i + 1) (by simp; omega) o)]

private theorem markHyphens_congr (ops : Array TextOp) (hs hs' : Array Nat)
    (h : ∀ i < ops.size, (i ∈ hs ↔ i ∈ hs')) : markHyphens ops hs = markHyphens ops hs' := by
  apply Array.toList_inj.mp
  simp only [markHyphens_eq, Array.toList_mapIdx]
  apply mapIdx_congr_lt
  intro i hi o
  have := h i (by simpa using hi)
  simp only [Array.contains_iff_mem]
  by_cases hm : i ∈ hs
  · simp [hm, this.mp hm]
  · have hm' : i ∉ hs' := fun h' => hm (this.mpr h')
    simp [hm, hm']

private theorem markHyphens_snoc (ops : Array TextOp) (o : TextOp) (hs : Array Nat) :
    markHyphens (ops.push o) (hs.push ops.size) =
      (markHyphens ops hs).push (.marked (.span generatedHyphen) #[o]) := by
  apply Array.toList_inj.mp
  simp only [markHyphens_eq, Array.toList_mapIdx, Array.toList_push, List.mapIdx_append,
    List.mapIdx_cons, List.mapIdx_nil, Array.contains_iff_mem, Array.mem_push]
  congr 1
  · apply mapIdx_congr_lt
    intro i hi o'
    have hne : i ≠ ops.size := by simp at hi; omega
    simp [hne]
  · simp

private theorem stepHyphen_hj (remap : Array Nat) (ls y : Length) (st : TextSt) (idx : Nat)
    (c : Ir.Color) (w : Length) (glyphs : Array (Nat × Char × Length)) (ss raise : Length)
    {acc : List (Array Nat)} (hj : HJ st acc) (hg : glyphs.isEmpty = false) :
    HJ (stepHyphen remap ls y st idx c w glyphs ss raise) (acc ++ [glyphs.map (·.1)]) := by
  have hj0 := hj.hext (closeTJ_hext st)
  have hi0 := closeTJ_items st
  unfold stepHyphen
  dsimp only
  generalize st.closeTJ = s0 at hj0 hi0 ⊢
  obtain ⟨ext, item, hops, hq, hit, hrun, hhy⟩ :=
    stepRun_fresh remap ls y s0 idx c w glyphs ss raise hi0 hg
  generalize stepRun remap ls y s0 idx c w glyphs ss raise = s1 at hops hit hhy ⊢
  have hj1 : HJ { s1 with ops := s0.ops ++ ext } acc :=
    hj0.hext ⟨⟨ext, rfl, fun o ho => (hq o ho).1⟩, hhy⟩
  have hco : s1.closeTJ.ops = (s0.ops ++ ext).push (.show #[item]) := by
    unfold TextSt.closeTJ
    rw [ite_eq_right (by simp [hit])]
    simp [hit, hops]
  have hch : s1.closeTJ.hyphens = s1.hyphens := by
    unfold TextSt.closeTJ
    split <;> rfl
  obtain ⟨hs1, hlt1⟩ := hj1
  simp only at hs1 hlt1
  refine ⟨?_, ?_⟩
  · simp only
    rw [hco, hch, Array.size_push, Nat.add_sub_cancel, markHyphens_snoc, Array.toList_push,
      TextOp.spanRunsList_eq, List.flatMap_append, ← TextOp.spanRunsList_eq, hs1]
    simp [TextOp.spanRuns, TextOp.runsList, TextOp.runs, hrun]
  · simp only
    intro i hi
    rw [hco, Array.size_push]
    rw [hch, hco, Array.size_push, Nat.add_sub_cancel, Array.mem_push] at hi
    rcases hi with hi | hi
    · have := hlt1 i hi; omega
    · omega

private theorem stepSeg_hj (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Length)
    (og : Origin) (st : TextSt) (seg : Seg) {acc : List (Array Nat)} (hj : HJ st acc) :
    HJ (stepSeg remap imgMap ls y og st seg) (acc ++ segHyphenRuns seg) := by
  cases seg with
  | run idx color link w glyphs size m decs raise ground attr =>
    simp only [stepSeg, segHyphenRuns]
    split
    · next h =>
      simp only [lineHyphen, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      exact stepHyphen_hj remap ls y st idx color w glyphs size raise hj h.2
    · simpa using hj.hext (stepRun_hext ..)
  | rule | decoration | image | gap | decoratedGap | poly =>
    simp only [segHyphenRuns, List.append_nil]
    exact hj.hext (HExt.ofEq rfl rfl)

private theorem foldl_segs_hj (remap : Array Nat) (imgMap : Array (Option Nat)) (ls y : Length)
    (og : Origin) (segs : List Seg) (st : TextSt) {acc : List (Array Nat)} (hj : HJ st acc) :
    HJ (segs.foldl (stepSeg remap imgMap ls y og) st) (acc ++ segs.flatMap segHyphenRuns) := by
  induction segs generalizing st acc with
  | nil => simpa using hj
  | cons s rest ih =>
    rw [List.foldl_cons, List.flatMap_cons, ← List.append_assoc]
    exact ih _ (stepSeg_hj remap imgMap ls y og st s hj)

private theorem lineSt_hj (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (og : Origin) (st : TextSt) (l : LineOut) :
    HJ (lineSt geom remap imgMap og st l) (l.segs.toList.flatMap segHyphenRuns) := by
  unfold lineSt
  dsimp only
  have h0 : HJ { st with ops := #[], hyphens := #[] } [] := ⟨rfl, by simp⟩
  have h1 : HJ (if l.expand != st.tz then
      { ({ st with ops := #[], hyphens := #[] } : TextSt).op (.scale (1000 + l.expand)) with tz := l.expand }
      else { st with ops := #[], hyphens := #[] }) [] := by
    split
    · exact h0.hext (op_hext _ _ rfl)
    · exact h0
  generalize (if l.expand != st.tz then
      { ({ st with ops := #[], hyphens := #[] } : TextSt).op (.scale (1000 + l.expand)) with tz := l.expand }
      else { st with ops := #[], hyphens := #[] }) = s1 at h1 ⊢
  have h2 : HJ { s1 with x := geom.bleed + l.x, pen := none } [] := h1.hext (HExt.ofEq rfl rfl)
  have h3 := foldl_segs_hj remap imgMap l.size (geom.bleed + geom.pageH - l.y) og l.segs.toList _ h2
  rw [List.nil_append, Array.foldl_toList] at h3
  exact h3.hext (closeTJ_hext _)

private theorem ContentOp.spanRunsList_eq (l : List ContentOp) :
    ContentOp.spanRunsList l = l.flatMap ContentOp.spanRuns := by
  induction l with
  | nil => rfl
  | cons o rest ih => simp [ContentOp.spanRunsList, ih]

private theorem stepLine_spanRuns (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (st : TextSt) (l : LineOut) :
    (stepLine geom remap imgMap tags st l).ops.toList.flatMap TextOp.spanRuns =
      st.ops.toList.flatMap TextOp.spanRuns ++ l.segs.toList.flatMap segHyphenRuns := by
  have hj := lineSt_hj geom remap imgMap (Origin.of tags l) st l
  obtain ⟨hs, -⟩ := hj
  rw [TextOp.spanRunsList_eq] at hs
  have hempty : (lineSt geom remap imgMap (Origin.of tags l) st l).ops.isEmpty = true →
      l.segs.toList.flatMap segHyphenRuns = [] := by
    intro he
    rw [← hs, Array.isEmpty_iff.mp he, markHyphens_eq]
    rfl
  unfold stepLine
  dsimp only
  split
  · simp [Array.toList_push, TextOp.spanRuns, TextOp.spanRunsList_eq, hs, furnitureTag]
  · split
    · rename_i he
      simp [hempty he]
    · simp [Array.toList_push, TextOp.spanRuns, TextOp.spanRunsList_eq, hs]
  · split
    · rename_i he
      simp [hempty he]
    · simp [Array.toList_push, TextOp.spanRuns, TextOp.spanRunsList_eq, hs]

private theorem foldl_lines_spanRuns (geom : Geom) (remap : Array Nat) (imgMap : Array (Option Nat))
    (tags : Array (Option String)) (ls : List LineOut) (st : TextSt) :
    (ls.foldl (stepLine geom remap imgMap tags) st).ops.toList.flatMap TextOp.spanRuns =
      st.ops.toList.flatMap TextOp.spanRuns ++ ls.flatMap fun l => l.segs.toList.flatMap segHyphenRuns := by
  induction ls generalizing st with
  | nil => simp
  | cons l rest ih =>
    rw [List.foldl_cons, ih, stepLine_spanRuns, List.flatMap_cons, List.append_assoc]

mutual

private theorem TextOp.number_spanRuns : ∀ (o : TextOp) (n : Nat),
    (TextOp.number n o).1.spanRuns = o.spanRuns
  | .scale _, _ => rfl
  | .move _ _, _ => rfl
  | .font _ _, _ => rfl
  | .color _, _ => rfl
  | .show _, _ => rfl
  | .marked (.artifact a) body, n => by
    have h := TextOp.numberList_spanRuns body.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [TextOp.number, TextOp.spanRuns, TextOp.spanRunsList_eq, h]
  | .marked (.span a) body, n => by
    have h := TextOp.numberList_spanRuns body.toList n #[]
    have hr := TextOp.numberList_runs body.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h hr
    simp [TextOp.number, TextOp.spanRuns, TextOp.spanRunsList_eq, TextOp.runsList_eq, h, hr]
  | .marked (.content s m k) body, n => by
    have h := TextOp.numberList_spanRuns body.toList (n + 1) #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [TextOp.number, TextOp.spanRuns, TextOp.spanRunsList_eq, h]

private theorem TextOp.numberList_spanRuns : ∀ (l : List TextOp) (n : Nat) (acc : Array TextOp),
    (TextOp.numberList n acc l).1.toList.flatMap TextOp.spanRuns
      = acc.toList.flatMap TextOp.spanRuns ++ l.flatMap TextOp.spanRuns
  | [], _, acc => by simp [TextOp.numberList]
  | o :: rest, n, acc => by
    rw [TextOp.numberList]
    simp [TextOp.numberList_spanRuns rest, Array.toList_push, TextOp.number_spanRuns o n]

end

mutual

private theorem ContentOp.number_spanRuns : ∀ (o : ContentOp) (n : Nat),
    (ContentOp.number n o).1.spanRuns = o.spanRuns
  | .fill _ _ _ _ _, _ => rfl
  | .paint _ _ _ _, _ => rfl
  | .shade _ _, _ => rfl
  | .outline _ _ _, _ => rfl
  | .xobject _ _ _ _, _ => rfl
  | .group m gs clips body, n => by
    have h := ContentOp.numberList_spanRuns body.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.spanRuns, ContentOp.spanRunsList_eq, h]
  | .image _ _ _ _ _, _ => rfl
  | .imageMissing _ _ _ _, _ => rfl
  | .text ops, n => by
    have h := TextOp.numberList_spanRuns ops.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.spanRuns, TextOp.spanRunsList_eq, h]
  | .marked (.artifact a) body, n => by
    have h := ContentOp.numberList_spanRuns body.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.spanRuns, ContentOp.spanRunsList_eq, h]
  | .marked (.span a) body, n => by
    have h := ContentOp.numberList_spanRuns body.toList n #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.spanRuns, ContentOp.spanRunsList_eq, h]
  | .marked (.content s m k) body, n => by
    have h := ContentOp.numberList_spanRuns body.toList (n + 1) #[]
    simp only [List.flatMap_nil, List.nil_append] at h
    simp [ContentOp.number, ContentOp.spanRuns, ContentOp.spanRunsList_eq, h]

private theorem ContentOp.numberList_spanRuns : ∀ (l : List ContentOp) (n : Nat) (acc : Array ContentOp),
    (ContentOp.numberList n acc l).1.toList.flatMap ContentOp.spanRuns
      = acc.toList.flatMap ContentOp.spanRuns ++ l.flatMap ContentOp.spanRuns
  | [], _, acc => by simp [ContentOp.numberList]
  | o :: rest, n, acc => by
    rw [ContentOp.numberList]
    simp [ContentOp.numberList_spanRuns rest, Array.toList_push, ContentOp.number_spanRuns o n]

end

mutual

private theorem figureOnly_spanRuns : ∀ (o : ContentOp), o.figureOnly = true → o.spanRuns = []
  | .paint _ _ _ _, _ => rfl
  | .shade _ _, _ => rfl
  | .outline _ _ _, _ => rfl
  | .xobject _ _ _ _, _ => rfl
  | .group _ _ _ body, h => by
    simp only [ContentOp.figureOnly] at h
    simp only [ContentOp.spanRuns]
    exact figureOnlyList_spanRuns body.toList h
  | .fill _ _ _ _ _, h => by simp [ContentOp.figureOnly] at h
  | .text _, h => by simp [ContentOp.figureOnly] at h
  | .image _ _ _ _ _, h => by simp [ContentOp.figureOnly] at h
  | .imageMissing _ _ _ _, h => by simp [ContentOp.figureOnly] at h
  | .marked _ _, h => by simp [ContentOp.figureOnly] at h

private theorem figureOnlyList_spanRuns : ∀ (l : List ContentOp), ContentOp.figureOnlyList l = true →
    ContentOp.spanRunsList l = []
  | [], _ => rfl
  | o :: rest, h => by
    simp only [ContentOp.figureOnlyList, Bool.and_eq_true] at h
    simp only [ContentOp.spanRunsList, figureOnly_spanRuns o h.1, figureOnlyList_spanRuns rest h.2,
      List.append_nil]

end

mutual

private theorem TextOp.ink_spanRuns : ∀ (o : TextOp), ∀ x ∈ o.ink, x.spanRuns = []
  | .scale _ => by simp [TextOp.ink, TextOp.spanRuns]
  | .move _ _ => by simp [TextOp.ink, TextOp.spanRuns]
  | .font _ _ => by simp [TextOp.ink, TextOp.spanRuns]
  | .color _ => by simp [TextOp.ink, TextOp.spanRuns]
  | .show _ => by simp [TextOp.ink, TextOp.spanRuns]
  | .marked _ body => by
    simp only [TextOp.ink]
    exact TextOp.inkList_spanRuns body.toList

private theorem TextOp.inkList_spanRuns : ∀ (l : List TextOp), ∀ x ∈ TextOp.inkList l, x.spanRuns = []
  | [] => by simp [TextOp.inkList]
  | o :: rest => by
    intro x hx
    simp only [TextOp.inkList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact TextOp.ink_spanRuns o x hx
    · exact TextOp.inkList_spanRuns rest x hx

end

private theorem picOp_spanRuns (o : ContentOp) (h : PicOp o) : o.spanRuns = [] := by
  rcases h with h | ⟨t, rfl, ht⟩
  · exact figureOnly_spanRuns o h
  · simp only [GfxPdf.textGroup, ContentOp.spanRuns, ContentOp.spanRunsList, TextOp.spanRunsList_eq,
      List.append_nil]
    rw [← ht]
    unfold inkText
    rw [List.toList_toArray]
    exact List.flatMap_eq_nil_iff.mpr (TextOp.inkList_spanRuns t.toList)

private theorem artifactBlock_spanRuns (k : Option ArtifactKind) (ops : Array ContentOp) :
    (artifactBlock k ops).toList.flatMap ContentOp.spanRuns = ops.toList.flatMap ContentOp.spanRuns := by
  unfold artifactBlock
  split
  · rename_i h
    simp [Array.isEmpty_iff.mp h]
  · simp [ContentOp.spanRuns, ContentOp.spanRunsList_eq]

private theorem imageOp_spanRuns (ix : GfxPdf.Request → Nat) (figs : Array (Option FigForm))
    (i : ImgOut) : (imageOp ix figs i).spanRuns = [] := by
  unfold imageOp
  split
  · simp [figOp, ContentOp.spanRuns, ContentOp.spanRunsList]
  · split <;> simp [artifact, ContentOp.spanRuns, ContentOp.spanRunsList]

/-- The hyphen the breaker sets at a line end ships under a span reading as a soft hyphen: the glyph
runs the page stream shows under such spans are exactly its body lines' line-end hyphen runs, in
order. -/
public theorem lineHyphen_generated (geom : Geom) (remap : Array Nat) (widths : Array (Array Int))
    (imgMap : Array (Option Nat)) (tags : Array (Option String)) (ix : GfxPdf.Request → Nat)
    (figs : Array (Option FigForm)) (page : PageOut) :
    spanRunsOf (contentOps geom remap widths imgMap tags ix figs page) =
      (bodyLines page).toList.flatMap fun l => l.segs.toList.flatMap segHyphenRuns := by
  have hpaths : (inkGroups geom ix (pageLabels geom remap widths imgMap tags page).text tags
      page.inks).toList.flatMap ContentOp.spanRuns = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro o ho
    obtain ⟨t, body, rfl, hb⟩ := inkGroups_shape geom ix _ tags page.inks
      (pageLabels_setter geom remap widths imgMap tags page) o (Array.mem_toList_iff.mp ho)
    simp only [ContentOp.spanRuns, ContentOp.spanRunsList_eq]
    exact List.flatMap_eq_nil_iff.mpr fun b hb' => picOp_spanRuns b (hb b (Array.mem_toList_iff.mp hb'))
  have hl := foldl_lines_spanRuns geom remap imgMap tags (bodyLines page).toList { widths }
  rw [Array.foldl_toList] at hl
  unfold contentOps spanRunsOf numberMarks
  simp only [Array.toList_append, List.flatMap_append, artifactBlock_spanRuns]
  rw [ContentOp.numberList_spanRuns]
  simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Array.toList_map, List.flatMap_map, hpaths, imageOp_spanRuns,
    ContentOp.spanRuns, TextOp.spanRunsList_eq, hl, polyOp, List.nil_append, List.append_nil]
  simp only [flatMap_nil_fun, List.nil_append, List.append_nil]

end LeanTex.Core.Pdf
