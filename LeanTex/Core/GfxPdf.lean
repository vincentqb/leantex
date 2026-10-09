module

public import LeanTex.Core.Gfx
public import LeanTex.Core.GfxAffine
public import LeanTex.Core.PdfOps

/-!
# A figure as PDF operators

`emit` lowers a figure onto typed content operators under a page
placement, and `readMarks` reads them back with PDF's own meaning — its
initial graphics state (ISO 32000-2 §8.4.1: butt caps, miter joins, miter
limit 10, solid lines, opaque), its `cm` composition, its clipping and its
transparency groups (§11.6.6). `marks_projects` is the statement that the
two meet at the figure's marks: what the PDF says is what the figure
paints, so a state the writer elides because PDF starts there is a state
the figure asked for.

The placement is an isometry, applied to coordinates exactly; a group's
transform is a `cm` whose matrix composes the placement in once, at the
first transformed group, and the identity group is no operator at all — so
a TikZ picture's operators are today's, byte for byte. A shading pattern's
matrix maps into the default space of the stream that paints (§8.7.2), so
it composes the placement and every `cm` since that stream began; the
reader reads it against that space (`RState.base`), which is what
`marks_projects` holds it to. A stamp's form is its outline and operator
alone, painted with the state its instance sets, as a Type 3 `d1` glyph is.
-/

namespace LeanTex.Core.GfxPdf

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Gfx LeanTex.Core.Pdf

/-! ## Geometry as path operators -/

/-- A segment's operator. -/
@[expose] public def segOp : Seg → PathOp
  | .line p => .lineTo p.1 p.2
  | .cubic c1 c2 p => .curveTo c1.1 c1.2 c2.1 c2.2 p.1 p.2

/-- A subpath's operators: a move to its start, its segments, a close. -/
@[expose] public def subpathOps (s : Subpath) : List PathOp :=
  .moveTo s.start.1 s.start.2 :: (s.segs.toList.map segOp ++ if s.closed then [.close] else [])

/-- A geometry's operators: a rectangle is `re`, an ellipse its four arcs,
a path its subpaths. -/
@[expose] public def geomOps : Geom → List PathOp
  | .rect x y w h => [.rect x y w h]
  | .ellipse cx cy rx ry => (Kit.ellipse cx cy rx ry).toList.flatMap subpathOps
  | .path subs => subs.toList.flatMap subpathOps

/-- An open subpath closed onto the finished ones. -/
@[expose] public def flush (done : Array Subpath) : Option Subpath → Array Subpath
  | none => done
  | some s => done.push s

/-- A segment appended to the open subpath; with none open, PDF starts
from the origin. -/
@[expose] public def extend (cur : Option Subpath) (sg : Seg) : Subpath :=
  match cur with
  | some s => { s with segs := s.segs.push sg }
  | none => { start := (0, 0), segs := #[sg], closed := false }

/-- Path operators read back as subpaths (§8.5.2): `m` opens one, `l` and
`c` extend it, `h` closes it, `re` is a closed rectangle of its own. -/
@[expose] public def subsOf (done : Array Subpath) (cur : Option Subpath) :
    List PathOp → Array Subpath
  | [] => flush done cur
  | .moveTo x y :: rest =>
    subsOf (flush done cur) (some { start := (x, y), segs := #[], closed := false }) rest
  | .lineTo x y :: rest => subsOf done (some (extend cur (.line (x, y)))) rest
  | .curveTo a b c d e f :: rest => subsOf done (some (extend cur (.cubic (a, b) (c, d) (e, f)))) rest
  | .close :: rest => subsOf done (cur.map fun s => { s with closed := true }) rest
  | .rect x y w h :: rest => subsOf ((flush done cur).push (Kit.rectPath x y w h)) none rest

/-- The geometry a path's operators draw: one `re` is a rectangle, anything
else its subpaths. -/
@[expose] public def geomOf (ops : List PathOp) : Geom :=
  match ops with
  | [.rect x y w h] => .rect x y w h
  | [] => .path #[]
  | o :: rest => .path (subsOf #[] none (o :: rest))

/-! ## Emission -/

/-- What the writer interns for a figure, keyed by content. -/
public inductive Request where
  | extG (fill stroke : Alpha)
  | pattern (g : Gradient)
  | form (kind : FormKind) (body : Array ContentOp)
  | raster (k : Nat)
  deriving Repr, BEq, Inhabited

/-- Where emission stands: whether the coordinates it writes are still
carried by the placement exactly (`iso`, at the root and under identity
groups), and the map from the current frame's user space to the stream's
default space, which a pattern's matrix composes (§8.7.2). -/
public structure Frame where
  iso : Option Iso
  stream : Affine
  deriving Repr, Inhabited

/-- A frame's transform as the `cm` that enters it: the placement composed
in where the coordinates were still carried by it. -/
@[expose] public def Frame.lift (fr : Frame) (xf : Affine) : Affine :=
  match fr.iso with
  | some t => t.toAffine.compose xf
  | none => xf

/-- The frame after a `cm`, if one was written. -/
@[expose] public def Frame.enter (fr : Frame) : Option Affine → Frame
  | none => fr
  | some m => { iso := none, stream := fr.stream.compose m }

/-- A geometry's operators in the frame: normalized, and carried by the
placement when it still applies. -/
@[expose] public def Frame.geomOps (fr : Frame) (g : Geom) : List PathOp :=
  match fr.iso with
  | some t => GfxPdf.geomOps (g.normal.mapIso t)
  | none => GfxPdf.geomOps g.normal

/-- A paint as PDF paints it: a device colour, or a shading pattern whose
matrix maps the gradient's frame to the stream's default space — the
gradient's own frame map carried through the frame and composed onto the
stream's (§8.7.2). -/
@[expose] public def pdfPaint (ix : Request → Nat) (fr : Frame) : Paint → PdfPaint
  | .solid c => .solid c
  | .gradient g =>
    let g' := g.withXf (fr.stream.compose (fr.lift g.xf))
    .pattern (ix (.pattern g')) g'

@[expose] public def capOpt : Cap → Option Cap
  | .butt => none
  | .round => some .round
  | .square => some .square

@[expose] public def joinOpt : Join → Option Join
  | .miter => none
  | .round => some .round
  | .bevel => some .bevel

/-- PDF's initial miter limit (§8.4.1, Table 51): never spelled. -/
@[expose] public def pdfMiter : Rat := 10

/-- The colour and line state in force (§8.4.1, Table 51), in the figure
frame: what an operator that states none of its own — a stamp form's
outline — paints with, and what a stroke leaves unstated reads as. -/
public structure Pen where
  fill : Paint
  stroke : Paint
  width : Sp
  cap : Cap
  join : Join
  miter : Rat
  dash : Array Sp
  phase : Sp
  deriving Repr, BEq, Inhabited

/-- PDF's initial state: black, a line one unit wide, butt caps, miter
joins at limit 10, solid. -/
@[expose] public def Pen.initial : Pen :=
  { fill := .solid { r := 0, g := 0, b := 0 }, stroke := .solid { r := 0, g := 0, b := 0 }
    width := 65536, cap := .butt, join := .miter, miter := pdfMiter, dash := #[], phase := 0 }

/-- How far a stamp instance's stroke reaches past the outline, in the
form's space — the margin the form's box needs — read as PDF reads the
instance's stroke, its unstated parameters the initial ones. -/
@[expose] public def stampReach : Option PaintStroke → Sp
  | some s =>
    let k : Stroke :=
      { paint := Pen.initial.stroke
        width := s.width
        cap := s.cap.getD Pen.initial.cap
        join := s.join.getD Pen.initial.join
        miterLimit := s.miter.getD Pen.initial.miter
        dash := #[]
        phase := 0
        alpha := Alpha.opaque }
    k.reach
  | none => 0


@[expose] public def miterOpt (r : Rat) : Option Rat := if r = pdfMiter then none else some r

@[expose] public def dashOpt (d : Array Sp) (p : Sp) : Option (Array Sp × Sp) :=
  if d = #[] ∧ p = 0 then none else some (d, p)

@[expose] public def paintFill (ix : Request → Nat) (fr : Frame) (f : Fill) : PaintFill :=
  { paint := pdfPaint ix fr f.paint
    evenOdd := match f.rule with
      | .evenOdd => true
      | .nonzero => false }

@[expose] public def paintStroke (ix : Request → Nat) (fr : Frame) (s : Stroke) : PaintStroke :=
  { paint := pdfPaint ix fr s.paint, width := s.width, cap := capOpt s.cap
    join := joinOpt s.join, miter := miterOpt s.miterLimit, dash := dashOpt s.dash s.phase }

/-- The ExtGState a pair of paint alphas needs: none when both are opaque. -/
@[expose] public def extOf (ix : Request → Nat) (fa sa : Alpha) : Option ExtG :=
  if fa = Alpha.opaque ∧ sa = Alpha.opaque then none
  else some { res := ix (.extG fa sa), fill := fa, stroke := sa }

/-- A draw's one operator. -/
@[expose] public def drawOp (ix : Request → Nat) (fr : Frame) (g : Geom) (fl : Option Fill)
    (st : Option Stroke) : ContentOp :=
  .paint (fl.map (paintFill ix fr)) (st.map (paintStroke ix fr))
    (extOf ix ((fl.map (·.alpha)).getD Alpha.opaque) ((st.map (·.alpha)).getD Alpha.opaque))
    (fr.geomOps g).toArray

/-- Whether a group changes nothing: identity frame, no clip, opaque. Its
kids are written inline. -/
@[expose] public def plainGroup (xf : Affine) (clips : Array Clip) (alpha : Alpha) : Prop :=
  xf = Affine.unit ∧ clips = #[] ∧ alpha = Alpha.opaque

public instance (xf : Affine) (clips : Array Clip) (alpha : Alpha) :
    Decidable (plainGroup xf clips alpha) := by
  unfold plainGroup
  infer_instance

/-- A group's `cm`, if it has a transform to write. -/
@[expose] public def groupCm (fr : Frame) (xf : Affine) : Option Affine :=
  if xf = Affine.unit then none else some (fr.lift xf)

/-- A group's clips as clipping paths in its child frame. -/
@[expose] public def clipOpsOf (fr : Frame) (clips : Array Clip) : Array (Array PathOp × Rule) :=
  clips.map fun c => ((fr.geomOps c.geom).toArray, c.rule)

/-- A form's frame: its own coordinates, its default space — where a
symbol's body stands. -/
@[expose] public def symFrame : Frame := { iso := none, stream := Affine.unit }

/-- Whether a stamp's paint can cross into its form as the state its
instance sets: a device colour only. A pattern never crosses a form
boundary — viewers read an inherited pattern's matrix against different
streams' default spaces (MuPDF the one that set it, Poppler the one that
paints) — so a stamp painted with a gradient paints inline instead. -/
@[expose] public def inheritable : Paint → Bool
  | .solid _ => true
  | .gradient _ => false

/-- A stamp's form body: its outline and the operator its paints select,
no state of its own. -/
@[expose] public def outlineBody (subs : Array Subpath) (fl : Option Fill) (st : Option Stroke) :
    Array ContentOp :=
  #[.outline (fl.map (·.rule)) st.isSome (geomOps (.path subs)).toArray]

mutual

-- conserves: none — an emitter: what it keeps is `marks_projects`.
/-- One node's operators. A `use` paints its symbol's form, whose body
`bodyOps` already holds; a label is set by `labelOps`. -/
@[expose] public def emitOne {L : Type} (ix : Request → Nat)
    (labelOps : Frame → L → Array ContentOp) (outlines : Array (Array Subpath))
    (bodyOps : Array (Array ContentOp)) (fr : Frame) (acc : Array ContentOp) :
    Node L → Array ContentOp
  | .draw g fl st => acc.push (drawOp ix fr g fl st)
  | .group xf clips alpha kids =>
    if plainGroup xf clips alpha then
      emitList ix labelOps outlines bodyOps fr acc kids.toList
    else
      let m := groupCm fr xf
      let fr' := fr.enter m
      let clipOps := clipOpsOf fr' clips
      if alpha = Alpha.opaque then
        acc.push (.group m none clipOps (emitList ix labelOps outlines bodyOps fr' #[] kids.toList))
      else
        let body := emitList ix labelOps outlines bodyOps { fr' with stream := Affine.unit } #[]
          kids.toList
        acc.push (.group m (some { res := ix (.extG alpha alpha), fill := alpha, stroke := alpha })
          clipOps #[.xobject none (ix (.form .group body)) .group body])
  | .use k xf =>
    match bodyOps[k]? with
    | some body => acc.push (.xobject (some (fr.lift xf)) (ix (.form .symbol body)) .symbol body)
    | none => acc
  | .stamp o xf fl st =>
    let m := fr.lift xf
    let subs := outlines[o]?.getD #[]
    if fl.all (inheritable ·.paint) && st.all (inheritable ·.paint) then
      let body := outlineBody subs fl st
      let ps := st.map (paintStroke ix fr)
      acc.push (.xobject (some m) (ix (.form (.stamp (stampReach ps)) body))
        (.stamp (fl.map fun f => pdfPaint ix fr f.paint) ps
          (extOf ix ((fl.map (·.alpha)).getD Alpha.opaque) ((st.map (·.alpha)).getD Alpha.opaque)))
        body)
    else
      acc.push (.group (some m) none #[] #[drawOp ix (fr.enter (some m)) (.path subs) fl st])
  | .image k xf => acc.push (.xobject (some (fr.lift xf)) (ix (.raster k)) (.raster k) #[])
  | .label l => acc ++ (labelOps fr l)
  | .words _ => acc

@[expose] public def emitList {L : Type} (ix : Request → Nat)
    (labelOps : Frame → L → Array ContentOp) (outlines : Array (Array Subpath))
    (bodyOps : Array (Array ContentOp)) (fr : Frame) (acc : Array ContentOp) :
    List (Node L) → Array ContentOp
  | [] => acc
  | n :: rest =>
    emitList ix labelOps outlines bodyOps fr (emitOne ix labelOps outlines bodyOps fr acc n) rest

end


/-- The forms' bodies, one per symbol: each expanded body (`Figure.bodies`)
written in its own frame. -/
@[expose] public def bodyOpsOf {L : Type} (ix : Request → Nat)
    (labelOps : Frame → L → Array ContentOp) (fig : Figure L) : Array (Array ContentOp) :=
  fig.bodies.map fun b => emitList ix labelOps fig.outlines #[] symFrame #[] b.toList

/-- **A figure as PDF operators** under the placement `place` (figure
coordinates to the page's PDF space). -/
@[expose] public def emit {L : Type} (ix : Request → Nat) (labelOps : Frame → L → Array ContentOp)
    (place : Iso) (fig : Figure L) : Array ContentOp :=
  emitList ix labelOps fig.outlines (bodyOpsOf ix labelOps fig)
    { iso := some place, stream := Affine.unit } #[] fig.nodes.toList

/-! ## Reading back -/

/-- What a reader of the operators carries: the placement to undo while the
coordinates are still placed (`placed`), the figure-frame matrix of the
current user space once a `cm` was read, the figure-frame matrix of the
current stream's default space (`base`, what a pattern's matrix maps
into), the clips and group alphas in force, the constant alphas an
ExtGState set, and the colour and line state in force. -/
public structure RState where
  place : Iso
  placed : Bool
  ctm : Affine
  base : Affine
  clips : Array (Affine × Clip)
  alphas : Array Alpha
  ca : Alpha
  cA : Alpha
  pen : Pen
  deriving Repr, Inhabited

/-- The figure frame of the coordinates being read. -/
@[expose] public def RState.frameCtm (rs : RState) : Affine :=
  if rs.placed then Affine.unit else rs.ctm

/-- The map from the current user space to the figure frame: the placement
undone while the coordinates are placed, else the `cm`s read. -/
@[expose] public def RState.userCtm (rs : RState) : Affine :=
  if rs.placed then rs.place.inv.toAffine else rs.ctm

/-- A path's geometry in the figure frame. -/
@[expose] public def RState.geom (rs : RState) (segs : Array PathOp) : Geom :=
  if rs.placed then (geomOf segs.toList).mapIso rs.place.inv else geomOf segs.toList

/-- The state after a `cm`, if one was read. -/
@[expose] public def RState.cm (rs : RState) : Option Affine → RState
  | none => rs
  | some m => { rs with placed := false, ctm := rs.userCtm.compose m }

/-- A paint as the stream says it, in the figure frame: a pattern's matrix
read against the stream's default space. -/
@[expose] public def readPaint (rs : RState) : PdfPaint → Paint
  | .solid c => .solid c
  | .pattern _ g => .gradient (g.withXf (rs.base.compose g.xf))

@[expose] public def readFill (rs : RState) (gs : Option ExtG) (f : PaintFill) : Fill :=
  { paint := readPaint rs f.paint, rule := if f.evenOdd then .evenOdd else .nonzero
    alpha := (gs.map (·.fill)).getD rs.ca }

/-- A stroke as the stream says it: what it leaves unstated is the state in
force. -/
@[expose] public def readStroke (rs : RState) (gs : Option ExtG) (s : PaintStroke) : Stroke :=
  { paint := readPaint rs s.paint, width := s.width, cap := s.cap.getD rs.pen.cap
    join := s.join.getD rs.pen.join, miterLimit := s.miter.getD rs.pen.miter
    dash := (s.dash.map (·.1)).getD rs.pen.dash, phase := (s.dash.map (·.2)).getD rs.pen.phase
    alpha := (gs.map (·.stroke)).getD rs.cA }

/-- The state a group's body is read in: its `cm`, its clips in the child
frame, the alphas its ExtGState sets. -/
@[expose] public def RState.enterGroup (rs : RState) (m : Option Affine) (gs : Option ExtG)
    (clips : Array (Array PathOp × Rule)) : RState :=
  let rs1 := rs.cm m
  { rs1 with
    clips := rs1.clips ++ clips.map fun c => (rs1.frameCtm, { geom := rs1.geom c.1, rule := c.2 })
    ca := (gs.map (·.fill)).getD rs1.ca
    cA := (gs.map (·.stroke)).getD rs1.cA }

/-- The state a form's stream is read in (§8.10.1): the state in force,
its default space the user space at its `Do`. -/
@[expose] public def RState.enterForm (rs : RState) : RState := { rs with base := rs.userCtm }

/-- The state a transparency group's form is read in (§11.6.6): a form's,
and the alpha in force composites the group as a whole, so inside it alpha
starts opaque. -/
@[expose] public def RState.enterTransparency (rs : RState) : RState :=
  { rs.enterForm with alphas := rs.alphas.push rs.ca, ca := Alpha.opaque, cA := Alpha.opaque }

/-- The state a stamp's instance sets before its `Do`: its fill colour, its
stroke's colour and the parameters it states, its alphas — each paint read
where the instance sets it. -/
@[expose] public def RState.setPen (rs : RState) (fp : Option PdfPaint) (sp : Option PaintStroke)
    (gs : Option ExtG) : RState :=
  { rs with
    ca := (gs.map (·.fill)).getD rs.ca
    cA := (gs.map (·.stroke)).getD rs.cA
    pen :=
      { fill := (fp.map (readPaint rs)).getD rs.pen.fill
        stroke := (sp.map fun s => readPaint rs s.paint).getD rs.pen.stroke
        width := (sp.map (·.width)).getD rs.pen.width
        cap := (sp.bind (·.cap)).getD rs.pen.cap
        join := (sp.bind (·.join)).getD rs.pen.join
        miter := (sp.bind (·.miter)).getD rs.pen.miter
        dash := ((sp.bind (·.dash)).map (·.1)).getD rs.pen.dash
        phase := ((sp.bind (·.dash)).map (·.2)).getD rs.pen.phase } }

/-- An outline painted with the state in force. -/
@[expose] public def RState.outlineMark (rs : RState) (fl : Option Rule) (st : Bool)
    (segs : Array PathOp) : Mark :=
  .paint rs.frameCtm (rs.geom segs)
    (fl.map fun r => { paint := rs.pen.fill, rule := r, alpha := rs.ca })
    (if st then
      some { paint := rs.pen.stroke, width := rs.pen.width, cap := rs.pen.cap, join := rs.pen.join
             miterLimit := rs.pen.miter, dash := rs.pen.dash, phase := rs.pen.phase, alpha := rs.cA }
     else none)
    rs.clips rs.alphas

mutual

-- conserves: none — a reader: `marks_projects` states what it reads.
/-- One operator's marks, read with PDF's meaning. A page fill reads as the
rectangle it fills; text, page images and placeholders are no figure ink;
marked content reads through. -/
@[expose] public def readOne (rs : RState) (acc : Array Mark) : ContentOp → Array Mark
  | .paint fl st gs segs =>
    acc.push (.paint rs.frameCtm (rs.geom segs) (fl.map (readFill rs gs)) (st.map (readStroke rs gs))
      rs.clips rs.alphas)
  | .group m gs clips body => readList (rs.enterGroup m gs clips) acc body.toList
  | .xobject m _ kind body =>
    match kind with
    | .symbol => readList (rs.cm m).enterForm acc body.toList
    | .group => readList (rs.cm m).enterTransparency acc body.toList
    | .stamp fp sp gs => readList ((rs.setPen fp sp gs).cm m).enterForm acc body.toList
    | .raster k => acc.push (.raster (rs.cm m).frameCtm k (rs.cm m).clips (rs.cm m).alphas)
  | .shade _ g => acc.push (.shading (g.withXf rs.userCtm) rs.clips rs.alphas)
  | .outline fl st segs => acc.push (rs.outlineMark fl st segs)
  | .fill c x y w h =>
    acc.push (.paint rs.frameCtm (rs.geom #[.rect x y w h])
      (some { paint := .solid c, rule := .nonzero, alpha := rs.ca }) none rs.clips rs.alphas)
  | .text _ => acc
  | .image _ _ _ _ _ => acc
  | .imageMissing _ _ _ _ => acc
  | .marked _ body => readList rs acc body.toList

@[expose] public def readList (rs : RState) (acc : Array Mark) : List ContentOp → Array Mark
  | [] => acc
  | o :: rest => readList rs (readOne rs acc o) rest

end

/-- The reader at the page: coordinates placed, the page's default space
the placement's image, nothing clipped, opaque, PDF's initial state. -/
@[expose] public def RState.root (place : Iso) : RState :=
  { place := place, placed := true, ctm := Affine.unit, base := place.inv.toAffine, clips := #[]
    alphas := #[], ca := Alpha.opaque, cA := Alpha.opaque, pen := Pen.initial }

/-- **What a figure's operators paint**, read with PDF's meaning. -/
@[expose] public def readMarks (place : Iso) (ops : Array ContentOp) : Array Mark :=
  readList (RState.root place) #[] ops.toList

/-! ## The reading is the figure's -/

private theorem subsOf_segs (done : Array Subpath) (st : Pt) (acc : Array Seg) (c : Bool)
    (segs : List Seg) (tail : List PathOp) :
    subsOf done (some ⟨st, acc, c⟩) (segs.map segOp ++ tail) =
      subsOf done (some ⟨st, acc ++ segs.toArray, c⟩) tail := by
  induction segs generalizing acc with
  | nil => simp
  | cons sg rest ih =>
    cases sg with
    | line p =>
      simp only [List.map_cons, List.cons_append, segOp, subsOf, extend]
      rw [ih]
      simp
    | cubic c1 c2 p =>
      simp only [List.map_cons, List.cons_append, segOp, subsOf, extend]
      rw [ih]
      simp

private theorem subsOf_flatMap (subs : List Subpath) (done : Array Subpath)
    (cur : Option Subpath) :
    subsOf done cur (subs.flatMap subpathOps) = flush done cur ++ subs.toArray := by
  induction subs generalizing done cur with
  | nil => simp [subsOf]
  | cons s rest ih =>
    obtain ⟨st, segs, cl⟩ := s
    simp only [List.flatMap_cons, subpathOps, List.cons_append, List.append_assoc, subsOf]
    rw [subsOf_segs]
    cases cl
    · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
      rw [ih]
      simp [flush]
    · simp only [↓reduceIte, List.cons_append, List.nil_append, subsOf, Option.map_some]
      rw [ih]
      simp [flush]

/-- A path's operators read back to it (`_id`). -/
private theorem geomOf_path_id (subs : Array Subpath) :
    geomOf (geomOps (.path subs)) = .path subs := by
  rcases subs with ⟨l⟩
  cases l with
  | nil => rfl
  | cons s rest =>
    have key : subsOf #[] none ((s :: rest).flatMap subpathOps) = ⟨s :: rest⟩ := by
      rw [subsOf_flatMap]; simp [flush]
    have ht : (s :: rest).flatMap subpathOps =
        .moveTo s.start.1 s.start.2 ::
          ((s.segs.toList.map segOp ++ if s.closed then [.close] else []) ++
            rest.flatMap subpathOps) := by
      simp [subpathOps]
    show geomOf ((s :: rest).flatMap subpathOps) = _
    rw [ht]
    simp only [geomOf]
    rw [← ht, key]

/-- **What the operators of a normalized geometry draw is that geometry**
(`_id`): one `re` is its rectangle, moves and segments their subpaths. -/
public theorem geomOf_geomOps_id (g : Geom) : geomOf (geomOps g.normal) = g.normal := by
  cases g with
  | rect x y w h => rfl
  | ellipse cx cy rx ry => exact geomOf_path_id _
  | path subs => exact geomOf_path_id subs

/-- The same through the placement: a placed normalized geometry reads back
placed. -/
private theorem geomOf_geomOps_mapIso_id (t : Iso) (g : Geom) :
    geomOf (geomOps (g.normal.mapIso t)) = g.normal.mapIso t := by
  cases g with
  | rect x y w h => rfl
  | ellipse cx cy rx ry => exact geomOf_path_id _
  | path subs => exact geomOf_path_id _

private theorem readList_append (rs : RState) (acc : Array Mark) (a b : List ContentOp) :
    readList rs acc (a ++ b) = readList rs (readList rs acc a) b := by
  induction a generalizing acc with
  | nil => rfl
  | cons o rest ih => simp [readList, ih]

mutual

private theorem emitOne_acc {L : Type} (ix : Request → Nat) (labelOps : Frame → L → Array ContentOp)
    (outlines : Array (Array Subpath)) (bodyOps : Array (Array ContentOp)) (fr : Frame)
    (acc : Array ContentOp) (n : Node L) :
    emitOne ix labelOps outlines bodyOps fr acc n =
      acc ++ emitOne ix labelOps outlines bodyOps fr #[] n := by
  cases n with
  | draw g fl st => simp [emitOne]
  | group xf clips alpha kids =>
    simp only [emitOne]
    split
    · exact emitList_acc ix labelOps outlines bodyOps fr acc kids.toList
    · split <;> simp
  | use k xf =>
    simp only [emitOne]
    split <;> simp
  | stamp o xf fl st =>
    simp only [emitOne]
    split <;> simp
  | image k xf => simp [emitOne]
  | label l => simp [emitOne]
  | words w => simp [emitOne]

private theorem emitList_acc {L : Type} (ix : Request → Nat) (labelOps : Frame → L → Array ContentOp)
    (outlines : Array (Array Subpath)) (bodyOps : Array (Array ContentOp)) (fr : Frame)
    (acc : Array ContentOp) (xs : List (Node L)) :
    emitList ix labelOps outlines bodyOps fr acc xs =
      acc ++ emitList ix labelOps outlines bodyOps fr #[] xs := by
  match xs with
  | [] => simp [emitList]
  | n :: rest =>
    simp only [emitList]
    rw [emitList_acc ix labelOps outlines bodyOps fr _ rest,
      emitList_acc ix labelOps outlines bodyOps fr (emitOne ix labelOps outlines bodyOps fr #[] n) rest,
      emitOne_acc ix labelOps outlines bodyOps fr acc n, Array.append_assoc]

end


/-- The model's reading context, the emitter's frame and the PDF reader's
state, at one point of the tree: the coordinates are placed on both sides
or on neither, the frames agree, the stream's default space composed with
the frame's stream map is the user space, the clips and group alphas agree,
no ExtGState is in force, and the state in force is PDF's initial one. -/
private structure Agrees (place : Iso) (cx : Ctx) (fr : Frame) (rs : RState) : Prop where
  hplace : rs.place = place
  hiso : fr.iso = if rs.placed then some place else none
  hctm : rs.frameCtm = cx.ctm
  hbase : rs.base.compose fr.stream = rs.userCtm
  hclips : rs.clips = cx.clips
  halphas : rs.alphas = cx.alphas
  hca : rs.ca = Alpha.opaque
  hcA : rs.cA = Alpha.opaque
  hpen : rs.pen = Pen.initial

/-- Where the frames agree on placement, a geometry's operators read back to
the geometry, normalized. -/
private theorem geom_agree (place : Iso) (fr : Frame) (rs : RState) (hp : rs.place = place)
    (hi : fr.iso = if rs.placed then some place else none) (g : Geom) :
    rs.geom (fr.geomOps g).toArray = g.normal := by
  cases hpl : rs.placed
  · simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hi
    simp only [RState.geom, hpl, Frame.geomOps, hi, Bool.false_eq_true, ↓reduceIte,
      geomOf_geomOps_id]
  · simp only [hpl, ↓reduceIte] at hi
    simp only [RState.geom, hpl, Frame.geomOps, hi, ↓reduceIte, geomOf_geomOps_mapIso_id, hp,
      Geom.mapIso_inv_id]

/-- A read `cm` composes onto the user space's frame. -/
private theorem cm_some_frameCtm (rs : RState) (m : Affine) :
    (rs.cm (some m)).frameCtm = rs.userCtm.compose m := rfl

private theorem cm_some_userCtm (rs : RState) (m : Affine) :
    (rs.cm (some m)).userCtm = rs.userCtm.compose m := rfl

/-- A `cm` lifted from the frame enters the model's frame: the placement it
composes in is undone by the reader's inverse, exactly. -/
private theorem cm_lift_frameCtm (place : Iso) (cx : Ctx) (fr : Frame) (rs : RState)
    (h : Agrees place cx fr rs) (xf : Affine) :
    (rs.cm (some (fr.lift xf))).frameCtm = cx.ctm.compose xf := by
  have hc := h.hctm
  rw [cm_some_frameCtm]
  cases hpl : rs.placed
  · have hi := h.hiso
    simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hi
    simp only [RState.frameCtm, hpl, Bool.false_eq_true, ↓reduceIte] at hc
    simp only [RState.userCtm, hpl, Bool.false_eq_true, ↓reduceIte, Frame.lift, hi, hc]
  · have hi := h.hiso
    simp only [hpl, ↓reduceIte] at hi
    simp only [RState.frameCtm, hpl, ↓reduceIte] at hc
    simp only [RState.userCtm, hpl, ↓reduceIte, Frame.lift, hi, h.hplace, ← hc]
    rw [← Affine.compose_assoc_exact, Iso.inv_compose_unit_id, (Affine.compose_unit_id xf).2]

/-- A paint as the emitter spells it reads back as the paint under the
model's frame: the pattern's matrix, read against the stream's default
space, carries the gradient's own frame map to the figure's. -/
private theorem readPaint_pdfPaint (ix : Request → Nat) (place : Iso) (cx : Ctx) (fr : Frame)
    (rs : RState) (h : Agrees place cx fr rs) (p : Paint) :
    readPaint rs (pdfPaint ix fr p) = p.under cx.ctm := by
  cases p with
  | solid c => rfl
  | gradient g =>
    simp only [pdfPaint, readPaint, Paint.under, Gradient.withXf_withXf, Gradient.xf_withXf]
    rw [← Affine.compose_assoc_exact, h.hbase, ← cm_some_frameCtm,
      cm_lift_frameCtm place cx fr rs h]

private theorem extOf_fill (ix : Request → Nat) (fa sa : Alpha) (ca : Alpha) (h : ca = Alpha.opaque) :
    ((extOf ix fa sa).map (·.fill)).getD ca = fa := by
  unfold extOf
  split
  · next hh => simp [h, hh.1]
  · rfl

private theorem extOf_stroke (ix : Request → Nat) (fa sa : Alpha) (ca : Alpha) (h : ca = Alpha.opaque) :
    ((extOf ix fa sa).map (·.stroke)).getD ca = sa := by
  unfold extOf
  split
  · next hh => simp [h, hh.2]
  · rfl

private theorem readFill_paintFill (ix : Request → Nat) (place : Iso) (cx : Ctx) (fr : Frame)
    (rs : RState) (h : Agrees place cx fr rs) (f : Fill) (sa : Alpha) :
    readFill rs (extOf ix f.alpha sa) (paintFill ix fr f) = f.under cx.ctm := by
  obtain ⟨p, r, a⟩ := f
  simp only [readFill, paintFill, readPaint_pdfPaint ix place cx fr rs h,
    extOf_fill ix a sa rs.ca h.hca, Fill.under]
  cases r <;> rfl

/-- What PDF starts with and a stroke leaves unstated: its cap, join, miter
limit and dash read back as the stroke's. -/
private theorem stroke_defaults (cap : Cap) (join : Join) (ml : Rat) (dash : Array Sp) (ph : Sp) :
    (capOpt cap).getD Pen.initial.cap = cap ∧ (joinOpt join).getD Pen.initial.join = join ∧
      (miterOpt ml).getD Pen.initial.miter = ml ∧
      ((dashOpt dash ph).map (·.1)).getD Pen.initial.dash = dash ∧
      ((dashOpt dash ph).map (·.2)).getD Pen.initial.phase = ph := by
  refine ⟨by cases cap <;> rfl, by cases join <;> rfl, ?_, ?_⟩
  · unfold miterOpt; split
    · next hh => exact hh.symm
    · rfl
  · unfold dashOpt; split
    · next hh => exact ⟨hh.1.symm, hh.2.symm⟩
    · exact ⟨rfl, rfl⟩

private theorem readStroke_paintStroke (ix : Request → Nat) (place : Iso) (cx : Ctx) (fr : Frame)
    (rs : RState) (h : Agrees place cx fr rs) (st : Stroke) (fa : Alpha) :
    readStroke rs (extOf ix fa st.alpha) (paintStroke ix fr st) = st.under cx.ctm := by
  obtain ⟨p, w, cap, join, ml, dash, ph, a⟩ := st
  obtain ⟨hc, hj, hm, hd, hp⟩ := stroke_defaults cap join ml dash ph
  simp only [readStroke, paintStroke, readPaint_pdfPaint ix place cx fr rs h,
    extOf_stroke ix fa a rs.cA h.hcA, h.hpen, hc, hj, hm, hd, hp, Stroke.under]

/-- A draw reads back as its mark. -/
private theorem read_draw (ix : Request → Nat) (place : Iso) (cx : Ctx) (fr : Frame) (rs : RState)
    (h : Agrees place cx fr rs) (acc : Array Mark) (g : Geom) (fl : Option Fill)
    (st : Option Stroke) :
    readOne rs acc (drawOp ix fr g fl st) =
      acc.push (.paint cx.ctm g.normal (fl.map (Fill.under cx.ctm)) (st.map (Stroke.under cx.ctm))
        cx.clips cx.alphas) := by
  simp only [drawOp, readOne, h.hctm, h.hclips, h.halphas, geom_agree place fr rs h.hplace h.hiso g]
  congr 2
  · cases fl with
    | none => rfl
    | some f =>
      simp only [Option.map_some]
      exact congrArg some (readFill_paintFill ix place cx fr rs h f _)
  · cases st with
    | none => rfl
    | some s =>
      simp only [Option.map_some]
      exact congrArg some (readStroke_paintStroke ix place cx fr rs h s _)

/-- A group's `cm`, written or not, enters the model's frame. -/
private theorem cm_group_frameCtm (place : Iso) (cx : Ctx) (fr : Frame) (rs : RState)
    (h : Agrees place cx fr rs) (xf : Affine) :
    (rs.cm (groupCm fr xf)).frameCtm = cx.ctm.compose xf := by
  unfold groupCm
  split
  · next hx => simp only [RState.cm, h.hctm, hx, (Affine.compose_unit_id cx.ctm).1]
  · exact cm_lift_frameCtm place cx fr rs h xf

private theorem enter_alphas (cx : Ctx) (xf : Affine) (clips : Array Clip) :
    (cx.enter xf clips Alpha.opaque).alphas = cx.alphas := by
  simp [Ctx.enter]

private theorem cm_place (rs : RState) (m : Option Affine) : (rs.cm m).place = rs.place := by
  cases m <;> rfl

private theorem cm_iso (place : Iso) (fr : Frame) (rs : RState)
    (hi : fr.iso = if rs.placed then some place else none) (m : Option Affine) :
    (fr.enter m).iso = if (rs.cm m).placed then some place else none := by
  cases m with
  | none => exact hi
  | some _ => rfl

private theorem cm_keeps (rs : RState) (m : Option Affine) :
    (rs.cm m).clips = rs.clips ∧ (rs.cm m).alphas = rs.alphas ∧ (rs.cm m).ca = rs.ca ∧
      (rs.cm m).cA = rs.cA ∧ (rs.cm m).base = rs.base ∧ (rs.cm m).pen = rs.pen := by
  cases m <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A `cm`, written or not, keeps the stream's default space composed with
the frame's stream map equal to the user space. -/
private theorem cm_base (fr : Frame) (rs : RState) (hb : rs.base.compose fr.stream = rs.userCtm)
    (m : Option Affine) : (rs.cm m).base.compose (fr.enter m).stream = (rs.cm m).userCtm := by
  cases m with
  | none => exact hb
  | some mm =>
    show rs.base.compose (fr.stream.compose mm) = rs.userCtm.compose mm
    rw [← Affine.compose_assoc_exact, hb]

/-- A form's stream starts at its own default space. -/
private theorem enterForm_base (rs : RState) :
    rs.enterForm.base.compose symFrame.stream = rs.enterForm.userCtm :=
  (Affine.compose_unit_id _).1

/-- The clips a group's operators declare read back as the model's: each in
the child frame, its geometry normalized. -/
private theorem clips_agree (place : Iso) (cx : Ctx) (fr : Frame) (rs : RState)
    (h : Agrees place cx fr rs) (xf : Affine) (m : Option Affine)
    (hm : (rs.cm m).frameCtm = cx.ctm.compose xf) (clips : Array Clip) :
    (clipOpsOf (fr.enter m) clips).map
        (fun c => ((rs.cm m).frameCtm, ({ geom := (rs.cm m).geom c.1, rule := c.2 } : Clip))) =
      clips.map fun c => (cx.ctm.compose xf, { c with geom := c.geom.normal }) := by
  simp only [clipOpsOf, Array.map_map]
  apply Array.map_congr_left
  intro c _
  simp only [Function.comp, hm,
    geom_agree place (fr.enter m) (rs.cm m) (by rw [cm_place, h.hplace]) (cm_iso place fr rs h.hiso _)
      c.geom]

/-- After an opaque group's `cm` — written or not, entering the model's
frame — and its clips, the three sides agree. -/
private theorem agrees_cm (place : Iso) (cx : Ctx) (fr : Frame) (rs : RState)
    (h : Agrees place cx fr rs) (xf : Affine) (m : Option Affine)
    (hm : (rs.cm m).frameCtm = cx.ctm.compose xf) (clips : Array Clip) :
    Agrees place (cx.enter xf clips Alpha.opaque) (fr.enter m)
      (rs.enterGroup m none (clipOpsOf (fr.enter m) clips)) where
  hplace := (cm_place rs _).trans h.hplace
  hiso := cm_iso place fr rs h.hiso _
  hctm := hm
  hbase := cm_base fr rs h.hbase m
  hclips := by
    show (rs.cm _).clips ++ _ = cx.clips ++ _
    rw [(cm_keeps rs _).1, h.hclips]
    congr 1
    exact clips_agree place cx fr rs h xf m hm clips
  halphas := by
    show (rs.cm _).alphas = _
    rw [(cm_keeps rs _).2.1, enter_alphas, h.halphas]
  hca := by show (rs.cm _).ca = _; rw [(cm_keeps rs _).2.2.1, h.hca]
  hcA := by show (rs.cm _).cA = _; rw [(cm_keeps rs _).2.2.2.1, h.hcA]
  hpen := by show (rs.cm _).pen = _; rw [(cm_keeps rs _).2.2.2.2.2, h.hpen]

/-- Inside an alpha group's transparency form, the three sides agree: the
group alpha is one more isolated group, alpha starts opaque inside, and the
form's default space is the user space at its `Do`. -/
private theorem agrees_alphaGroup (place : Iso) (cx : Ctx) (fr : Frame) (rs : RState)
    (h : Agrees place cx fr rs) (xf : Affine) (clips : Array Clip) (alpha : Alpha) (r : Nat)
    (ha : ¬alpha = Alpha.opaque) :
    Agrees place (cx.enter xf clips alpha) { fr.enter (groupCm fr xf) with stream := Affine.unit }
      ((rs.enterGroup (groupCm fr xf) (some { res := r, fill := alpha, stroke := alpha })
        (clipOpsOf (fr.enter (groupCm fr xf)) clips)).cm none).enterTransparency where
  hplace := (cm_place rs _).trans h.hplace
  hiso := cm_iso place fr rs h.hiso _
  hctm := (cm_group_frameCtm place cx fr rs h xf)
  hbase := (Affine.compose_unit_id _).1
  hclips := by
    show (rs.cm _).clips ++ _ = cx.clips ++ _
    rw [(cm_keeps rs _).1, h.hclips]
    congr 1
    exact clips_agree place cx fr rs h xf _ (cm_group_frameCtm place cx fr rs h xf) clips
  halphas := by
    have hb : (alpha == Alpha.opaque) = false := by simpa using ha
    show (rs.cm _).alphas.push alpha = _
    rw [(cm_keeps rs _).2.1, h.halphas]
    simp [Ctx.enter, hb]
  hca := rfl
  hcA := rfl
  hpen := by show (rs.cm _).pen = _; rw [(cm_keeps rs _).2.2.2.2.2, h.hpen]

/-- A plain group changes nothing the three sides read. -/
private theorem agrees_plain (place : Iso) (cx : Ctx) (fr : Frame) (rs : RState)
    (h : Agrees place cx fr rs) : Agrees place (cx.enter Affine.unit #[] Alpha.opaque) fr rs where
  hplace := h.hplace
  hiso := h.hiso
  hctm := by rw [h.hctm]; simp [Ctx.enter, (Affine.compose_unit_id cx.ctm).1]
  hbase := h.hbase
  hclips := by simp [Ctx.enter, h.hclips]
  halphas := by rw [enter_alphas]; exact h.halphas
  hca := h.hca
  hcA := h.hcA
  hpen := h.hpen

/-- Inside a symbol's form, painted under a lifted `cm` with no clip and no
alpha, the three sides agree: the form's frame is its own default space. -/
private theorem agrees_form (place : Iso) (cx : Ctx) (fr : Frame) (rs : RState)
    (h : Agrees place cx fr rs) (xf : Affine) :
    Agrees place (cx.enter xf #[] Alpha.opaque) symFrame (rs.cm (some (fr.lift xf))).enterForm where
  hplace := by simp [RState.enterForm, RState.cm, h.hplace]
  hiso := by simp [RState.enterForm, RState.cm, symFrame]
  hctm := by
    show (rs.cm (some (fr.lift xf))).frameCtm = _
    rw [cm_lift_frameCtm place cx fr rs h xf]; rfl
  hbase := enterForm_base _
  hclips := by simp [RState.enterForm, RState.cm, Ctx.enter, h.hclips]
  halphas := by rw [enter_alphas]; simp [RState.enterForm, RState.cm, h.halphas]
  hca := by simp [RState.enterForm, RState.cm, h.hca]
  hcA := by simp [RState.enterForm, RState.cm, h.hcA]
  hpen := by simp [RState.enterForm, RState.cm, h.hpen]

/-- A solid stamp's form reads back as its mark: its outline under the
instance's lifted `cm`, painted with the state the instance set. -/
private theorem read_stamp_form (ix : Request → Nat) (place : Iso) (cx : Ctx) (fr : Frame)
    (rs : RState) (h : Agrees place cx fr rs) (acc : Array Mark) (subs : Array Subpath) (xf : Affine)
    (fl : Option Fill) (st : Option Stroke) (hfl : fl.all (inheritable ·.paint) = true)
    (hst : st.all (inheritable ·.paint) = true) :
    readList (((rs.setPen (fl.map fun f => pdfPaint ix fr f.paint) (st.map (paintStroke ix fr))
        (extOf ix ((fl.map (·.alpha)).getD Alpha.opaque) ((st.map (·.alpha)).getD Alpha.opaque))).cm
          (some (fr.lift xf))).enterForm) acc (outlineBody subs fl st).toList =
      acc.push (.paint (cx.ctm.compose xf) (.path subs) (fl.map (Fill.under (cx.ctm.compose xf)))
        (st.map (Stroke.under (cx.ctm.compose xf))) cx.clips cx.alphas) := by
  generalize hgs : extOf ix ((fl.map (·.alpha)).getD Alpha.opaque)
    ((st.map (·.alpha)).getD Alpha.opaque) = gs
  have hgf : (gs.map (·.fill)).getD rs.ca = (fl.map (·.alpha)).getD Alpha.opaque := by
    rw [← hgs]; exact extOf_fill ix _ _ rs.ca h.hca
  have hgS : (gs.map (·.stroke)).getD rs.cA = (st.map (·.alpha)).getD Alpha.opaque := by
    rw [← hgs]; exact extOf_stroke ix _ _ rs.cA h.hcA
  generalize hr1 : rs.setPen (fl.map fun f => pdfPaint ix fr f.paint) (st.map (paintStroke ix fr)) gs
    = rs1
  have hu : rs1.userCtm = rs.userCtm := by rw [← hr1]; rfl
  have hp1 : rs1.placed = rs.placed ∧ rs1.clips = rs.clips ∧ rs1.alphas = rs.alphas := by
    rw [← hr1]; exact ⟨rfl, rfl, rfl⟩
  have hf : (rs1.cm (some (fr.lift xf))).frameCtm = cx.ctm.compose xf := by
    rw [cm_some_frameCtm, hu, ← cm_some_frameCtm]
    exact cm_lift_frameCtm place cx fr rs h xf
  simp only [outlineBody, readList, readOne, RState.outlineMark]
  have hfe : (rs1.cm (some (fr.lift xf))).enterForm.frameCtm = cx.ctm.compose xf := hf
  have hge : (rs1.cm (some (fr.lift xf))).enterForm.geom (geomOps (.path subs)).toArray =
      .path subs := by
    simp only [RState.geom, RState.enterForm, RState.cm, Bool.false_eq_true, ↓reduceIte,
      geomOf_path_id]
  have hce : (rs1.cm (some (fr.lift xf))).enterForm.clips = cx.clips := by
    rw [← h.hclips, ← hp1.2.1]; rfl
  have hae : (rs1.cm (some (fr.lift xf))).enterForm.alphas = cx.alphas := by
    rw [← h.halphas, ← hp1.2.2]; rfl
  rw [hfe, hge, hce, hae]
  have hpe : (rs1.cm (some (fr.lift xf))).enterForm.pen = rs1.pen := rfl
  have hcae : (rs1.cm (some (fr.lift xf))).enterForm.ca = rs1.ca := rfl
  have hcAe : (rs1.cm (some (fr.lift xf))).enterForm.cA = rs1.cA := rfl
  rw [hpe, hcae, hcAe]
  subst hr1
  congr 2
  · cases fl with
    | none => rfl
    | some f =>
      obtain ⟨p, r, a⟩ := f
      cases p with
      | gradient g => simp [inheritable] at hfl
      | solid c =>
        simp only [Option.map_some, Option.getD_some] at hgf
        simp only [RState.setPen, Option.map_some, Option.getD_some, Fill.under, Paint.under,
          pdfPaint, readPaint, hgf]
  · cases st with
    | none => rfl
    | some s =>
      obtain ⟨p, w, cap, join, ml, dash, ph, a⟩ := s
      obtain ⟨hc, hj, hm, hd, hph⟩ := stroke_defaults cap join ml dash ph
      cases p with
      | gradient g => simp [inheritable] at hst
      | solid c =>
        simp only [Option.map_some, Option.getD_some] at hgS
        simp only [RState.setPen, Option.isSome_some, ↓reduceIte, Option.map_some, Option.getD_some,
          Option.bind_some, Stroke.under, Paint.under, paintStroke, pdfPaint, readPaint, h.hpen, hc,
          hj, hm, hd, hph, hgS]

/-- A stamp painted inline — a gradient's — reads back as its mark: one
saved state under its lifted `cm`, the outline drawn in its frame. -/
private theorem read_stamp_inline (ix : Request → Nat) (place : Iso) (cx : Ctx) (fr : Frame)
    (rs : RState) (h : Agrees place cx fr rs) (acc : Array Mark) (subs : Array Subpath) (xf : Affine)
    (fl : Option Fill) (st : Option Stroke) :
    readOne rs acc (.group (some (fr.lift xf)) none #[]
        #[drawOp ix (fr.enter (some (fr.lift xf))) (.path subs) fl st]) =
      acc.push (.paint (cx.ctm.compose xf) (.path subs) (fl.map (Fill.under (cx.ctm.compose xf)))
        (st.map (Stroke.under (cx.ctm.compose xf))) cx.clips cx.alphas) := by
  have ha := agrees_cm place cx fr rs h xf (some (fr.lift xf)) (cm_lift_frameCtm place cx fr rs h xf) #[]
  simp only [clipOpsOf, Array.map_empty] at ha
  simp only [readOne, readList]
  rw [read_draw ix place _ _ _ ha]
  simp [Ctx.enter, Geom.normal]

mutual

/-- **A use-free tree's operators read back as its marks** — the induction
every form body rests on. -/
private theorem read_emitOne_free {L : Type} (ix : Request → Nat)
    (labelOps : Frame → L → Array ContentOp)
    (hl : ∀ fr l rs acc, readList rs acc (labelOps fr l).toList = acc)
    (outlines : Array (Array Subpath)) (bodyOps : Array (Array ContentOp)) (place : Iso) :
    ∀ (n : Node L) (cx : Ctx) (fr : Frame) (rs : RState) (acc : Array Mark),
      n.useFree = true → Agrees place cx fr rs →
      readList rs acc (emitOne ix labelOps outlines bodyOps fr #[] n).toList =
        Node.marksOne outlines cx acc n
  | .draw g fl st, cx, fr, rs, acc, _, h => by
    simp only [emitOne, Array.toList_push, List.nil_append, readList,
      read_draw ix place cx fr rs h, Node.marksOne]
  | .group xf clips alpha kids, cx, fr, rs, acc, hu, h => by
    simp only [Node.useFree] at hu
    simp only [emitOne, Node.marksOne]
    split
    · next hp =>
      obtain ⟨hx, hc, ha⟩ := hp
      subst hx hc ha
      exact read_emitList_free ix labelOps hl outlines bodyOps place kids.toList _ fr rs acc hu
        (agrees_plain place cx fr rs h)
    · split
      · next ha =>
        subst ha
        simp only [Array.toList_push, List.nil_append, readList, readOne]
        exact read_emitList_free ix labelOps hl outlines bodyOps place kids.toList _ _ _ acc hu
          (agrees_cm place cx fr rs h xf _ (cm_group_frameCtm place cx fr rs h xf) clips)
      · next ha =>
        simp only [Array.toList_push, List.nil_append, readList, readOne]
        exact read_emitList_free ix labelOps hl outlines bodyOps place kids.toList _ _ _ acc hu
          (agrees_alphaGroup place cx fr rs h xf clips alpha _ ha)
  | .use _ _, _, _, _, _, hu, _ => by simp [Node.useFree] at hu
  | .stamp o xf fl st, cx, fr, rs, acc, _, h => by
    simp only [emitOne, Node.marksOne]
    split
    · next hin =>
      simp only [Bool.and_eq_true] at hin
      simp only [Array.toList_push, List.nil_append, readList, readOne]
      exact read_stamp_form ix place cx fr rs h acc _ xf fl st hin.1 hin.2
    · simp only [Array.toList_push, List.nil_append, readList]
      exact read_stamp_inline ix place cx fr rs h acc _ xf fl st
  | .image k xf, cx, fr, rs, acc, _, h => by
    simp only [emitOne, Array.toList_push, List.nil_append, readList, readOne,
      Node.marksOne]
    rw [cm_lift_frameCtm place cx fr rs h xf, (cm_keeps rs _).1, (cm_keeps rs _).2.1, h.hclips,
      h.halphas]
  | .label l, cx, fr, rs, acc, _, _ => by
    simp only [emitOne, Array.empty_append, Node.marksOne]
    exact hl fr l rs acc
  | .words _, cx, fr, rs, acc, _, _ => by
    simp [emitOne, readList, Node.marksOne]

private theorem read_emitList_free {L : Type} (ix : Request → Nat)
    (labelOps : Frame → L → Array ContentOp)
    (hl : ∀ fr l rs acc, readList rs acc (labelOps fr l).toList = acc)
    (outlines : Array (Array Subpath)) (bodyOps : Array (Array ContentOp)) (place : Iso) :
    ∀ (xs : List (Node L)) (cx : Ctx) (fr : Frame) (rs : RState) (acc : Array Mark),
      Node.useFreeList xs = true → Agrees place cx fr rs →
      readList rs acc (emitList ix labelOps outlines bodyOps fr #[] xs).toList =
        Node.marksList outlines cx acc xs
  | [], _, _, _, _, _, _ => by simp [emitList, readList, Node.marksList]
  | n :: rest, cx, fr, rs, acc, hu, h => by
    simp only [Node.useFreeList, Bool.and_eq_true] at hu
    simp only [emitList, Node.marksList]
    rw [emitList_acc, Array.toList_append, readList_append,
      read_emitOne_free ix labelOps hl outlines bodyOps place n cx fr rs acc hu.1 h,
      read_emitList_free ix labelOps hl outlines bodyOps place rest cx fr rs _ hu.2 h]

end

private theorem agrees_root (place : Iso) :
    Agrees place Ctx.root { iso := some place, stream := Affine.unit } (RState.root place) where
  hplace := rfl
  hiso := rfl
  hctm := rfl
  hbase := (Affine.compose_unit_id _).1
  hclips := rfl
  halphas := rfl
  hca := rfl
  hcA := rfl
  hpen := rfl

mutual

private theorem read_emitOne {L : Type} (ix : Request → Nat)
    (labelOps : Frame → L → Array ContentOp)
    (hl : ∀ fr l rs acc, readList rs acc (labelOps fr l).toList = acc)
    (fig : Figure L) (place : Iso) :
    ∀ (n : Node L) (cx : Ctx) (fr : Frame) (rs : RState) (acc : Array Mark),
      Agrees place cx fr rs →
      readList rs acc
          (emitOne ix labelOps fig.outlines (bodyOpsOf ix labelOps fig) fr #[] n).toList =
        Node.marksList fig.outlines cx acc
          (Node.expandOne fig.bodies fig.bodies.size #[] n).toList
  | .draw g fl st, cx, fr, rs, acc, h => by
    simp only [emitOne, Node.expandOne, Array.toList_push, List.nil_append, readList,
      read_draw ix place cx fr rs h, Node.marksList, Node.marksOne]
  | .group xf clips alpha kids, cx, fr, rs, acc, h => by
    simp only [emitOne, Node.expandOne, Array.toList_push, List.nil_append, Node.marksList,
      Node.marksOne]
    split
    · next hp =>
      obtain ⟨hx, hc, ha⟩ := hp
      subst hx hc ha
      exact read_emitList ix labelOps hl fig place kids.toList _ fr rs acc
        (agrees_plain place cx fr rs h)
    · split
      · next ha =>
        subst ha
        simp only [Array.toList_push, List.nil_append, readList, readOne]
        exact read_emitList ix labelOps hl fig place kids.toList _ _ _ acc
          (agrees_cm place cx fr rs h xf _ (cm_group_frameCtm place cx fr rs h xf) clips)
      · next ha =>
        simp only [Array.toList_push, List.nil_append, readList, readOne]
        exact read_emitList ix labelOps hl fig place kids.toList _ _ _ acc
          (agrees_alphaGroup place cx fr rs h xf clips alpha _ ha)
  | .use k xf, cx, fr, rs, acc, h => by
    simp only [emitOne, Node.expandOne, bodyOpsOf, Array.getElem?_map]
    by_cases hk : k < fig.bodies.size
    · have hb : fig.bodies[k]? = some fig.bodies[k] := Array.getElem?_eq_getElem hk
      simp only [hk, ↓reduceIte, hb, Option.map_some, Array.toList_push, List.nil_append,
        readList, readOne, Node.marksList, Node.marksOne]
      exact read_emitList_free ix labelOps hl fig.outlines #[] place _ _ symFrame _ acc
        (Figure.bodies_useFree_covers fig _ (Array.getElem_mem hk))
        (agrees_form place cx fr rs h xf)
    · simp [hk, readList, Node.marksList]
  | .stamp o xf fl st, cx, fr, rs, acc, h => by
    have := read_emitOne_free ix labelOps hl fig.outlines (bodyOpsOf ix labelOps fig) place
      (.stamp o xf fl st) cx fr rs acc rfl h
    simpa [Node.expandOne, Node.marksList] using this
  | .image k xf, cx, fr, rs, acc, h => by
    have := read_emitOne_free ix labelOps hl fig.outlines (bodyOpsOf ix labelOps fig) place
      (.image k xf) cx fr rs acc rfl h
    simpa [Node.expandOne, Node.marksList] using this
  | .label l, cx, fr, rs, acc, h => by
    have := read_emitOne_free ix labelOps hl fig.outlines (bodyOpsOf ix labelOps fig) place
      (.label l) cx fr rs acc rfl h
    simpa [Node.expandOne, Node.marksList] using this
  | .words w, cx, fr, rs, acc, h => by
    have := read_emitOne_free ix labelOps hl fig.outlines (bodyOpsOf ix labelOps fig) place
      (.words w) cx fr rs acc rfl h
    simpa [Node.expandOne, Node.marksList] using this

private theorem read_emitList {L : Type} (ix : Request → Nat)
    (labelOps : Frame → L → Array ContentOp)
    (hl : ∀ fr l rs acc, readList rs acc (labelOps fr l).toList = acc)
    (fig : Figure L) (place : Iso) :
    ∀ (xs : List (Node L)) (cx : Ctx) (fr : Frame) (rs : RState) (acc : Array Mark),
      Agrees place cx fr rs →
      readList rs acc
          (emitList ix labelOps fig.outlines (bodyOpsOf ix labelOps fig) fr #[] xs).toList =
        Node.marksList fig.outlines cx acc
          (Node.expandList fig.bodies fig.bodies.size #[] xs).toList
  | [], _, _, _, _, _ => by simp [emitList, readList, Node.expandList, Node.marksList]
  | n :: rest, cx, fr, rs, acc, h => by
    simp only [emitList, Node.expandList]
    rw [emitList_acc, Array.toList_append, readList_append, Node.expandList_acc, Array.toList_append,
      Node.marksList_append, read_emitOne ix labelOps hl fig place n cx fr rs acc h,
      read_emitList ix labelOps hl fig place rest cx fr rs _ h]

end

/-- **What the PDF says is what the figure paints** (`_projects`): the
operators `emit` writes, read with PDF's meaning — its initial graphics
state, its `cm` composition, a pattern's matrix against the default space of
the stream that paints, its clips, its transparency groups, and a stamp's
form painting with the state its instance set — are the figure's marks, for
every figure, placement and resource naming, given a label setter that adds
no ink. Half of `backend_marks_agree`: the state the writer elides because
PDF starts there is the state the figure asked for, and a gradient lands in
the frame the figure placed it in. -/
public theorem marks_projects {L : Type} (ix : Request → Nat)
    (labelOps : Frame → L → Array ContentOp)
    (hl : ∀ fr l rs acc, readList rs acc (labelOps fr l).toList = acc)
    (place : Iso) (fig : Figure L) :
    readMarks place (emit ix labelOps place fig) = fig.marks := by
  unfold readMarks emit Figure.marks Figure.expanded
  exact read_emitList ix labelOps hl fig place fig.nodes.toList Ctx.root _ (RState.root place) #[]
    (agrees_root place)

end LeanTex.Core.GfxPdf
