module

public import LeanTex.Core.Gfx
public import LeanTex.Core.GfxAffine
public import LeanTex.Core.Html

/-!
# A figure as SVG

Two layers. `tree` lowers a figure onto a typed SVG element tree — typed
geometry and typed presentation attributes, each attribute present exactly
where it differs from SVG's initial value — and `readMarks` reads that tree
with SVG's own meaning (SVG 2 §13: fill initially black, stroke initially
none, width 1, miter limit 4; a zero width paints nothing; a group's
`opacity` composites it as one isolated group). `marks_projects` is the
statement that the reading is the figure's marks, before a byte is spelled.
`spell` is the second layer: the total spelling of that tree into
`Html.Node`, through the certified escaper, with presentation attributes
only — never a style element, never a tag string.

The placement into the SVG's frame (y down, the viewBox's origin) is an
isometry applied to coordinates exactly; a group's transform composes it in
once, at the first transformed group, and so does a gradient's
`gradientTransform` where its shape's coordinates are still placed — a
`userSpaceOnUse` gradient reads its numbers in the placed frame, so its own
frame map must carry the placement as the shape's points do. The reader
places it back in the figure frame (`readPaint`), which is what
`marks_projects` holds it to. Every group is a `g`, so a TikZ edge's
wrapper is today's.
-/

namespace LeanTex.Core.GfxSvg

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Gfx

/-! ## The typed tree -/

/-- A paint attribute's value: `none`, a colour, or a gradient reference —
the gradient as its definition spells it, its frame map the
`gradientTransform` from its own frame to the user space of the element it
paints (`userSpaceOnUse`, SVG 2 §14.2), its id assigned when spelled. -/
public inductive SPaint where
  | none
  | color (c : Ir.Color)
  | url (g : Gradient)
  deriving Repr, Inhabited

/-- A stroke width as spelled: a length in the viewBox's units, or the
hairline — one CSS pixel that does not scale (`vector-effect`), the
thinnest visible line, as PDF's width 0 is one device pixel. -/
public inductive SWidth where
  | len (w : Sp)
  | hairline
  deriving Repr, BEq, Inhabited

/-- A shape's presentation attributes, each absent where SVG's initial value
is the one meant. -/
public structure ShapeAttrs where
  fill : Option SPaint
  fillRule : Option Rule
  fillOpacity : Option Alpha
  stroke : Option SPaint
  strokeWidth : Option SWidth
  cap : Option Cap
  join : Option Join
  miter : Option Rat
  dash : Option (Array Sp)
  dashOffset : Option Sp
  strokeOpacity : Option Alpha
  deriving Repr, Inhabited

/-- A clip region: its geometry in the frame of the group it clips, its
rule; its id assigned when spelled. -/
public structure ClipRef where
  geom : Geom
  rule : Rule
  deriving Repr, Inhabited

/-- A raster as the SVG references it: its URL (a `data:` URI for an
embedded one), and whether a reader may smooth its samples when it scales
them (`Gfx.Raster.smooth`). -/
public structure RasterRef where
  href : String
  smooth : Bool
  deriving Inhabited

/-- One element of the typed tree. A shape draws its geometry with its
attributes (`rect`, `circle` or `ellipse`, `path` by the geometry's kind); a
`g` has an optional transform, group opacity and clip; a `use` paints symbol
`sym` and carries its body for the reader; a stamp paints outline
`outline` with its own attributes; an image maps raster `k`'s unit square;
a raw node is engine-set label content. -/
public inductive El where
  | shape (g : Geom) (a : ShapeAttrs)
  | g (xf : Option Affine) (opacity : Option Alpha) (clip : Option ClipRef) (kids : Array El)
  | use (sym : Nat) (xf : Affine) (body : Array El)
  | stamp (outline : Nat) (xf : Affine) (subs : Array Subpath) (a : ShapeAttrs)
  | image (k : Nat) (m : Affine) (ref : RasterRef)
  | raw (n : Html.Node)
  deriving Inhabited

/-! ## Emission -/

/-- SVG's initial miter limit (SVG 2 §13.5.5). -/
@[expose] public def svgMiter : Rat := 4

/-- One user unit: the viewBox's point. -/
@[expose] public def svgUnit : Sp := Dim.spPerPt

/-- Where emission stands: whether coordinates are still carried by the
placement exactly. -/
public structure SFrame where
  iso : Option Iso
  deriving Repr, Inhabited

@[expose] public def SFrame.lift (fr : SFrame) (xf : Affine) : Affine :=
  match fr.iso with
  | some t => t.toAffine.compose xf
  | none => xf

@[expose] public def SFrame.place (fr : SFrame) (g : Geom) : Geom :=
  match fr.iso with
  | some t => g.mapIso t
  | none => g

/-- A paint in the element's user space: a gradient's frame map carried
into it as coordinates are — the placement composed in where the
coordinates are still placed. -/
@[expose] public def sPaint (fr : SFrame) : Paint → SPaint
  | .solid c => .color c
  | .gradient g => .url (g.withXf (fr.lift g.xf))

/-- A draw's attributes: `fill="none"` stated when it does not fill (SVG
fills black otherwise); the stroke's every field where it differs from
SVG's initial value — the miter limit included, since pgf's and PDF's 10 is
not SVG's 4 — and the width always, the hairline as `vector-effect`; each
paint in the element's user space (`sPaint`). -/
@[expose] public def attrsOf (fr : SFrame) (fl : Option Fill) (st : Option Stroke) : ShapeAttrs :=
  { fill := some (match fl with
      | some f => sPaint fr f.paint
      | none => .none)
    fillRule := fl.bind fun f => match f.rule with
      | .evenOdd => some .evenOdd
      | .nonzero => none
    fillOpacity := fl.bind fun f => if f.alpha = Alpha.opaque then none else some f.alpha
    stroke := st.map fun s => sPaint fr s.paint
    strokeWidth := st.map fun s => if s.width = 0 then .hairline else .len s.width
    cap := st.bind fun s => match s.cap with
      | .butt => none
      | .round => some .round
      | .square => some .square
    join := st.bind fun s => match s.join with
      | .miter => none
      | .round => some .round
      | .bevel => some .bevel
    miter := st.bind fun s => if s.miterLimit = svgMiter then none else some s.miterLimit
    dash := st.bind fun s => if s.dash = #[] then none else some s.dash
    dashOffset := st.bind fun s => if s.phase = 0 then none else some s.phase
    strokeOpacity := st.bind fun s => if s.alpha = Alpha.opaque then none else some s.alpha }

/-- A group's transform attribute, if it has one to write. -/
@[expose] public def groupXf (fr : SFrame) (xf : Affine) : Option Affine :=
  if xf = Affine.unit then none else some (fr.lift xf)

@[expose] public def SFrame.enter (fr : SFrame) : Option Affine → SFrame
  | none => fr
  | some _ => { iso := none }

/-- A group's clips, each one `g` around the kids, in the group's frame. -/
@[expose] public def nestClips (fr : SFrame) (kids : Array El) : List Clip → Array El
  | [] => kids
  | c :: rest => #[.g none none (some { geom := fr.place c.geom, rule := c.rule })
      (nestClips fr kids rest)]

/-- Flip a raster's unit square, one frame unit on a side (`rasterUnit`):
the model's (0,0) is its bottom-left, an SVG image's its top-left. -/
@[expose] public def unitFlip : Affine := ⟨1, 0, 0, -1, 0, 65536⟩

mutual

-- conserves: none — an emitter: what it keeps is `marks_projects`.
/-- One node's elements. A label is set by `labelEl`, which reads the frame. -/
@[expose] public def treeOne {L : Type} (labelEl : SFrame → L → Html.Node)
    (outlines : Array (Array Subpath)) (rasters : Array RasterRef)
    (bodies : Array (Array El)) (fr : SFrame) (acc : Array El) : Node L → Array El
  | .draw g fl st => acc.push (.shape (fr.place g) (attrsOf fr fl st))
  | .group xf clips alpha kids =>
    let t := groupXf fr xf
    let fr' := fr.enter t
    let inner := treeList labelEl outlines rasters bodies fr' #[] kids.toList
    let op := if alpha = Alpha.opaque then none else some alpha
    acc.push (.g t op none (nestClips fr' inner clips.toList))
  | .use k xf =>
    match bodies[k]? with
    | some body => acc.push (.use k (fr.lift xf) body)
    | none => acc
  | .stamp o xf fl st =>
    -- The paints stand in the stamp's own frame: the cloned outline's
    -- user space is the use's, its transform applied.
    acc.push (.stamp o (fr.lift xf) (outlines[o]?.getD #[]) (attrsOf { iso := none } fl st))
  | .image k xf => acc.push (.image k (fr.lift xf) (rasters[k]?.getD default))
  | .label l => acc.push (.raw (labelEl fr l))
  | .words _ => acc

@[expose] public def treeList {L : Type} (labelEl : SFrame → L → Html.Node)
    (outlines : Array (Array Subpath)) (rasters : Array RasterRef)
    (bodies : Array (Array El)) (fr : SFrame) (acc : Array El) : List (Node L) → Array El
  | [] => acc
  | n :: rest =>
    treeList labelEl outlines rasters bodies fr (treeOne labelEl outlines rasters bodies fr acc n) rest

end

/-- The symbols' bodies, each expanded body (`Figure.bodies`) in its own
frame. -/
@[expose] public def bodyEls {L : Type} (labelEl : SFrame → L → Html.Node) (rasters : Array RasterRef)
    (fig : Figure L) : Array (Array El) :=
  fig.bodies.map fun b => treeList labelEl fig.outlines rasters #[] { iso := none } #[] b.toList

/-- **A figure as a typed SVG tree** under the placement into the SVG's
frame; `rasters` are the rasters' data URIs. -/
@[expose] public def tree {L : Type} (labelEl : SFrame → L → Html.Node) (rasters : Array RasterRef)
    (place : Iso) (fig : Figure L) : Array El :=
  treeList labelEl fig.outlines rasters (bodyEls labelEl rasters fig) { iso := some place } #[]
    fig.nodes.toList

/-! ## Spelling -/

/-- What the spelling carries: the figure's ordinal, the next clip and
gradient numbers, the definitions collected so far, and the symbols and
outlines already defined. -/
public structure Spell where
  ord : Nat
  clips : Nat
  grads : Nat
  defs : Array Html.Node
  syms : Array Nat
  outlines : Array Nat
  deriving Inhabited

/-- What an element id names: a gradient, a clip path, a symbol, an
outline. -/
public inductive IdKind where
  | gradient
  | clip
  | symbol
  | outline
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The letter an id spells its kind with. -/
@[expose] public def IdKind.letter : IdKind → Char
  | .gradient => 'g'
  | .clip => 'c'
  | .symbol => 's'
  | .outline => 'o'

/-- The character a figure's ids put between the figure's ordinal and the
kind: one no other id this backend writes can hold — a label's anchor
keeps only letters, digits, `:`, `.`, `-` and `_` (`Ir.labelAnchor`), a
title's slug only letters, digits and `-` (`Ir.slug`), a reference entry's
starts `ref-` — so a figure's ids never take an anchor the document names. -/
@[expose] public def idSep : Char := '~'

/-- An element id: `f{figure}~{kind}{index}`. Distinct triples never share
an id (`ids_inj`), and the parts read back (`parseId_svgId_exact`), so the
page numbers its figures apart (`renumberList`) and the spelling is stable
across builds. -/
@[expose] public def svgId (ord : Nat) (kind : IdKind) (i : Nat) : String :=
  "f" ++ toString ord ++ String.singleton idSep ++ String.singleton kind.letter ++ (toString i)

private theorem digits_sep (a b r s : List Char) (ha : ∀ c ∈ a, c.isDigit = true)
    (hb : ∀ c ∈ b, c.isDigit = true) (h : a ++ idSep :: r = b ++ idSep :: s) : a = b ∧ r = s := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons c b =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have := hb c (by simp)
      rw [← h.1] at this
      exact absurd this (by decide)
  | cons c a ih =>
    cases b with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have := ha c (by simp)
      rw [h.1] at this
      exact absurd this (by decide)
    | cons d b =>
      simp only [List.cons_append, List.cons.injEq] at h
      have := ih b (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx])) h.2
      exact ⟨by rw [h.1, this.1], this.2⟩

private theorem toDigits_inj {m n : Nat} (h : Nat.toDigits 10 m = Nat.toDigits 10 n) : m = n := by
  rw [← Nat.ofDigitChars_ten_toDigits (n := m), ← Nat.ofDigitChars_ten_toDigits (n := n), h]

private theorem letter_inj {k k' : IdKind} (h : k.letter = k'.letter) : k = k' := by
  cases k <;> cases k' <;> first | rfl | exact absurd h (by decide)

private theorem digit_toDigits (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := fun _ hc =>
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

private theorem svgId_chars (o : Nat) (k : IdKind) (i : Nat) :
    (svgId o k i).toList = 'f' :: (Nat.toDigits 10 o ++ idSep :: k.letter :: Nat.toDigits 10 i) := by
  simp only [svgId, String.toList_append, Nat.toString_eq_ofList_toDigits, String.toList_ofList,
    String.toList_singleton, List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-- **Element ids are injective** (`_inj`): a figure's ordinal, the kind
and the index are read back from the id, because a decimal numeral holds no
separator and the kind is one letter — so two definitions of one figure, or
of two figures numbered apart, never share an id. -/
public theorem ids_inj {o o' i i' : Nat} {k k' : IdKind} (h : svgId o k i = svgId o' k' i') :
    o = o' ∧ k = k' ∧ i = i' := by
  have h' := congrArg String.toList h
  rw [svgId_chars, svgId_chars] at h'
  simp only [List.cons.injEq, true_and] at h'
  obtain ⟨ho, hr⟩ := digits_sep _ _ _ _ (digit_toDigits o) (digit_toDigits o') h'
  simp only [List.cons.injEq] at hr
  exact ⟨toDigits_inj ho, letter_inj hr.1, toDigits_inj hr.2⟩

/-- A kind read from its letter. -/
@[expose] public def IdKind.ofLetter? (c : Char) : Option IdKind :=
  if c = 'g' then some .gradient else if c = 'c' then some .clip
  else if c = 's' then some .symbol else if c = 'o' then some .outline else none

private theorem ofLetter_letter (k : IdKind) : IdKind.ofLetter? k.letter = some k := by
  cases k <;> rfl

/-- A figure id's parts, read from its characters: `f`, the figure's
numeral, the separator, the kind's letter, the index's numeral — anything
else is no figure id. -/
@[expose] public def parseIdChars (cs : List Char) : Option (Nat × IdKind × Nat) :=
  match cs with
  | [] => none
  | c0 :: rest =>
    if c0 = 'f' then
      match rest.dropWhile Char.isDigit with
      | [] => none
      | [_] => none
      | c :: l :: d2 =>
        let d1 := rest.takeWhile Char.isDigit
        if c = idSep ∧ d1 ≠ [] ∧ d2 ≠ [] ∧ d2.all Char.isDigit = true then
          (IdKind.ofLetter? l).map fun k => (Nat.ofDigitChars 10 d1 0, k, Nat.ofDigitChars 10 d2 0)
        else none
    else none

@[expose] public def parseId (s : String) : Option (Nat × IdKind × Nat) := parseIdChars s.toList

private theorem span_digits (a r : List Char) (ha : ∀ c ∈ a, c.isDigit = true) (c : Char)
    (hc : c.isDigit = false) :
    (a ++ c :: r).takeWhile Char.isDigit = a ∧ (a ++ c :: r).dropWhile Char.isDigit = c :: r := by
  induction a with
  | nil => simp [hc]
  | cons x a ih =>
    have hx := ha x (by simp)
    have ih' := ih (fun y hy => ha y (by simp [hy]))
    simp [hx, ih'.1, ih'.2]

/-- **A figure id reads back as its parts** (`_exact`): the ordinal, the
kind and the index `svgId` spelled — what renumbering a page's figures reads. -/
public theorem parseId_svgId_exact (o : Nat) (k : IdKind) (i : Nat) :
    parseId (svgId o k i) = some (o, k, i) := by
  have hs : idSep.isDigit = false := by decide
  obtain ⟨ht, hd⟩ := span_digits (Nat.toDigits 10 o) (k.letter :: Nat.toDigits 10 i)
    (digit_toDigits o) idSep hs
  have hall : (Nat.toDigits 10 i).all Char.isDigit = true :=
    List.all_eq_true.mpr (digit_toDigits i)
  simp only [parseId, svgId_chars, parseIdChars, ↓reduceIte, hd, ht, ofLetter_letter, Option.map_some,
    Nat.ofDigitChars_ten_toDigits, Nat.toDigits_ne_nil, hall, ne_eq, not_false_eq_true, and_self]

/-- The attributes a figure's spelling names a definition in: the
definition's own id, a `use`'s `href`, a paint or a clip. -/
@[expose] public def refKeys : List String := ["id", "href", "fill", "stroke", "clip-path"]

/-- An attribute value naming one of figure 0's definitions — the id, a `#`
reference, a `url(#…)` paint or clip, each spelling `spell` writes —
renumbered to figure `n`; any other value as it is. -/
@[expose] public def renumberValue (n : Nat) (v : String) : String :=
  let cs := v.toList
  match parseIdChars cs with
  | some (0, k, i) => svgId n k i
  | _ =>
    match cs with
    | '#' :: rest =>
      match parseIdChars rest with
      | some (0, k, i) =>
        let id := svgId n k i
        "#" ++ id
      | _ => v
    | 'u' :: 'r' :: 'l' :: '(' :: '#' :: rest =>
      match parseIdChars rest.dropLast, rest.getLast? with
      | some (0, k, i), some ')' => "url(#" ++ svgId n k i ++ ")"
      | _, _ => v
    | _ => v

mutual

-- conserves: none — a renaming of the attribute values that name a
-- figure's definitions; text and structure stay (`renumberChecks`).
/-- A figure's spelled nodes renumbered to figure `n`: every attribute that
names one of its definitions. A nested `svg` is another figure's, and keeps
its own numbering. -/
public def renumberOne (n : Nat) : Html.Node → Html.Node
  | .elem tag attrs kids =>
    if tag == "svg" then .elem tag attrs kids
    else
      .elem tag (attrs.map fun kv => if refKeys.contains kv.1 then (kv.1, renumberValue n kv.2) else kv)
        (renumberList n #[] kids.toList)
  | .text s => .text s
  | .style s => .style s
  | .script a s => .script a s

public def renumberList (n : Nat) (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | x :: rest => renumberList n (acc.push (renumberOne n x)) rest

end

/-- A path's `d`: each command and its operands followed by a space, a
closed subpath's `Z` too unless it ends the path. -/
public def pathD (subs : Array Subpath) : String :=
  let seg (acc : String) : Seg → String
    | .line p => acc ++ s!"L {p.1.toPtString} {p.2.toPtString} "
    | .cubic c1 c2 p =>
      acc ++ s!"C {c1.1.toPtString} {c1.2.toPtString}, {c2.1.toPtString} {c2.2.toPtString}, \
{p.1.toPtString} {p.2.toPtString} "
  let raw := subs.foldl (fun acc sp =>
    let acc := acc ++ s!"M {sp.start.1.toPtString} {sp.start.2.toPtString} "
    let acc := sp.segs.foldl seg acc
    if sp.closed then acc ++ "Z " else acc) ""
  if raw.endsWith "Z " then (raw.dropEnd 1).toString else raw

/-- A geometry as an element: a rectangle, a circle or ellipse, a path. -/
public def geomEl (g : Geom) (attrs : Array (String × String)) : Html.Node :=
  match g with
  | .rect x y w h =>
    Html.elem "rect" #[] (#[("x", x.toPtString), ("y", y.toPtString), ("width", w.toPtString),
      ("height", h.toPtString)] ++ attrs)
  | .ellipse cx cy rx ry =>
    if rx = ry then
      Html.elem "circle" #[] (#[("cx", cx.toPtString), ("cy", cy.toPtString),
        ("r", rx.toPtString)] ++ attrs)
    else
      Html.elem "ellipse" #[] (#[("cx", cx.toPtString), ("cy", cy.toPtString),
        ("rx", rx.toPtString), ("ry", ry.toPtString)] ++ attrs)
  | .path subs => Html.elem "path" #[] (#[("d", pathD subs)] ++ attrs)

/-- An alpha as an opacity, to three decimals. -/
@[expose] public def alphaSpell (a : Alpha) : String := ratString a.val 1000

/-- A gradient as its element, its coordinates in the user space of the
shape it paints (`userSpaceOnUse`), its own frame its `gradientTransform`,
pad spread. -/
public def gradientEl (id : String) : Gradient → Html.Node
  | .linear p0 p1 stops xf =>
    Html.elem "linearGradient" (stops.map stopEl) #[("id", id), ("gradientUnits", "userSpaceOnUse"),
      ("x1", p0.1.toPtString), ("y1", p0.2.toPtString), ("x2", p1.1.toPtString),
      ("y2", p1.2.toPtString), ("gradientTransform", s!"matrix({xf.operands})")]
  | .radial c0 r0 c1 r1 stops xf =>
    Html.elem "radialGradient" (stops.map stopEl) #[("id", id), ("gradientUnits", "userSpaceOnUse"),
      ("fx", c0.1.toPtString), ("fy", c0.2.toPtString), ("fr", r0.toPtString),
      ("cx", c1.1.toPtString), ("cy", c1.2.toPtString), ("r", r1.toPtString),
      ("gradientTransform", s!"matrix({xf.operands})")]
where
  stopEl (st : Stop) : Html.Node :=
    Html.elem "stop" #[] #[("offset", ratString st.offset.val 65536), ("stop-color", st.color.css)]

/-- A paint attribute's value; a gradient takes the next id and its
definition. -/
public def paintValue (sp : Spell) : SPaint → String × Spell
  | .none => ("none", sp)
  | .color c => (c.css, sp)
  | .url g =>
    let id := svgId sp.ord .gradient sp.grads
    (s!"url(#{id})", { sp with grads := sp.grads + 1, defs := sp.defs.push (gradientEl id g) })

/-- An optional paint's value; a gradient takes the next id. -/
@[expose] public def optPaint (sp : Spell) : Option SPaint → Option String × Spell
  | some p => let r := paintValue sp p; (some r.1, r.2)
  | none => (none, sp)

/-- An attribute present exactly when its value is. -/
@[expose] public def optAttr (k : String) : Option String → Array (String × String)
  | some v => #[(k, v)]
  | none => #[]

@[expose] public def ruleName : Rule → String
  | .evenOdd => "evenodd"
  | .nonzero => "nonzero"

@[expose] public def capName : Cap → String
  | .butt => "butt"
  | .round => "round"
  | .square => "square"

@[expose] public def joinName : Join → String
  | .miter => "miter"
  | .round => "round"
  | .bevel => "bevel"

/-- A stroke width's attributes: a length, or the hairline's one pixel
that does not scale. -/
@[expose] public def widthAttrs : Option SWidth → Array (String × String)
  | some (.len l) => #[("stroke-width", l.toPtString)]
  | some .hairline => #[("stroke-width", "1"), ("vector-effect", "non-scaling-stroke")]
  | none => #[]

/-- A shape's attributes in a fixed order — the fill's, then the stroke's —
each present only where the typed tree says. -/
@[expose] public def attrsSpell (sp : Spell) (a : ShapeAttrs) : Array (String × String) × Spell :=
  let fv := optPaint sp a.fill
  let sv := optPaint fv.2 a.stroke
  (optAttr "fill" fv.1 ++ optAttr "fill-rule" (a.fillRule.map ruleName) ++
    optAttr "fill-opacity" (a.fillOpacity.map alphaSpell) ++ optAttr "stroke" sv.1 ++
    widthAttrs a.strokeWidth ++ optAttr "stroke-linecap" (a.cap.map capName) ++
    optAttr "stroke-linejoin" (a.join.map joinName) ++
    optAttr "stroke-dasharray" (a.dash.map fun d => " ".intercalate (d.toList.map Sp.toPtString)) ++
    optAttr "stroke-dashoffset" (a.dashOffset.map Sp.toPtString) ++
    optAttr "stroke-miterlimit" (a.miter.map ratDecimal) ++
    optAttr "stroke-opacity" (a.strokeOpacity.map alphaSpell), sv.2)

/-- A transform attribute. -/
@[expose] public def transformAttr (m : Affine) : String × String := ("transform", s!"matrix({m.operands})")

mutual

-- conserves: none — a spelling: `spell_plain_exact` and the matrix pin it.
/-- One element spelled onto `acc`. A clip, a gradient, a symbol's body and
an outline go once into the definitions, under their ids. -/
public def spellOne (sp : Spell) (acc : Array Html.Node) : El → Array Html.Node × Spell
  | .shape g a =>
    let (attrs, sp) := attrsSpell sp a
    (acc.push (geomEl g attrs), sp)
  | .g xf op clip kids =>
    let (inner, sp) := spellList sp #[] kids.toList
    let base : Array (String × String) :=
      (match xf with
       | some m => #[transformAttr m]
       | none => #[]) ++
      (match op with
       | some a => #[("opacity", alphaSpell a)]
       | none => #[])
    match clip with
    | none => (acc.push (Html.elem "g" inner base), sp)
    | some c =>
      let id := svgId sp.ord .clip sp.clips
      let ruleAttr : Array (String × String) := match c.rule with
        | .evenOdd => #[("clip-rule", "evenodd")]
        | .nonzero => #[]
      let def_ := Html.elem "clipPath" #[geomEl c.geom ruleAttr]
        #[("id", id), ("clipPathUnits", "userSpaceOnUse")]
      (acc.push (Html.elem "g" inner (base.push ("clip-path", s!"url(#{id})"))),
        { sp with clips := sp.clips + 1, defs := sp.defs.push def_ })
  | .use k xf body =>
    let id := svgId sp.ord .symbol k
    let sp := if sp.syms.contains k then sp else
      let (inner, sp') := spellList { sp with syms := sp.syms.push k } #[] body.toList
      { sp' with defs := sp'.defs.push (Html.elem "symbol" inner #[("id", id), ("overflow", "visible")]) }
    (acc.push (Html.elem "use" #[] #[("href", s!"#{id}"), transformAttr xf]), sp)
  | .stamp o xf subs a =>
    let id := svgId sp.ord .outline o
    let sp := if sp.outlines.contains o then sp else
      { sp with outlines := sp.outlines.push o
                defs := sp.defs.push (Html.elem "path" #[] #[("id", id), ("d", pathD subs)]) }
    let (attrs, sp) := attrsSpell sp a
    (acc.push (Html.elem "use" #[] (#[("href", s!"#{id}"), transformAttr xf] ++ attrs)), sp)
  | .image _ m ref =>
    let rendering : Array (String × String) :=
      if ref.smooth then #[] else #[("image-rendering", "pixelated")]
    (acc.push (Html.elem "image" #[] (#[("href", ref.href), ("width", "1"), ("height", "1"),
      ("preserveAspectRatio", "none"), transformAttr (m.compose unitFlip)] ++ rendering)), sp)
  | .raw n => (acc.push n, sp)

public def spellList (sp : Spell) (acc : Array Html.Node) : List El → Array Html.Node × Spell
  | [] => (acc, sp)
  | e :: rest =>
    let (acc, sp) := spellOne sp acc e
    spellList sp acc rest

end

/-- **A typed tree spelled**: its elements, behind one `defs` when it
defines anything. `ord` numbers the figure in its document. -/
public def spell (ord : Nat) (els : Array El) : Array Html.Node :=
  let start : Spell :=
    { ord := ord, clips := 0, grads := 0, defs := #[], syms := #[], outlines := #[] }
  let (items, sp) := spellList start #[] els.toList
  if sp.defs.isEmpty then items else #[Html.elem "defs" sp.defs] ++ items

/-! ## A tree that names no definition spells element for element -/

@[expose] public def SPaint.plain : SPaint → Bool
  | .none => true
  | .color _ => true
  | .url _ => false

mutual

-- conserves: none — a predicate.
/-- An element that names no definition — no gradient paint, no clip, no
symbol, no stamp: what spells with nothing to define, one node per element.
A TikZ picture's elements are. -/
@[expose] public def El.plain : El → Bool
  | .shape _ a => a.fill.all SPaint.plain && a.stroke.all SPaint.plain
  | .g _ _ clip kids => clip.isNone && El.plainList kids.toList
  | .use _ _ _ => false
  | .stamp _ _ _ _ => false
  | .image _ _ _ => true
  | .raw _ => true

@[expose] public def El.plainList : List El → Bool
  | [] => true
  | e :: rest => e.plain && El.plainList rest

end

private theorem optPaint_plain (sp : Spell) (p : Option SPaint) (h : p.all SPaint.plain = true) :
    (optPaint sp p).2 = sp := by
  cases p with
  | none => rfl
  | some q => cases q <;> simp_all [optPaint, SPaint.plain, paintValue]

private theorem attrsSpell_plain (sp : Spell) (a : ShapeAttrs) (hf : a.fill.all SPaint.plain = true)
    (hs : a.stroke.all SPaint.plain = true) : (attrsSpell sp a).2 = sp := by
  simp only [attrsSpell]
  rw [optPaint_plain _ _ hs, optPaint_plain _ _ hf]

mutual

private theorem spellOne_plain (sp : Spell) :
    ∀ (acc : Array Html.Node) (e : El), e.plain = true → ∃ node, spellOne sp acc e = (acc.push node, sp)
  | acc, .shape g a, h => by
    simp only [El.plain, Bool.and_eq_true] at h
    have ha := attrsSpell_plain sp a h.1 h.2
    refine ⟨geomEl g (attrsSpell sp a).1, ?_⟩
    simp only [spellOne]
    rw [ha]
  | acc, .g xf op clip kids, h => by
    simp only [El.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨hc, hk⟩ := h
    subst hc
    have hl := (spellList_plain sp #[] kids.toList hk).1
    refine ⟨Html.elem "g" (spellList sp #[] kids.toList).1
      ((match xf with
        | some m => #[transformAttr m]
        | none => #[]) ++
       (match op with
        | some a => #[("opacity", alphaSpell a)]
        | none => #[])), ?_⟩
    simp only [spellOne]
    rw [hl]
  | _, .use _ _ _, h => by simp [El.plain] at h
  | _, .stamp _ _ _ _, h => by simp [El.plain] at h
  | acc, .image k m ref, _ => ⟨_, rfl⟩
  | acc, .raw n, _ => ⟨n, rfl⟩

private theorem spellList_plain (sp : Spell) :
    ∀ (acc : Array Html.Node) (els : List El), El.plainList els = true →
      (spellList sp acc els).2 = sp ∧
        ∃ nodes : Array Html.Node, (spellList sp acc els).1 = acc ++ nodes ∧
          nodes.size = els.length ∧
            ∀ (j : Nat) (n : Html.Node), els[j]? = some (El.raw n) → nodes[j]? = some n
  | acc, [], _ => ⟨rfl, #[], by simp [spellList]⟩
  | acc, e :: rest, h => by
    simp only [El.plainList, Bool.and_eq_true] at h
    obtain ⟨node, hn⟩ := spellOne_plain sp acc e h.1
    have hr := spellList_plain sp (acc.push node) rest h.2
    obtain ⟨nodes, h1, h2, h3⟩ := hr.2
    have he : spellList sp acc (e :: rest) = spellList sp (acc.push node) rest := by
      simp only [spellList, hn]
    rw [he]
    refine ⟨hr.1, #[node] ++ nodes, by rw [h1]; simp, by simp [h2]; omega, ?_⟩
    intro j n hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [spellOne, Prod.mk.injEq] at hn
      have : node = n := by
        have := congrArg Array.back? hn.1
        simpa using this.symm
      subst this
      rw [Array.getElem?_append_left (by simp)]
      rfl
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have := h3 j n hj
      rw [Array.getElem?_append_right (by simp)]
      simpa using this

end

/-- **A tree that names no definition spells element for element**
(`_exact`): no `defs`, and a raw element — a label's node — ships as
itself at its own index. -/
public theorem spell_plain_exact (ord : Nat) (els : Array El) (h : El.plainList els.toList = true)
    (j : Nat) (n : Html.Node) (hj : els[j]? = some (El.raw n)) : (spell ord els)[j]? = some n := by
  obtain ⟨hs, nodes, h1, _, h3⟩ := spellList_plain
    { ord := ord, clips := 0, grads := 0, defs := #[], syms := #[], outlines := #[] } #[] els.toList h
  have hj' : els.toList[j]? = some (El.raw n) := by simpa using hj
  simp only [spell]
  rw [hs]
  simp only [Array.isEmpty_empty, ↓reduceIte, h1, Array.empty_append]
  exact h3 j n hj'

/-- The element names a plain element spells into: geometry, groups and
images. A plain tree defines nothing, so these are all its own nodes. -/
@[expose] public def plainTags : List String := ["rect", "circle", "ellipse", "path", "g", "image"]

mutual

-- conserves: none — a predicate.
/-- Every raw node an element carries satisfies `q`. -/
@[expose] public def El.rawsAll (q : Html.Node → Bool) : El → Bool
  | .shape _ _ => true
  | .g _ _ _ kids => El.rawsAllList q kids.toList
  | .use _ _ body => El.rawsAllList q body.toList
  | .stamp _ _ _ _ => true
  | .image _ _ _ => true
  | .raw n => q n

@[expose] public def El.rawsAllList (q : Html.Node → Bool) : List El → Bool
  | [] => true
  | e :: rest => El.rawsAll q e && El.rawsAllList q rest

end

/-- A node property every plain SVG element has once its children have it. -/
@[expose] public def PlainClosed (q : Html.Node → Bool) : Prop :=
  ∀ t ∈ plainTags, ∀ (attrs : Array (String × String)) (kids : Array Html.Node),
    (∀ k ∈ kids, q k = true) → q (Html.elem t kids attrs) = true

private theorem geomEl_closed (q : Html.Node → Bool) (hq : PlainClosed q) (g : Geom)
    (attrs : Array (String × String)) : q (geomEl g attrs) = true := by
  have leaf (t : String) (ht : t ∈ plainTags) (a : Array (String × String)) :
      q (Html.elem t #[] a) = true := hq t ht a #[] (by simp)
  cases g with
  | rect x y w h => exact leaf "rect" (by simp [plainTags]) _
  | ellipse cx cy rx ry =>
    simp only [geomEl]
    split
    · exact leaf "circle" (by simp [plainTags]) _
    · exact leaf "ellipse" (by simp [plainTags]) _
  | path subs => exact leaf "path" (by simp [plainTags]) _

mutual

private theorem spellOne_closed (q : Html.Node → Bool) (hq : PlainClosed q) (sp : Spell) :
    ∀ (acc : Array Html.Node) (e : El), e.plain = true → e.rawsAll q = true →
      ∃ node, spellOne sp acc e = (acc.push node, sp) ∧ q node = true
  | acc, .shape g a, h, _ => by
    simp only [El.plain, Bool.and_eq_true] at h
    refine ⟨geomEl g (attrsSpell sp a).1, ?_, geomEl_closed q hq _ _⟩
    simp only [spellOne]
    rw [attrsSpell_plain sp a h.1 h.2]
  | acc, .g xf op clip kids, h, hr => by
    simp only [El.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨hc, hk⟩ := h
    subst hc
    simp only [El.rawsAll] at hr
    obtain ⟨hl, hall⟩ := spellList_closed q hq sp #[] kids.toList hk hr (by simp)
    refine ⟨Html.elem "g" (spellList sp #[] kids.toList).1
      ((match xf with
        | some m => #[transformAttr m]
        | none => #[]) ++
       (match op with
        | some a => #[("opacity", alphaSpell a)]
        | none => #[])), ?_, hq "g" (by simp [plainTags]) _ _ hall⟩
    simp only [spellOne]
    rw [hl]
  | _, .use _ _ _, h, _ => by simp [El.plain] at h
  | _, .stamp _ _ _ _, h, _ => by simp [El.plain] at h
  | acc, .image k m ref, _, _ =>
    ⟨Html.elem "image" #[] (#[("href", ref.href), ("width", "1"), ("height", "1"),
      ("preserveAspectRatio", "none"), transformAttr (m.compose unitFlip)] ++
        (if ref.smooth then #[] else #[("image-rendering", "pixelated")])),
      rfl, hq "image" (by simp [plainTags]) _ _ (by simp)⟩
  | acc, .raw n, _, hr => ⟨n, rfl, by simpa only [El.rawsAll] using hr⟩

private theorem spellList_closed (q : Html.Node → Bool) (hq : PlainClosed q) (sp : Spell) :
    ∀ (acc : Array Html.Node) (els : List El), El.plainList els = true →
      El.rawsAllList q els = true → (∀ n ∈ acc, q n = true) →
        (spellList sp acc els).2 = sp ∧ ∀ n ∈ (spellList sp acc els).1, q n = true
  | acc, [], _, _, ha => ⟨rfl, by simpa only [spellList] using ha⟩
  | acc, e :: rest, h, hr, ha => by
    simp only [El.plainList, Bool.and_eq_true] at h
    simp only [El.rawsAllList, Bool.and_eq_true] at hr
    obtain ⟨node, hn, hnode⟩ := spellOne_closed q hq sp acc e h.1 hr.1
    have he : spellList sp acc (e :: rest) = spellList sp (acc.push node) rest := by
      simp only [spellList, hn]
    rw [he]
    refine spellList_closed q hq sp (acc.push node) rest h.2 hr.2 fun n hm => ?_
    rcases Array.mem_push.mp hm with hm | rfl
    · exact ha n hm
    · exact hnode

end

/-- **A plain tree's spelling wraps its raw nodes in plain SVG**
(`_contract`): every node a tree that names no definition spells has any
property each plain SVG element has once its children do, as soon as the
tree's raw nodes have it — the spelling adds geometry, groups and images
around what a producer passed in, and nothing else. A picture's raw nodes
are its labels. -/
public theorem spell_plain_contract (q : Html.Node → Bool) (hq : PlainClosed q) (ord : Nat)
    (els : Array El) (h : El.plainList els.toList = true)
    (hr : El.rawsAllList q els.toList = true) : ∀ n ∈ spell ord els, q n = true := by
  obtain ⟨hs, hall⟩ := spellList_closed q hq
    { ord := ord, clips := 0, grads := 0, defs := #[], syms := #[], outlines := #[] } #[]
    els.toList h hr (by simp)
  simp only [spell]
  rw [hs]
  simpa only [Array.isEmpty_empty, ↓reduceIte] using hall

/-- The placement a standalone document draws a figure under: its box's
top-left corner at the origin, y down. -/
@[expose] public def documentIso (box : Box) : Iso :=
  { flipY := true, dx := -box.1.1, dy := box.2.2 }

/-- **A figure as a standalone SVG document's root**: spelled children in
the SVG namespace, the viewBox the figure's box in points from its
top-left corner, the size the same in `pt`, overflow hidden exactly when
the figure clips to its box. -/
public def documentRoot (box : Box) (clipToBox : Bool) (kids : Array Html.Node) : Html.Node :=
  let w := (box.2.1 - box.1.1).toPtString
  let h := (box.2.2 - box.1.2).toPtString
  Html.elem "svg" kids #[("xmlns", "http://www.w3.org/2000/svg"), ("viewBox", s!"0 0 {w} {h}"),
    ("width", s!"{w}pt"), ("height", s!"{h}pt"),
    ("overflow", if clipToBox then "hidden" else "visible")]

/-- A figure as a standalone SVG file: the XML declaration and its root. -/
public def document {L : Type} (labelEl : SFrame → L → Html.Node) (rasters : Array RasterRef)
    (fig : Figure L) : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
    Html.render (documentRoot fig.box fig.clipToBox
      (spell 0 (tree labelEl rasters (documentIso fig.box) fig))) 0

/-! ## Reading back -/

/-- SVG's initial fill colour. -/
@[expose] public def svgBlack : Ir.Color := { r := 0, g := 0, b := 0 }

/-- What a reader of the tree carries: the placement to undo while
coordinates are placed, the figure-frame matrix once a transform was read,
the clips and group opacities in force. -/
public structure SState where
  place : Iso
  placed : Bool
  ctm : Affine
  clips : Array (Affine × Clip)
  alphas : Array Alpha
  deriving Repr, Inhabited

/-- The map from the current user space to the figure frame: the
placement undone while coordinates are placed, else the transforms read. -/
@[expose] public def SState.userCtm (ss : SState) : Affine :=
  if ss.placed then ss.place.inv.toAffine else ss.ctm

/-- A paint attribute's value, read in the user space it stands in: a
gradient's `gradientTransform` composed through to the figure frame. -/
@[expose] public def readPaint (ss : SState) : SPaint → Option Paint
  | .none => none
  | .color c => some (.solid c)
  | .url g => some (.gradient (g.withXf (ss.userCtm.compose g.xf)))

/-- A shape's fill, read with SVG's initial values. -/
@[expose] public def readFill (ss : SState) (a : ShapeAttrs) : Option Fill :=
  let paint : Option Paint := match a.fill with
    | none => some (.solid svgBlack)
    | some p => readPaint ss p
  paint.map fun p => { paint := p, rule := a.fillRule.getD .nonzero
                       alpha := a.fillOpacity.getD Alpha.opaque }

/-- A shape's stroke, read with SVG's initial values: no stroke unless one
is named, width 1, and a zero width paints nothing. -/
@[expose] public def readStroke (ss : SState) (a : ShapeAttrs) : Option Stroke :=
  let width : Option Sp := match a.strokeWidth with
    | none => some svgUnit
    | some (.len w) => if w = 0 then none else some w
    | some .hairline => some 0
  match a.stroke.bind (readPaint ss), width with
  | some p, some w =>
    some { paint := p, width := w, cap := a.cap.getD .butt, join := a.join.getD .miter
           miterLimit := a.miter.getD svgMiter, dash := a.dash.getD #[]
           phase := a.dashOffset.getD 0, alpha := a.strokeOpacity.getD Alpha.opaque }
  | some _, none => none
  | none, _ => none

@[expose] public def SState.frameCtm (ss : SState) : Affine :=
  if ss.placed then Affine.unit else ss.ctm

/-- An element's geometry in the figure frame, as its drawing reads: an
ellipse is its four arcs. -/
@[expose] public def SState.geom (ss : SState) (g : Geom) : Geom :=
  (if ss.placed then g.mapIso ss.place.inv else g).normal

@[expose] public def SState.cm (ss : SState) : Option Affine → SState
  | none => ss
  | some m => { ss with placed := false, ctm := ss.userCtm.compose m }

/-- A `g`'s state: its transform, then its clip in the transformed frame,
then its opacity as one more isolated group. -/
@[expose] public def SState.enterG (ss : SState) (xf : Option Affine) (op : Option Alpha)
    (clip : Option ClipRef) : SState :=
  let s1 := ss.cm xf
  let s2 := match clip with
    | some c => { s1 with clips := s1.clips.push (s1.frameCtm, { geom := s1.geom c.geom, rule := c.rule }) }
    | none => s1
  match op with
  | some a => { s2 with alphas := s2.alphas.push a }
  | none => s2

mutual

-- conserves: none — a reader: `marks_projects` states what it reads.
/-- One element's marks, read with SVG's meaning; label content is not
ink. -/
@[expose] public def readOne (ss : SState) (acc : Array Mark) : El → Array Mark
  | .shape g a =>
    acc.push (.paint ss.frameCtm (ss.geom g) (readFill ss a) (readStroke ss a) ss.clips ss.alphas)
  | .g xf op clip kids => readList (ss.enterG xf op clip) acc kids.toList
  | .use _ xf body => readList (ss.cm (some xf)) acc body.toList
  | .stamp _ xf subs a =>
    let su := ss.cm (some xf)
    acc.push (.paint su.frameCtm (.path subs) (readFill su a) (readStroke su a) ss.clips ss.alphas)
  | .image k m _ => acc.push (.raster (ss.cm (some m)).frameCtm k ss.clips ss.alphas)
  | .raw _ => acc

@[expose] public def readList (ss : SState) (acc : Array Mark) : List El → Array Mark
  | [] => acc
  | e :: rest => readList ss (readOne ss acc e) rest

end

@[expose] public def SState.root (place : Iso) : SState :=
  { place := place, placed := true, ctm := Affine.unit, clips := #[], alphas := #[] }

/-- **What a typed SVG tree paints**, read with SVG's meaning. -/
@[expose] public def readMarks (place : Iso) (els : Array El) : Array Mark :=
  readList (SState.root place) #[] els.toList

/-! ## The reading is the figure's -/

/-- The model's reading context, the emitter's frame and the SVG reader's
state at one point of the tree. -/
private structure Agrees (place : Iso) (cx : Ctx) (fr : SFrame) (ss : SState) : Prop where
  hplace : ss.place = place
  hiso : fr.iso = if ss.placed then some place else none
  hctm : ss.frameCtm = cx.ctm
  hclips : ss.clips = cx.clips
  halphas : ss.alphas = cx.alphas

private theorem geom_agree (place : Iso) (fr : SFrame) (ss : SState) (hp : ss.place = place)
    (hi : fr.iso = if ss.placed then some place else none) (g : Geom) :
    ss.geom (fr.place g) = g.normal := by
  cases hpl : ss.placed
  · simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hi
    simp [SState.geom, SFrame.place, hpl, hi]
  · simp only [hpl, ↓reduceIte] at hi
    simp [SState.geom, SFrame.place, hpl, hi, hp, Geom.mapIso_inv_id]

/-- A paint spelled in a user space reads back as the paint under the frame
that user space's coordinates were lifted from. -/
private theorem readPaint_sPaint (ss : SState) (fr : SFrame) (m : Affine)
    (h : ∀ x, ss.userCtm.compose (fr.lift x) = m.compose x) (p : Paint) :
    readPaint ss (sPaint fr p) = some (p.under m) := by
  cases p with
  | solid c => rfl
  | gradient g =>
    simp only [sPaint, readPaint, Paint.under, Gradient.withXf_withXf, Gradient.xf_withXf, h]

private theorem readFill_attrsOf (ss : SState) (fr : SFrame) (m : Affine)
    (h : ∀ x, ss.userCtm.compose (fr.lift x) = m.compose x) (fl : Option Fill) (st : Option Stroke) :
    readFill ss (attrsOf fr fl st) = fl.map (Fill.under m) := by
  cases fl with
  | none => rfl
  | some f =>
    obtain ⟨p, r, a⟩ := f
    simp only [readFill, attrsOf, readPaint_sPaint ss fr m h, Option.map_some, Option.bind_some,
      Fill.under]
    congr 1
    simp only [Fill.mk.injEq, true_and]
    constructor
    · cases r <;> rfl
    · split
      · next h => exact h.symm
      · rfl

private theorem readStroke_attrsOf (ss : SState) (fr : SFrame) (m : Affine)
    (h : ∀ x, ss.userCtm.compose (fr.lift x) = m.compose x) (fl : Option Fill) (st : Option Stroke) :
    readStroke ss (attrsOf fr fl st) = st.map (Stroke.under m) := by
  cases st with
  | none => rfl
  | some s =>
    obtain ⟨p, w, cap, join, ml, dash, ph, a⟩ := s
    have hc : (match cap with
        | .butt => (none : Option Cap) | .round => some .round | .square => some .square).getD .butt
          = cap := by cases cap <;> rfl
    have hj : (match join with
        | .miter => (none : Option Join) | .round => some .round | .bevel => some .bevel).getD .miter
          = join := by cases join <;> rfl
    have hm : (if ml = svgMiter then none else some ml).getD svgMiter = ml := by
      split
      · next h => exact h.symm
      · rfl
    have hd : (if dash = #[] then none else some dash).getD #[] = dash := by
      split
      · next h => exact h.symm
      · rfl
    have hph : (if ph = 0 then none else some ph).getD 0 = ph := by
      split
      · next h => exact h.symm
      · rfl
    have ha : (if a = Alpha.opaque then none else some a).getD Alpha.opaque = a := by
      split
      · next h => exact h.symm
      · rfl
    have hp := readPaint_sPaint ss fr m h p
    by_cases hw : w = 0
    · simp [readStroke, attrsOf, hp, hw, hc, hj, hm, hd, hph, ha, Stroke.under]
    · simp [readStroke, attrsOf, hp, hw, hc, hj, hm, hd, hph, ha, Stroke.under]

/-- A read transform composes onto the user space's frame. -/
private theorem cm_some_frameCtm (ss : SState) (m : Affine) :
    (ss.cm (some m)).frameCtm = ss.userCtm.compose m := rfl

private theorem cm_lift_frameCtm (place : Iso) (cx : Ctx) (fr : SFrame) (ss : SState)
    (h : Agrees place cx fr ss) (xf : Affine) :
    (ss.cm (some (fr.lift xf))).frameCtm = cx.ctm.compose xf := by
  have hc := h.hctm
  rw [cm_some_frameCtm]
  cases hpl : ss.placed
  · have hi := h.hiso
    simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hi
    simp only [SState.frameCtm, hpl, Bool.false_eq_true, ↓reduceIte] at hc
    simp only [SState.userCtm, hpl, Bool.false_eq_true, ↓reduceIte, SFrame.lift, hi, hc]
  · have hi := h.hiso
    simp only [hpl, ↓reduceIte] at hi
    simp only [SState.frameCtm, hpl, ↓reduceIte] at hc
    simp only [SState.userCtm, hpl, ↓reduceIte, SFrame.lift, hi, h.hplace, ← hc]
    rw [← Affine.compose_assoc_exact, Iso.inv_compose_unit_id, (Affine.compose_unit_id xf).2]

/-- Where the three sides agree, the user space's coordinates were lifted
from the model's frame. -/
private theorem agrees_user (place : Iso) (cx : Ctx) (fr : SFrame) (ss : SState)
    (h : Agrees place cx fr ss) : ∀ x, ss.userCtm.compose (fr.lift x) = cx.ctm.compose x := fun x =>
  (cm_some_frameCtm ss _).symm.trans (cm_lift_frameCtm place cx fr ss h x)

/-- Inside a lifted transform, the user space is the new frame. -/
private theorem lift_user (place : Iso) (cx : Ctx) (fr : SFrame) (ss : SState)
    (h : Agrees place cx fr ss) (xf : Affine) :
    ∀ x, (ss.cm (some (fr.lift xf))).userCtm.compose (({ iso := none } : SFrame).lift x) =
      (cx.ctm.compose xf).compose x := fun x => by
  have := cm_lift_frameCtm place cx fr ss h xf
  simp only [SState.frameCtm, SState.cm] at this
  simp only [SState.userCtm, SState.cm, SFrame.lift, Bool.false_eq_true, ↓reduceIte] at this ⊢
  rw [this]

private theorem cm_group_frameCtm (place : Iso) (cx : Ctx) (fr : SFrame) (ss : SState)
    (h : Agrees place cx fr ss) (xf : Affine) :
    (ss.cm (groupXf fr xf)).frameCtm = cx.ctm.compose xf := by
  unfold groupXf
  split
  · next hx => simp only [SState.cm, h.hctm, hx, (Affine.compose_unit_id cx.ctm).1]
  · exact cm_lift_frameCtm place cx fr ss h xf

private theorem cm_place (ss : SState) (m : Option Affine) : (ss.cm m).place = ss.place := by
  cases m <;> rfl

private theorem cm_iso (place : Iso) (fr : SFrame) (ss : SState)
    (hi : fr.iso = if ss.placed then some place else none) (m : Option Affine) :
    (fr.enter m).iso = if (ss.cm m).placed then some place else none := by
  cases m with
  | none => exact hi
  | some _ => rfl

private theorem cm_keeps (ss : SState) (m : Option Affine) :
    (ss.cm m).clips = ss.clips ∧ (ss.cm m).alphas = ss.alphas := by
  cases m <;> exact ⟨rfl, rfl⟩

private theorem enter_alphas (cx : Ctx) (xf : Affine) (clips : Array Clip) :
    (cx.enter xf clips Alpha.opaque).alphas = cx.alphas := by
  simp [Ctx.enter]

private theorem agrees_lift (place : Iso) (cx : Ctx) (fr : SFrame) (ss : SState)
    (h : Agrees place cx fr ss) (xf : Affine) (fr' : SFrame) (hfr : fr'.iso = none) :
    Agrees place (cx.enter xf #[] Alpha.opaque) fr' (ss.cm (some (fr.lift xf))) where
  hplace := by simp [SState.cm, h.hplace]
  hiso := by simp [SState.cm, hfr]
  hctm := by rw [cm_lift_frameCtm place cx fr ss h xf]; rfl
  hclips := by simp [SState.cm, Ctx.enter, h.hclips]
  halphas := by rw [enter_alphas]; simp [SState.cm, h.halphas]

/-- The clips past the first read back as one more clip each, in the same
frame. -/
private theorem read_nestClips (place : Iso) (fr : SFrame) (inner : Array El) (acc : Array Mark) :
    ∀ (rest : List Clip) (ss : SState), ss.place = place →
      (fr.iso = if ss.placed then some place else none) →
      readList ss acc (nestClips fr inner rest).toList =
        readList { ss with clips := ss.clips ++ (rest.map fun c =>
          (ss.frameCtm, ({ c with geom := c.geom.normal } : Clip))).toArray } acc inner.toList
  | [], ss, _, _ => by simp [nestClips]
  | c :: rest, ss, hp, hi => by
    simp only [nestClips, List.toList_toArray, readList, readOne, SState.enterG, SState.cm]
    rw [read_nestClips place fr inner acc rest
      { ss with clips := ss.clips.push (ss.frameCtm, { geom := ss.geom (fr.place c.geom), rule := c.rule }) }
      hp hi]
    simp only [geom_agree place fr ss hp hi c.geom, List.map_cons]
    congr 2
    simp [SState.frameCtm]

/-- The state a group's body is read in: its transform and opacity, then
each of its clips in the transformed frame. -/
private def groupState (ss : SState) (t : Option Affine) (op : Option Alpha)
    (clips : List Clip) : SState :=
  let s := ss.enterG t op none
  { s with clips := s.clips ++ (clips.map fun c =>
      (s.frameCtm, ({ c with geom := c.geom.normal } : Clip))).toArray }

private theorem enter_clips_map (cx : Ctx) (xf : Affine) (clips : Array Clip) (alpha : Alpha) :
    (cx.enter xf clips alpha).clips =
      cx.clips ++ clips.map fun c => (cx.ctm.compose xf, { c with geom := c.geom.normal }) := rfl

private theorem enterG_none (ss : SState) (t : Option Affine) (op : Option Alpha) :
    (ss.enterG t op none).frameCtm = (ss.cm t).frameCtm ∧
      (ss.enterG t op none).place = (ss.cm t).place ∧
      (ss.enterG t op none).placed = (ss.cm t).placed ∧
      (ss.enterG t op none).clips = (ss.cm t).clips ∧
      (ss.enterG t op none).alphas = (match op with
        | some a => (ss.cm t).alphas.push a
        | none => (ss.cm t).alphas) := by
  cases op <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- After a group's transform, opacity and clips, the three sides agree. -/
private theorem agrees_group (place : Iso) (cx : Ctx) (fr : SFrame) (ss : SState)
    (h : Agrees place cx fr ss) (xf : Affine) (clips : Array Clip) (alpha : Alpha) :
    Agrees place (cx.enter xf clips alpha) (fr.enter (groupXf fr xf))
      (groupState ss (groupXf fr xf) (if alpha = Alpha.opaque then none else some alpha)
        clips.toList) := by
  have hct := cm_group_frameCtm place cx fr ss h xf
  have he := enterG_none ss (groupXf fr xf) (if alpha = Alpha.opaque then none else some alpha)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (ss.enterG _ _ none).place = _
    rw [he.2.1]; exact (cm_place ss _).trans h.hplace
  · show _ = if (ss.enterG _ _ none).placed then _ else _
    rw [he.2.2.1]; exact cm_iso place fr ss h.hiso _
  · show (if (ss.enterG _ _ none).placed then _ else (ss.enterG _ _ none).ctm) = _
    have : (ss.enterG (groupXf fr xf) (if alpha = Alpha.opaque then none else some alpha)
        none).frameCtm = cx.ctm.compose xf := he.1.trans hct
    exact this
  · show (ss.enterG _ _ none).clips ++ _ = _
    rw [enter_clips_map, he.2.2.2.1, (cm_keeps ss _).1, h.hclips, he.1, hct]
    congr 1
    apply Array.ext'
    simp
  · show (ss.enterG _ _ none).alphas = _
    rw [he.2.2.2.2, (cm_keeps ss _).2, h.halphas]
    by_cases ha : alpha = Alpha.opaque
    · simp [ha, Ctx.enter]
    · have hb : (alpha == Alpha.opaque) = false := by simpa using ha
      simp [ha, hb, Ctx.enter]

/-- A group's element reads back as its body read in the group's state. -/
private theorem read_group (place : Iso) (fr : SFrame) (ss : SState) (hp : ss.place = place)
    (hi : fr.iso = if ss.placed then some place else none) (xf : Affine) (clips : Array Clip)
    (op : Option Alpha) (inner : Array El) (acc : Array Mark) :
    readOne ss acc (.g (groupXf fr xf) op none (nestClips (fr.enter (groupXf fr xf)) inner clips.toList)) =
      readList (groupState ss (groupXf fr xf) op clips.toList) acc inner.toList := by
  have he := enterG_none ss (groupXf fr xf) op
  simp only [readOne]
  rw [read_nestClips place (fr.enter (groupXf fr xf)) inner acc clips.toList _
    (by rw [he.2.1, cm_place, hp]) (by rw [he.2.2.1]; exact cm_iso place fr ss hi _)]
  rfl

private theorem readList_append (ss : SState) (acc : Array Mark) (a b : List El) :
    readList ss acc (a ++ b) = readList ss (readList ss acc a) b := by
  induction a generalizing acc with
  | nil => rfl
  | cons o rest ih => simp [readList, ih]

mutual

public theorem treeOne_acc {L : Type} (labelEl : SFrame → L → Html.Node)
    (outlines : Array (Array Subpath)) (rasters : Array RasterRef) (bodies : Array (Array El))
    (fr : SFrame) (acc : Array El) (n : Node L) :
    treeOne labelEl outlines rasters bodies fr acc n =
      acc ++ treeOne labelEl outlines rasters bodies fr #[] n := by
  cases n with
  | use k xf =>
    simp only [treeOne]
    split <;> simp
  | draw | group | stamp | image | label | words => simp [treeOne]

public theorem treeList_acc {L : Type} (labelEl : SFrame → L → Html.Node)
    (outlines : Array (Array Subpath)) (rasters : Array RasterRef) (bodies : Array (Array El))
    (fr : SFrame) (acc : Array El) (xs : List (Node L)) :
    treeList labelEl outlines rasters bodies fr acc xs =
      acc ++ treeList labelEl outlines rasters bodies fr #[] xs := by
  match xs with
  | [] => simp [treeList]
  | n :: rest =>
    simp only [treeList]
    rw [treeList_acc labelEl outlines rasters bodies fr _ rest,
      treeList_acc labelEl outlines rasters bodies fr
        (treeOne labelEl outlines rasters bodies fr #[] n) rest,
      treeOne_acc labelEl outlines rasters bodies fr acc n, Array.append_assoc]

end

private theorem agrees_plainGeom (place : Iso) (cx : Ctx) (fr : SFrame) (ss : SState)
    (h : Agrees place cx fr ss) (g : Geom) : ss.geom (fr.place g) = g.normal :=
  geom_agree place fr ss h.hplace h.hiso g

mutual

private theorem read_treeOne_free {L : Type} (labelEl : SFrame → L → Html.Node)
    (outlines : Array (Array Subpath)) (rasters : Array RasterRef) (bodies : Array (Array El))
    (place : Iso) :
    ∀ (n : Node L) (cx : Ctx) (fr : SFrame) (ss : SState) (acc : Array Mark),
      n.useFree = true → Agrees place cx fr ss →
      readList ss acc (treeOne labelEl outlines rasters bodies fr #[] n).toList =
        Node.marksOne outlines cx acc n
  | .draw g fl st, cx, fr, ss, acc, _, h => by
    simp only [treeOne, Array.toList_push, List.nil_append, readList, readOne, Node.marksOne,
      agrees_plainGeom place cx fr ss h g,
      readFill_attrsOf ss fr cx.ctm (agrees_user place cx fr ss h),
      readStroke_attrsOf ss fr cx.ctm (agrees_user place cx fr ss h), h.hctm, h.hclips, h.halphas]
  | .group xf clips alpha kids, cx, fr, ss, acc, hu, h => by
    simp only [Node.useFree] at hu
    simp only [treeOne, Array.toList_push, List.nil_append, readList, Node.marksOne]
    rw [read_group place fr ss h.hplace h.hiso xf clips _ _ acc]
    exact read_treeList_free labelEl outlines rasters bodies place kids.toList _ _ _ acc hu
      (agrees_group place cx fr ss h xf clips alpha)
  | .use _ _, _, _, _, _, hu, _ => by simp [Node.useFree] at hu
  | .stamp o xf fl st, cx, fr, ss, acc, _, h => by
    simp only [treeOne, Array.toList_push, List.nil_append, readList, readOne, Node.marksOne,
      readFill_attrsOf _ _ _ (lift_user place cx fr ss h xf),
      readStroke_attrsOf _ _ _ (lift_user place cx fr ss h xf), cm_lift_frameCtm place cx fr ss h xf,
      h.hclips, h.halphas]
  | .image k xf, cx, fr, ss, acc, _, h => by
    simp only [treeOne, Array.toList_push, List.nil_append, readList, readOne, Node.marksOne,
      cm_lift_frameCtm place cx fr ss h xf, h.hclips, h.halphas]
  | .label l, cx, fr, ss, acc, _, _ => by
    simp [treeOne, readList, readOne, Node.marksOne]
  | .words _, cx, fr, ss, acc, _, _ => by
    simp [treeOne, readList, Node.marksOne]

private theorem read_treeList_free {L : Type} (labelEl : SFrame → L → Html.Node)
    (outlines : Array (Array Subpath)) (rasters : Array RasterRef) (bodies : Array (Array El))
    (place : Iso) :
    ∀ (xs : List (Node L)) (cx : Ctx) (fr : SFrame) (ss : SState) (acc : Array Mark),
      Node.useFreeList xs = true → Agrees place cx fr ss →
      readList ss acc (treeList labelEl outlines rasters bodies fr #[] xs).toList =
        Node.marksList outlines cx acc xs
  | [], _, _, _, _, _, _ => by simp [treeList, readList, Node.marksList]
  | n :: rest, cx, fr, ss, acc, hu, h => by
    simp only [Node.useFreeList, Bool.and_eq_true] at hu
    simp only [treeList, Node.marksList]
    rw [treeList_acc, Array.toList_append, readList_append,
      read_treeOne_free labelEl outlines rasters bodies place n cx fr ss acc hu.1 h,
      read_treeList_free labelEl outlines rasters bodies place rest cx fr ss _ hu.2 h]

end

private theorem agrees_root (place : Iso) :
    Agrees place Ctx.root { iso := some place } (SState.root place) where
  hplace := rfl
  hiso := rfl
  hctm := rfl
  hclips := rfl
  halphas := rfl

mutual

private theorem read_treeOne {L : Type} (labelEl : SFrame → L → Html.Node) (rasters : Array RasterRef)
    (fig : Figure L) (place : Iso) :
    ∀ (n : Node L) (cx : Ctx) (fr : SFrame) (ss : SState) (acc : Array Mark),
      Agrees place cx fr ss →
      readList ss acc
          (treeOne labelEl fig.outlines rasters (bodyEls labelEl rasters fig) fr #[] n).toList =
        Node.marksList fig.outlines cx acc
          (Node.expandOne fig.bodies fig.bodies.size #[] n).toList
  | .draw g fl st, cx, fr, ss, acc, h => by
    have := read_treeOne_free labelEl fig.outlines rasters (bodyEls labelEl rasters fig) place
      (.draw g fl st) cx fr ss acc rfl h
    simpa [Node.expandOne, Node.marksList] using this
  | .group xf clips alpha kids, cx, fr, ss, acc, h => by
    simp only [treeOne, Node.expandOne, Array.toList_push, List.nil_append, readList,
      Node.marksList, Node.marksOne]
    rw [read_group place fr ss h.hplace h.hiso xf clips _ _ acc]
    exact read_treeList labelEl rasters fig place kids.toList _ _ _ acc
      (agrees_group place cx fr ss h xf clips alpha)
  | .use k xf, cx, fr, ss, acc, h => by
    simp only [treeOne, Node.expandOne, bodyEls, Array.getElem?_map]
    by_cases hk : k < fig.bodies.size
    · have hb : fig.bodies[k]? = some fig.bodies[k] := Array.getElem?_eq_getElem hk
      simp only [hk, ↓reduceIte, hb, Option.map_some, Array.toList_push, List.nil_append,
        readList, readOne, Node.marksList, Node.marksOne]
      exact read_treeList_free labelEl fig.outlines rasters #[] place _ _ { iso := none } _ acc
        (Figure.bodies_useFree_covers fig _ (Array.getElem_mem hk))
        (agrees_lift place cx fr ss h xf { iso := none } rfl)
    · simp [hk, readList, Node.marksList]
  | .stamp o xf fl st, cx, fr, ss, acc, h => by
    have := read_treeOne_free labelEl fig.outlines rasters (bodyEls labelEl rasters fig) place
      (.stamp o xf fl st) cx fr ss acc rfl h
    simpa [Node.expandOne, Node.marksList] using this
  | .image k xf, cx, fr, ss, acc, h => by
    have := read_treeOne_free labelEl fig.outlines rasters (bodyEls labelEl rasters fig) place
      (.image k xf) cx fr ss acc rfl h
    simpa [Node.expandOne, Node.marksList] using this
  | .label l, cx, fr, ss, acc, h => by
    have := read_treeOne_free labelEl fig.outlines rasters (bodyEls labelEl rasters fig) place
      (.label l) cx fr ss acc rfl h
    simpa [Node.expandOne, Node.marksList] using this
  | .words w, cx, fr, ss, acc, h => by
    have := read_treeOne_free labelEl fig.outlines rasters (bodyEls labelEl rasters fig) place
      (.words w) cx fr ss acc rfl h
    simpa [Node.expandOne, Node.marksList] using this

private theorem read_treeList {L : Type} (labelEl : SFrame → L → Html.Node) (rasters : Array RasterRef)
    (fig : Figure L) (place : Iso) :
    ∀ (xs : List (Node L)) (cx : Ctx) (fr : SFrame) (ss : SState) (acc : Array Mark),
      Agrees place cx fr ss →
      readList ss acc
          (treeList labelEl fig.outlines rasters (bodyEls labelEl rasters fig) fr #[] xs).toList =
        Node.marksList fig.outlines cx acc
          (Node.expandList fig.bodies fig.bodies.size #[] xs).toList
  | [], _, _, _, _, _ => by simp [treeList, readList, Node.expandList, Node.marksList]
  | n :: rest, cx, fr, ss, acc, h => by
    simp only [treeList, Node.expandList]
    rw [treeList_acc, Array.toList_append, readList_append, Node.expandList_acc,
      Array.toList_append, Node.marksList_append, read_treeOne labelEl rasters fig place n cx fr ss acc h,
      read_treeList labelEl rasters fig place rest cx fr ss _ h]

end

/-- **What the SVG says is what the figure paints** (`_projects`): the typed
tree `tree` builds, read with SVG's meaning — fill initially black, stroke
initially none, width 1, miter limit 4, a zero width painting nothing,
transforms composing, clips in the transformed frame, group opacity
isolated — is the figure's marks, for every figure, placement and label
setter, before a byte is spelled. The other half of `backend_marks_agree`:
an attribute the emitter leaves out is SVG's initial value the figure asked
for, and an attribute it states — the miter limit 10, the hairline — is
there because SVG's would differ. -/
public theorem marks_projects {L : Type} (labelEl : SFrame → L → Html.Node)
    (rasters : Array RasterRef) (place : Iso) (fig : Figure L) :
    readMarks place (tree labelEl rasters place fig) = fig.marks := by
  unfold readMarks tree Figure.marks Figure.expanded
  exact read_treeList labelEl rasters fig place fig.nodes.toList Ctx.root _ (SState.root place) #[]
    (agrees_root place)

end LeanTex.Core.GfxSvg
