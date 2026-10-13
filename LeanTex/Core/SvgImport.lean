module

public import LeanTex.Core.Gfx
public import LeanTex.Core.Xml
public import LeanTex.Core.Css
public import LeanTex.Core.CssColor
public import LeanTex.Core.PathData
public import LeanTex.Core.SvgJudge
import LeanTex.Core.Image
public import Std.Data.HashMap

/-!
# SVG as a vector figure

An accepted SVG tree (`Svg.judge`) read into the vector model: the root
viewport is the figure's box and clips it; every element the importer reads
becomes the draws, groups, symbol uses, rasters and text runs both backends
emit (`GfxPdf`, `GfxSvg`). Coordinates are the SVG's own user space, y down,
in `Sp` at one CSS pixel — 0.75 pt — per user unit, rounded once; matrices
are exact rationals, and the root group carries the flip into the figure's
y-up frame together with the viewBox transform (SVG 2 §8.2).

What the importer reads: `svg` (nested viewports, `viewBox`,
`preserveAspectRatio`, every absolute and relative unit), `g`, `defs`,
`symbol`, `use`, `switch`, `a` (drawn, its link dropped with a note),
`path`, `rect` (`rx`/`ry`), `circle`, `ellipse`, `line`, `polyline`,
`polygon`, `linearGradient` and `radialGradient` (href chains, both unit
systems, `gradientTransform`, pad), `clipPath` (both unit systems), `image`
(a `data:` PNG or JPEG), `text` and `tspan`, `title`, `desc`, `metadata`,
`style`; the fill, stroke and opacity families, `transform`, `clip-path`,
`display`, `visibility`, `color`, the font properties and `text-anchor`,
through the CSS cascade (`Css`).

What it meets and cannot give this meaning is a keyed loss (`Gfx.Loss`):
filters, masks, patterns, markers, a translucent gradient stop, a reflected
or repeated spread, blend modes, text on a path, `vector-effect`,
`paint-order`, CSS outside the subset. A figure with no loss is exact;
that an exact figure also *looks* the same is the oracles' claim
(`scripts/svg-diff.lean`), not a theorem.

`use` is expanded without recursion through the reference: the walk records
each reference as a request and paints a symbol use; the requests are read
one by one, each a walk of its own, under a request budget; and the symbols
are then ordered so that a body uses only symbols before it, as the model
requires (`Figure.wf`). A reference cycle is a loss, and so is a request
past the budget.
-/

namespace LeanTex.Core.Svg

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Gfx

/-! ## Units and numbers -/

/-- One user unit, the CSS pixel, in `Sp`: 0.75 pt. -/
@[expose] public def pxSp : Int := 49152

/-- A length's unit (CSS Values 4 §5–§6): a bare number is in user units. -/
public inductive LenUnit where
  | user
  | px
  | pt
  | pc
  | mm
  | cm
  | inch
  | em
  | ex
  | pct
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How many CSS pixels one unit is, exactly (CSS Values 4 §6.2: 96 px to
the inch); the font- and box-relative units are their caller's. -/
@[expose] public def LenUnit.factor : LenUnit → Rat
  | .user => 1
  | .px => 1
  | .pt => 4 / 3
  | .pc => 16
  | .mm => 480 / 127
  | .cm => 4800 / 127
  | .inch => 96
  | .em => 1
  | .ex => 1
  | .pct => 1

/-- The suffix a unit is spelled with. -/
@[expose] public def LenUnit.suffix : LenUnit → String
  | .user => ""
  | .px => "px"
  | .pt => "pt"
  | .pc => "pc"
  | .mm => "mm"
  | .cm => "cm"
  | .inch => "in"
  | .em => "em"
  | .ex => "ex"
  | .pct => "%"

@[expose] public def LenUnit.ofSuffix (s : String) : Option LenUnit :=
  match s.toLower with
  | "" => some .user
  | "px" => some .px
  | "pt" => some .pt
  | "pc" => some .pc
  | "mm" => some .mm
  | "cm" => some .cm
  | "in" => some .inch
  | "em" => some .em
  | "ex" => some .ex
  | "%" => some .pct
  | _ => none

/-- A length as spelled: a decimal and its unit. -/
public structure Length where
  value : Rat
  unit : LenUnit
  deriving Repr, BEq, Inhabited

/-- A number alone, white space around it allowed. -/
public def num? (s : String) : Option Rat :=
  (PathData.number (PathData.skipWs s.toList)).bind fun (d, rest) =>
    if (PathData.skipWs rest).isEmpty then some d.toRat else none

/-- **A length**: a decimal, then a unit suffix, white space around it. -/
@[expose] public def length? (s : String) : Option Length :=
  (PathData.number (PathData.skipWs s.toList)).bind fun (d, rest) =>
    let suffix := String.ofList (rest.takeWhile (!PathData.isWsp ·))
    if (PathData.skipWs (rest.dropWhile (!PathData.isWsp ·))).isEmpty then
      (LenUnit.ofSuffix suffix).map fun u => { value := d.toRat, unit := u }
    else none

/-- A length in CSS pixels, against the font size `em` and the percentage
basis `base` (both in pixels): `1ex` is half an em, as CSS's fallback
reads it when no font is consulted. -/
@[expose] public def Length.toPx (l : Length) (em base : Rat) : Rat :=
  match l.unit with
  | .em => l.value * em
  | .ex => l.value * em / 2
  | .pct => l.value * base / 100
  | u => l.value * u.factor

/-- Pixels as `Sp` of user space, rounded once, half away from zero. -/
@[expose] public def spOf (px : Rat) : Sp :=
  let v := px * (pxSp : Rat)
  let n := v.num
  let d := (v.den : Int)
  if n < 0 then -((-n * 2 + d) / (2 * d)) else (n * 2 + d) / (2 * d)

/-- Numbers separated by white space and commas. -/
public def numList? (s : String) : Option (Array Rat) := Id.run do
  let mut acc : Array Rat := #[]
  let mut cs := PathData.skipWs s.toList
  for _ in [0:s.length + 1] do
    if cs.isEmpty then return some acc
    match PathData.number cs with
    | some (d, rest) =>
      acc := acc.push d.toRat
      cs := PathData.skipSep rest
    | none => return none
  return none

/-- Lengths separated by white space and commas. -/
public def lengthList? (s : String) : Option (Array Length) :=
  let parts := (s.replace "," " ").splitOn " " |>.filter (!·.trimAscii.isEmpty)
  parts.toArray.mapM length?

/-! ## Transforms -/

/-- A rotation by `deg` degrees: CORDIC's cosine and sine at 2⁻³⁰, exact on
every multiple of a right angle (`Trig.cosSin`). -/
public def rotation (deg : Rat) : Affine :=
  let θ := Trig.divRound (deg.num * Trig.pi) (180 * (deg.den : Int))
  let (c, s) := Trig.cosSin θ
  let u : Rat := (Trig.unit : Rat)
  ⟨(c : Rat) / u, (s : Rat) / u, -(s : Rat) / u, (c : Rat) / u, 0, 0⟩

/-- `tan` of `deg` degrees, from the same CORDIC pair. -/
public def tangentOf (deg : Rat) : Rat :=
  let θ := Trig.divRound (deg.num * Trig.pi) (180 * (deg.den : Int))
  let (c, s) := Trig.cosSin θ
  if c == 0 then 0 else (s : Rat) / (c : Rat)

/-- A translation by user units. -/
@[expose] public def shift (x y : Rat) : Affine := ⟨1, 0, 0, 1, x * (pxSp : Rat), y * (pxSp : Rat)⟩

/-- One transform function (SVG 2 §8.5 / SVG 1.1 §7.6), its arguments in
user units. -/
public def transformFn (name : String) (args : Array Rat) : Option Affine :=
  match name, args.toList with
  | "matrix", [a, b, c, d, e, f] => some ⟨a, b, c, d, e * (pxSp : Rat), f * (pxSp : Rat)⟩
  | "translate", [x] => some (shift x 0)
  | "translate", [x, y] => some (shift x y)
  | "scale", [s] => some (Affine.scale s s)
  | "scale", [x, y] => some (Affine.scale x y)
  | "rotate", [a] => some (rotation a)
  | "rotate", [a, cx, cy] => some ((shift cx cy).compose ((rotation a).compose (shift (-cx) (-cy))))
  | "skewX", [a] => some ⟨1, 0, tangentOf a, 1, 0, 0⟩
  | "skewY", [a] => some ⟨1, tangentOf a, 0, 1, 0, 0⟩
  | _, _ => none

/-- **A transform list**, composed left to right: the first function is the
outermost. An unreadable list is no transform. Read in one pass over the
text, each function a name, `(`, its numbers and `)`, separated by white
space and commas. -/
public def transform? (s : String) : Option Affine := Id.run do
  let cs := s.toList.toArray
  let n := cs.size
  let sep (c : Char) : Bool := c == ',' || PathData.isWsp c
  let mut m := Affine.unit
  let mut i := 0
  for _ in [0:n + 1] do
    for _ in [0:n + 1] do
      if i < n && sep (cs[i]?.getD ' ') then i := i + 1 else break
    if n ≤ i then return some m
    let start := i
    for _ in [0:n + 1] do
      if i < n && (cs[i]?.getD ' ').isAlpha then i := i + 1 else break
    let name := String.ofList (cs.extract start i).toList
    for _ in [0:n + 1] do
      if i < n && PathData.isWsp (cs[i]?.getD ' ') then i := i + 1 else break
    unless cs[i]? == some '(' do return none
    let open_ := i
    for _ in [0:n + 1] do
      if i < n && cs[i]? != some ')' then i := i + 1 else break
    unless cs[i]? == some ')' do return none
    let some args := numList? (String.ofList (cs.extract (open_ + 1) i).toList) | return none
    let some f := transformFn name args | return none
    m := m.compose f
    i := i + 1
  return none

/-- The inverse of an affine map, when it has one. -/
public def Affine.inverse? (m : Affine) : Option Affine :=
  let det := m.a * m.d - m.b * m.c
  if det == 0 then none else
  let a := m.d / det
  let b := -m.b / det
  let c := -m.c / det
  let d := m.a / det
  some ⟨a, b, c, d, -(a * m.e + c * m.f), -(b * m.e + d * m.f)⟩

/-! ## Viewports -/

/-- A `viewBox`: its origin and extents in user units. -/
public structure ViewBox where
  x : Rat
  y : Rat
  w : Rat
  h : Rat
  deriving Repr, BEq, Inhabited

public def viewBox? (s : String) : Option ViewBox :=
  match (numList? s).map (·.toList) with
  | some [x, y, w, h] => if 0 < w && 0 < h then some { x := x, y := y, w := w, h := h } else none
  | _ => none

/-- An alignment along one axis. -/
public inductive Align where
  | min
  | mid
  | max
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `preserveAspectRatio` (SVG 2 §8.3): `none`, or an alignment on each axis
and whether to slice rather than meet. -/
public structure Par where
  align : Option (Align × Align)
  slice : Bool
  deriving Repr, BEq, Inhabited

@[expose] public def Par.default : Par := { align := some (.mid, .mid), slice := false }

public def par? (s : String) : Par :=
  match (s.trimAscii.toString.splitOn " ").filter (!·.isEmpty) with
  | a :: rest =>
    let slice := rest.contains "slice"
    let ax (c : String) : Option Align :=
      if c == "Min" then some .min else if c == "Mid" then some .mid else if c == "Max" then some .max
      else none
    if a == "none" then { align := none, slice := false }
    else if a.length == 8 && a.startsWith "x" then
      match ax ((a.drop 1).take 3).toString, ax ((a.drop 5).take 3).toString with
      | some x, some y => { align := some (x, y), slice }
      | _, _ => Par.default
    else Par.default
  | [] => Par.default

/-- The offset an alignment puts a box of extent `used` at inside `avail`. -/
@[expose] public def Align.offset (a : Align) (avail used : Rat) : Rat :=
  match a with
  | .min => 0
  | .mid => (avail - used) / 2
  | .max => avail - used

/-- **The viewBox transform** (SVG 2 §8.2), in pixels: the scale on each
axis — equal unless `none` — and the translation that puts the viewBox's
origin at the aligned corner of the viewport `(vx, vy, vw, vh)`. -/
@[expose] public def viewScale (vb : ViewBox) (p : Par) (vw vh : Rat) : Rat × Rat :=
  let sx := vw / vb.w
  let sy := vh / vb.h
  match p.align with
  | none => (sx, sy)
  | some _ =>
    let s := if p.slice then (if sx < sy then sy else sx) else (if sx < sy then sx else sy)
    (s, s)

@[expose] public def viewMap (vb : ViewBox) (p : Par) (vx vy vw vh : Rat) : Affine :=
  let (sx, sy) := viewScale vb p vw vh
  let (ox, oy) : Rat × Rat := match p.align with
    | none => (0, 0)
    | some (ax, ay) => (ax.offset vw (vb.w * sx), ay.offset vh (vb.h * sy))
  ⟨sx, 0, 0, sy, (vx + ox - vb.x * sx) * (pxSp : Rat), (vy + oy - vb.y * sy) * (pxSp : Rat)⟩

/-- The viewport a percentage reads: its width and height in pixels. -/
public structure Viewport where
  w : Rat
  h : Rat
  deriving Repr, BEq, Inhabited

/-- The normalized diagonal a percentage of no axis reads (SVG 2 §8.9):
√((w² + h²)/2), to a thousandth of a pixel. -/
public def Viewport.diag (vp : Viewport) : Rat :=
  let q := (vp.w * vp.w + vp.h * vp.h) / 2
  let scaled := (q * 1000000).floor.toNat
  ((Nat.sqrt scaled : Nat) : Rat) / 1000

/-! ## Paints and styles -/

/-- A paint as the cascade leaves it (SVG 2 §13.2): none, a colour with its
alpha, the `color` property's, or a paint server with its fallback. -/
public inductive PaintSpec where
  | none
  | color (c : Ir.Color) (alpha : Nat)
  | current
  | url (id : String) (fallback : Option PaintSpec)
  deriving Repr, Inhabited, BEq

@[expose] public def black : Ir.Color := { r := 0, g := 0, b := 0 }

/-- The inherited properties the importer reads, computed. -/
public structure Style where
  fill : PaintSpec
  fillOpacity : Nat
  fillRule : Rule
  stroke : PaintSpec
  strokeOpacity : Nat
  strokeWidth : Sp
  cap : Cap
  join : Join
  miter : Rat
  dash : Array Sp
  dashOffset : Sp
  color : Ir.Color × Nat
  visible : Bool
  families : Array String
  fontSize : Rat
  weight : Nat
  italic : Bool
  anchor : Anchor
  clipRule : Rule
  smooth : Bool
  preserve : Bool
  lang : Option String
  deriving Repr, Inhabited, BEq

/-- The initial values (SVG 2 §13, CSS Fonts 4): black fill, no stroke, a
one-pixel butt-capped miter-joined stroke at limit 4, a 16 px serif face. -/
@[expose] public def Style.initial : Style :=
  { fill := .color black 1000, fillOpacity := 1000, fillRule := .nonzero, stroke := .none
    strokeOpacity := 1000, strokeWidth := pxSp, cap := .butt, join := .miter, miter := 4
    dash := #[], dashOffset := 0, color := (black, 1000), visible := true
    families := #["serif"], fontSize := 16, weight := 400, italic := false, anchor := .start
    clipRule := .nonzero, smooth := true, preserve := false, lang := none }

/-- An element's declarations, every source of the cascade: property,
key, value. -/
public abbrev Decls := Array (String × Css.Key × String)

/-- How the importer treats a property it meets: read with its meaning
(`honoured`); `inert` where nothing the figure paints reads it — a
rendering hint, a filter primitive's input when filters are a loss, a
property only a lost feature reads, interaction; or a loss unless the
value is one of those that change nothing (`lossUnless`, lower case; the
CSS-wide keywords change nothing a parent did not already say). -/
public inductive Treatment where
  | honoured
  | inert
  | lossUnless (harmless : List String)
  deriving Repr, BEq, Inhabited

/-- **Every property the importer reads or reports, and how** (SVG 2 §6.6
and the CSS modules it names): the one table the presentation attributes,
the loss census and the treatment check (`propertyTreatmentChecks`) read.
A property missing here is one SVG does not apply to these elements, or
one a sheet may set only as `cssLost` names. -/
@[expose] public def propertyTable : List (String × Treatment) :=
  [("fill", .honoured), ("fill-opacity", .honoured), ("fill-rule", .honoured),
   ("stroke", .honoured), ("stroke-width", .honoured), ("stroke-linecap", .honoured),
   ("stroke-linejoin", .lossUnless ["miter", "round", "bevel"]),
   ("stroke-miterlimit", .honoured), ("stroke-dasharray", .honoured),
   ("stroke-dashoffset", .honoured), ("stroke-opacity", .honoured), ("opacity", .honoured),
   ("color", .honoured), ("display", .honoured), ("visibility", .honoured),
   ("clip-path", .honoured), ("clip-rule", .honoured), ("font-family", .honoured),
   ("font-size", .honoured), ("font-weight", .honoured), ("font-style", .honoured),
   ("font", .lossUnless []), ("text-anchor", .honoured), ("stop-color", .honoured),
   ("stop-opacity", .honoured), ("overflow", .honoured), ("image-rendering", .honoured),
   ("transform-origin", .honoured),
   ("mask", .lossUnless ["none"]), ("filter", .lossUnless ["none"]),
   ("marker-start", .lossUnless ["none"]), ("marker-mid", .lossUnless ["none"]),
   ("marker-end", .lossUnless ["none"]), ("marker", .lossUnless ["none"]),
   ("mix-blend-mode", .lossUnless ["normal"]),
   ("paint-order", .lossUnless ["normal", "fill", "fill stroke", "fill stroke markers"]),
   ("vector-effect", .lossUnless ["none"]), ("text-decoration", .lossUnless ["none"]),
   ("letter-spacing", .lossUnless ["normal", "0", "0px"]),
   ("word-spacing", .lossUnless ["normal", "0", "0px"]),
   ("baseline-shift", .lossUnless ["baseline", "0", "0px"]),
   ("dominant-baseline", .lossUnless ["auto", "alphabetic"]),
   ("alignment-baseline", .lossUnless ["auto", "baseline", "alphabetic"]),
   ("writing-mode", .lossUnless ["horizontal-tb", "lr", "lr-tb"]),
   ("direction", .lossUnless ["ltr"]), ("font-variant", .lossUnless ["normal"]),
   ("font-stretch", .lossUnless ["normal", "100%"]),
   ("font-size-adjust", .lossUnless ["none"]),
   ("color-interpolation", .lossUnless ["auto", "srgb"]),
   ("unicode-bidi", .lossUnless ["normal"]), ("white-space", .lossUnless ["normal", "nowrap"]),
   ("transform-box", .lossUnless ["view-box"]),
   ("glyph-orientation-horizontal", .lossUnless ["0", "0deg"]),
   ("kerning", .lossUnless ["auto"]), ("clip", .lossUnless ["auto"]),
   ("inline-size", .lossUnless ["0", "0px", "auto"]),
   ("shape-inside", .lossUnless ["none", "auto"]), ("shape-padding", .lossUnless ["0", "0px"]),
   ("shape-margin", .lossUnless ["0", "0px"]),
   ("shape-rendering", .inert), ("text-rendering", .inert), ("color-rendering", .inert),
   ("color-interpolation-filters", .inert), ("pointer-events", .inert), ("cursor", .inert),
   ("isolation", .inert), ("flood-color", .inert), ("flood-opacity", .inert),
   ("lighting-color", .inert), ("enable-background", .inert), ("text-overflow", .inert),
   ("mask-type", .inert), ("solid-color", .inert), ("solid-opacity", .inert),
   ("glyph-orientation-vertical", .inert), ("line-height", .inert)]

/-- The properties a presentation attribute may set (SVG 2 §6.6), that this
importer reads or reports. -/
@[expose] public def properties : List String := propertyTable.map (·.1)

/-- The properties a style sheet or `style` attribute may set that the
importer reads only as attributes, or not at all — the geometry properties
(SVG 2 §10.1.1, §9.2), the CSS transform with its individual and motion
properties, a mask's longhands — each with the values that change nothing.
A declaration of one from CSS with another value is a loss: a geometry
property's initial value still overrides the attribute it shadows. -/
@[expose] public def cssLost : List (String × List String) :=
  (["x", "y", "width", "height", "cx", "cy", "r", "rx", "ry", "d"].map (·, [])) ++
  (["transform", "translate", "rotate", "scale", "offset-path", "mask-image",
    "backdrop-filter"].map (·, ["none"])) ++
  (["offset", "offset-distance", "offset-rotate", "offset-anchor", "offset-position",
    "mask-mode", "mask-position", "mask-size", "mask-repeat", "mask-origin", "mask-clip",
    "mask-composite"].map (·, []))

/-- The system font keywords: a face only the host names. -/
@[expose] public def systemFonts : List String :=
  ["caption", "icon", "menu", "message-box", "small-caption", "status-bar"]

/-- **The longhands a `font` shorthand sets** (CSS Fonts 4 §2.7), each one
it leaves unsaid reset to its initial value — style, variant, weight and
width before the size, an optional line height after it, the family list
last; `none` where the value is no shorthand this reader reads, a system
font keyword among them. -/
public def fontShorthand? (v : String) : Option (Array (String × String)) := Id.run do
  let t := v.trimAscii.toString
  let lower := t.toLower
  if ["inherit", "initial", "unset"].contains lower then
    return some (#["font-style", "font-variant", "font-weight", "font-stretch", "font-size",
      "line-height", "font-family"].map (·, lower))
  if systemFonts.contains lower then return none
  let styles := ["italic", "oblique"]
  let weights := ["bold", "bolder", "lighter"]
  let widths := ["ultra-condensed", "extra-condensed", "condensed", "semi-condensed",
    "semi-expanded", "expanded", "extra-expanded", "ultra-expanded"]
  let sizes := ["xx-small", "x-small", "small", "medium", "large", "x-large", "xx-large",
    "xxx-large", "smaller", "larger"]
  let isSize (s : String) : Bool :=
    sizes.contains s.toLower || (match length? s with
      | some l => l.unit != .user || l.value == 0
      | none => false)
  let mut style := "normal"
  let mut variant := "normal"
  let mut weight := "normal"
  let mut width := "normal"
  let mut rest := t
  for _ in [0:5] do
    let r := rest.trimAscii.toString
    let tok := (r.takeWhile (!PathData.isWsp ·)).toString
    if tok.isEmpty then return none
    let after := (r.drop tok.length).toString
    -- A size, or a size and a line height after a slash.
    let (sizeTok, lh) := match tok.splitOn "/" with
      | [a, b] => (a, some b)
      | _ => (tok, none)
    if isSize sizeTok then
      let after := after.trimAscii.toString
      let (lh, after) := match lh with
        | some l => (some l, after)
        | none =>
          if after.startsWith "/" then
            let a := (after.drop 1).trimAscii.toString
            let l := (a.takeWhile (!PathData.isWsp ·)).toString
            (some l, (a.drop l.length).toString)
          else (none, after)
      if lh == some "" then return none
      rest := after
      let fam := rest.trimAscii.toString
      if fam.isEmpty then return none
      return some #[("font-style", style), ("font-variant", variant), ("font-weight", weight),
        ("font-stretch", width), ("font-size", sizeTok), ("line-height", lh.getD "normal"),
        ("font-family", fam)]
    let lt := tok.toLower
    if lt == "normal" then pure ()
    else if styles.contains lt || lt.startsWith "oblique" then style := tok
    else if lt == "small-caps" then variant := tok
    else if weights.contains lt || (num? tok).isSome then weight := tok
    else if widths.contains lt then width := tok
    else return none
    rest := after
  return none

/-- A selector's view of an element. -/
public def subjectOf (name : String) (attrs : Array Xml.Attr) : Css.Subject :=
  { type := name
    classes := ((Xml.Attr.get? attrs "" "class").map fun c =>
      ((c.split Css.isWs).toList.map (·.toString)).filter (!·.isEmpty) |>.toArray).getD #[]
    id := Xml.Attr.get? attrs "" "id" }

/-- What an element declares, from all three sources: its presentation
attributes (level 0), the sheet rules whose selectors match it in its own
place (level 1), its `style` attribute (level 2). A sheet rule's order is
its rule's, then its declaration's, place in the sheets. -/
public def declsOf (rules : Array Css.Rule) (subject : Css.Subject) (up : List Css.Subject)
    (attrs : Array Xml.Attr) : Decls × Array String := Id.run do
  let mut out : Decls := #[]
  let mut problems : Array String := #[]
  for h : i in [0:attrs.size] do
    let a := attrs[i]
    if a.ns == "" && properties.contains a.name then
      out := out.push (a.name, { important := false, level := 0, spec := (0, 0, 0), order := i },
        a.value.trimAscii.toString)
  let mut order := 0
  for r in rules do
    let best := r.selectors.foldl (fun acc (s : Css.Selector) =>
      if s.matches subject up then
        match acc with
        | none => some s.specificity
        | some sp => if Css.Key.lt { important := false, level := 1, spec := sp, order := 0 }
            { important := false, level := 1, spec := s.specificity, order := 0 }
          then some s.specificity else some sp
      else acc) none
    if let some sp := best then
      for d in r.decls do
        out := out.push (d.prop, { important := d.important, level := 1, spec := sp, order }, d.value)
        order := order + 1
    else order := order + r.decls.size
  if let some st := Xml.Attr.get? attrs "" "style" then
    match Css.parseDecls st with
    | .ok ds =>
      for h : j in [0:ds.size] do
        let d := ds[j]
        out := out.push (d.prop, { important := d.important, level := 2, spec := (0, 0, 0), order := j },
          d.value)
    | .error (.unsupported why) => problems := problems.push why
    | .error (.refused why) => problems := problems.push why
  -- A `font` shorthand is its longhands, under its own key; one this reader
  -- cannot read stays, and is the loss `propertyTable` names.
  let expanded := out.foldl (fun acc (p, k, v) =>
    if p == "font" then
      match fontShorthand? v with
      | some ls => acc ++ ls.map fun (lp, lv) => (lp, k, lv)
      | none => acc.push (p, k, v)
    else acc.push (p, k, v)) #[]
  return (expanded, problems)

/-- The declarations for one property, greatest key first. -/
public def candidates (d : Decls) (prop : String) : Array (Css.Key × String) :=
  (d.filterMap fun (p, k, v) => if p == prop then some (k, v) else none).qsort
    fun a b => Css.Key.lt b.1 a.1

/-- A property's value through the cascade: the winner among the
declarations whose value reads (an unreadable one is dropped, as CSS drops
it), `inherit`, `initial` and `unset` as CSS Cascading 4 §7.3 reads them,
and the parent's or the initial value where nothing is declared. -/
public def pick {α : Type} (d : Decls) (prop : String) (inherited : Bool) (parent initial : α)
    (parse : String → Option α) : α :=
  let keyword (v : String) : Option α :=
    match v.toLower with
    | "inherit" => some parent
    | "initial" => some initial
    | "unset" => some (if inherited then parent else initial)
    | _ => none
  let read (v : String) : Option α := (keyword v).orElse fun _ => parse v
  -- The cascade runs over the declarations whose value reads: an
  -- unreadable one is dropped before it can win (`Css.cascade_exact`).
  let valid := (d.filterMap fun (p, k, v) => if p == prop && (read v).isSome then some (k, v) else none)
  match (Css.cascade valid).bind read with
  | some v => v
  | none => if inherited then parent else initial

/-- Whether any declaration names the property at all. -/
@[expose] public def declares (d : Decls) (prop : String) : Bool := d.any (·.1 == prop)

/-- A colour value with its alpha, `currentColor` the caller's. -/
public def colorValue? (current : Ir.Color × Nat) (s : String) : Option (Ir.Color × Nat) :=
  if s.trimAscii.toString.toLower == "currentcolor" then some current
  else (CssColor.parse s).map fun v => (v.color, v.alpha)

/-- A paint (SVG 2 §13.2): `none`, `currentColor`, a colour, or a paint
server reference with an optional fallback. -/
public def paint? (s : String) : Option PaintSpec :=
  let t := s.trimAscii.toString
  let lower := t.toLower
  if lower == "none" then some .none
  else if lower == "currentcolor" then some .current
  else if lower.startsWith "url(" then
    match t.splitOn ")" with
    | inner :: rest =>
      let inner := ((inner.drop 4).toString.trimAscii.toString)
      let inner := if inner.startsWith "\"" || inner.startsWith "'" then ((inner.drop 1).dropEnd 1).toString
        else inner
      if !inner.startsWith "#" then none else
      let fb := (")".intercalate rest).trimAscii.toString
      let fallback : Option PaintSpec :=
        if fb.isEmpty then none
        else if fb.toLower == "none" then some .none
        else if fb.toLower == "currentcolor" then some .current
        else (CssColor.parse fb).map fun v => .color v.color v.alpha
      some (.url (inner.drop 1).toString fallback)
    | [] => none
  else (CssColor.parse t).map fun v => .color v.color v.alpha

/-- An opacity: a number or a percentage, clamped to [0, 1], in thousandths. -/
public def opacity? (s : String) : Option Nat :=
  let t := s.trimAscii.toString
  if t.endsWith "%" then (num? (t.dropEnd 1).toString).map fun q => clampMilli (q * 10)
  else (num? t).map fun q => clampMilli (q * 1000)
where
  clampMilli (q : Rat) : Nat := if q ≤ 0 then 0 else if q ≥ 1000 then 1000 else
    let r := q + 1 / 2
    r.floor.toNat

@[expose] public def rule? (s : String) : Option Rule :=
  match s.trimAscii.toString.toLower with
  | "nonzero" => some .nonzero
  | "evenodd" => some .evenOdd
  | _ => none

/-- The generic families CSS Fonts 4 §4.2 names. -/
@[expose] public def generics : List String :=
  ["serif", "sans-serif", "monospace", "cursive", "fantasy", "system-ui", "ui-serif",
   "ui-sans-serif", "ui-monospace", "ui-rounded", "math", "emoji", "fangsong"]

/-- A `font-family` list: each family unquoted, a generic one lower case. -/
public def families? (s : String) : Option (Array String) :=
  let fams := (s.splitOn ",").map fun f =>
    let t := f.trimAscii.toString
    let t := if t.length ≥ 2 && (t.startsWith "\"" && t.endsWith "\"" || t.startsWith "'" && t.endsWith "'")
      then ((t.drop 1).dropEnd 1).toString else t
    if generics.contains t.toLower then t.toLower else t
  let fams := fams.filter (!·.isEmpty)
  if fams.isEmpty then none else some fams.toArray

/-- A `font-weight`: a keyword or a number, `bolder`/`lighter` against the
parent's (CSS Fonts 4 §2.2's table). -/
public def weight? (parent : Nat) (s : String) : Option Nat :=
  match s.trimAscii.toString.toLower with
  | "normal" => some 400
  | "bold" => some 700
  | "bolder" => some (if parent < 350 then 400 else if parent < 550 then 700 else 900)
  | "lighter" => some (if parent < 550 then 100 else if parent < 750 then 400 else 700)
  | t => (num? t).bind fun q => if 1 ≤ q && q ≤ 1000 then some q.floor.toNat else none

/-- A font size in pixels (CSS Fonts 4 §2.5): a keyword, a length, a
percentage or an em of the parent's size. -/
public def fontSize? (parent : Rat) (s : String) : Option Rat :=
  match s.trimAscii.toString.toLower with
  | "xx-small" => some 9
  | "x-small" => some 10
  | "small" => some 13
  | "medium" => some 16
  | "large" => some 18
  | "x-large" => some 24
  | "xx-large" => some 32
  | "xxx-large" => some 48
  | "smaller" => some (parent * 5 / 6)
  | "larger" => some (parent * 6 / 5)
  | t => (length? t).bind fun l =>
    let v := l.toPx parent parent
    if v < 0 then none else some v

/-- What a computed style reads off an element's declarations. -/
public structure Read where
  style : Style
  opacity : Nat
  clipPath : Option String
  display : Bool
  overflowVisible : Option Bool
  /-- The element's `transform-origin`, in user units. -/
  origin : Rat × Rat
  losses : Array Gfx.Loss
  deriving Inhabited

/-- A `transform-origin` (CSS Transforms 1 §6.1) in user units: one to
three values — keywords, lengths, percentages of the reference box `(w, h)`,
the nearest viewport's, as `transform-box: view-box` reads it — the third, a
z offset, moving nothing in a plane. -/
public def origin? (em w h : Rat) (s : String) : Option (Rat × Rat) :=
  let toks := ((s.trimAscii.toString.split PathData.isWsp).toList.map (·.toString)).filter
    (!·.isEmpty)
  -- A keyword's axis (`some true` horizontal, `some false` vertical,
  -- `none` either) and its percentage.
  let kw (t : String) : Option (Option Bool × Rat) := match t.toLower with
    | "left" => some (some true, 0)
    | "right" => some (some true, 100)
    | "top" => some (some false, 0)
    | "bottom" => some (some false, 100)
    | "center" => some (none, 50)
    | _ => none
  let len (t : String) (base : Rat) : Option Rat := (length? t).map (·.toPx em base)
  let axis (t : String) (horizontal : Bool) : Option Rat :=
    match kw t with
    | some (some hz, p) => if hz == horizontal then some (p * (if horizontal then w else h) / 100) else none
    | some (none, p) => some (p * (if horizontal then w else h) / 100)
    | none => len t (if horizontal then w else h)
  let pair (a b : String) : Option (Rat × Rat) :=
    -- Two keywords may come in either order; a length fixes the order.
    let swapped := match kw a, kw b with
      | some (some false, _), some _ => true
      | some _, some (some true, _) => true
      | _, _ => false
    let (a, b) := if swapped then (b, a) else (a, b)
    match axis a true, axis b false with
    | some x, some y => some (x, y)
    | _, _ => none
  match toks with
  | [a] =>
    match kw a with
    | some (some false, p) => some (w / 2, p * h / 100)
    | some (some true, p) => some (p * w / 100, h / 2)
    | some (none, _) => some (w / 2, h / 2)
    | none => (len a w).map (·, h / 2)
  | [a, b] => pair a b
  | [a, b, z] => if (length? z).isSome then pair a b else none
  | _ => none

/-- A transform about an origin: translated there, transformed, translated
back (CSS Transforms 1 §6.1); the identity stays the identity. -/
@[expose] public def aroundOrigin (m : Affine) (o : Rat × Rat) : Affine :=
  if m == Affine.unit || (o.1 == 0 && o.2 == 0) then m
  else (shift o.1 o.2).compose (m.compose (shift (-o.1) (-o.2)))

/-- **One element's computed style**: its declarations over its parent's
style, in the viewport `vp`. -/
public def computeStyle (d : Decls) (parent : Style) (vp : Viewport) (attrs : Array Xml.Attr) : Read :=
  let fontSize := pick d "font-size" true parent.fontSize Style.initial.fontSize (fontSize? parent.fontSize)
  let len (base : Rat) (s : String) : Option Sp :=
    (length? s).bind fun l => let v := l.toPx fontSize base; if v < 0 then none else some (spOf v)
  let color := pick d "color" true parent.color Style.initial.color (colorValue? parent.color)
  let dash? (s : String) : Option (Array Sp) :=
    if s.trimAscii.toString.toLower == "none" then some #[] else
    (lengthList? s).bind fun ls =>
      let vs := ls.map fun l => spOf (l.toPx fontSize vp.diag)
      if vs.any (· < 0) then none else some (Kit.normDash vs)
  let style : Style :=
    { fill := pick d "fill" true parent.fill Style.initial.fill paint?
      fillOpacity := pick d "fill-opacity" true parent.fillOpacity 1000 opacity?
      fillRule := pick d "fill-rule" true parent.fillRule .nonzero rule?
      stroke := pick d "stroke" true parent.stroke .none paint?
      strokeOpacity := pick d "stroke-opacity" true parent.strokeOpacity 1000 opacity?
      strokeWidth := pick d "stroke-width" true parent.strokeWidth pxSp (len vp.diag)
      cap := pick d "stroke-linecap" true parent.cap .butt fun s => match s.trimAscii.toString with
        | "butt" => some .butt | "round" => some .round | "square" => some .square | _ => none
      join := pick d "stroke-linejoin" true parent.join .miter fun s => match s.trimAscii.toString with
        | "miter" => some .miter | "round" => some .round | "bevel" => some .bevel | _ => none
      miter := pick d "stroke-miterlimit" true parent.miter 4 fun s =>
        (num? s).bind fun q => if q < 1 then none else some q
      dash := pick d "stroke-dasharray" true parent.dash #[] dash?
      dashOffset := pick d "stroke-dashoffset" true parent.dashOffset 0 fun s =>
        (length? s).map fun l => spOf (l.toPx fontSize vp.diag)
      color
      visible := pick d "visibility" true parent.visible true fun s => match s.trimAscii.toString with
        | "visible" => some true | "hidden" => some false | "collapse" => some false | _ => none
      families := pick d "font-family" true parent.families Style.initial.families families?
      fontSize
      weight := pick d "font-weight" true parent.weight 400 (weight? parent.weight)
      italic := pick d "font-style" true parent.italic false fun s => match s.trimAscii.toString with
        | "normal" => some false | "italic" => some true | "oblique" => some true | _ =>
          if s.trimAscii.toString.startsWith "oblique" then some true else none
      anchor := pick d "text-anchor" true parent.anchor .start fun s => match s.trimAscii.toString with
        | "start" => some .start | "middle" => some .middle | "end" => some .end | _ => none
      clipRule := pick d "clip-rule" true parent.clipRule .nonzero rule?
      smooth := pick d "image-rendering" true parent.smooth true fun s => match s.trimAscii.toString with
        | "auto" | "optimizeQuality" | "smooth" | "high-quality" => some true
        | "optimizeSpeed" | "pixelated" | "crisp-edges" => some false
        | _ => none
      preserve := match Xml.Attr.get? attrs Xml.xmlNs "space" with
        | some "preserve" => true
        | some "default" => false
        | _ => parent.preserve
      lang := (Xml.Attr.get? attrs Xml.xmlNs "lang").orElse fun _ =>
        (Xml.Attr.get? attrs "" "lang").orElse fun _ => parent.lang }
  let opacity := pick d "opacity" false 1000 1000 opacity?
  let clipPath := pick d "clip-path" false none none fun s =>
    let t := s.trimAscii.toString
    if t.toLower == "none" then some none
    else if t.startsWith "url(#" && t.endsWith ")" then some (some ((t.drop 5).dropEnd 1).toString)
    else none
  let display := pick d "display" false true true fun s => some (s.trimAscii.toString != "none")
  let overflowVisible := pick d "overflow" false none none fun s => match s.trimAscii.toString with
    | "visible" | "auto" => some (some true)
    | "hidden" | "scroll" | "clip" => some (some false)
    | _ => none
  let origin := pick d "transform-origin" false (0, 0) (0, 0) (origin? fontSize vp.w vp.h)
  -- The properties the importer does not give their meaning: a loss each,
  -- once declared with a value other than one that changes nothing.
  let unless_ (prop : String) (harmless : List String) : Bool :=
    match (candidates d prop)[0]? with
    | some (_, v) =>
      let v := v.trimAscii.toString.toLower
      !(harmless.contains v || ["inherit", "initial", "unset"].contains v)
    | none => false
  let tableLosses := propertyTable.foldl (fun acc (p, t) => match t with
    | .lossUnless harmless => if unless_ p harmless then acc.push (.property p) else acc
    | .honoured => acc
    | .inert => acc) #[]
  let cssLosses := cssLost.foldl (fun acc (p, harmless) =>
    if d.any fun (q, k, v) => q == p && k.level ≥ 1 &&
        !harmless.contains v.trimAscii.toString.toLower then acc.push (.property p)
    else acc) #[]
  let losses := tableLosses ++ cssLosses
  { style := style, opacity := opacity, clipPath := clipPath, display := display
    overflowVisible := overflowVisible, origin := origin, losses := losses }

/-! ## Geometry -/

/-- A point of user space, in `Sp`. -/
@[expose] public def pt (x y : Rat) : Pt := (spOf x, spOf y)

/-- Path commands as subpaths of user space: relative commands made
absolute, smooth curves' reflected controls, quadratics elevated, arcs as
cubics (`Kit.arcEndpoint`), each subpath closed where the data closes it. -/
public def subpathsOf (cmds : Array PathData.Cmd) : Array Subpath := Id.run do
  let mut done : Array Subpath := #[]
  let mut cur : Option Subpath := none
  -- The current point and the subpath's start, in pixels, exactly.
  let mut px : Rat := 0
  let mut py : Rat := 0
  let mut sx : Rat := 0
  let mut sy : Rat := 0
  -- The last control point, for S and T, with what kind of segment set it.
  let mut lastCubic : Option (Rat × Rat) := none
  let mut lastQuad : Option (Rat × Rat) := none
  for c in cmds do
    let base (rel : Bool) : Rat × Rat := if rel then (px, py) else (0, 0)
    match c with
    | .move rel x y =>
      let (bx, by_) := base rel
      if let some s := cur then done := done.push s
      px := bx + x.toRat
      py := by_ + y.toRat
      sx := px
      sy := py
      cur := some { start := pt px py, segs := #[], closed := false }
      lastCubic := none
      lastQuad := none
    | .close =>
      if let some s := cur then
        done := done.push { s with closed := true }
        cur := some { start := pt sx sy, segs := #[], closed := false }
      px := sx
      py := sy
      lastCubic := none
      lastQuad := none
    | other =>
      let s := cur.getD { start := pt px py, segs := #[], closed := false }
      let (segs, np, cubic, quad) : Array Seg × (Rat × Rat) × Option (Rat × Rat) × Option (Rat × Rat) :=
        match other with
        | .line rel x y =>
          let (bx, by_) := base rel
          let p := (bx + x.toRat, by_ + y.toRat)
          (#[.line (pt p.1 p.2)], p, none, none)
        | .horiz rel x =>
          let p := ((if rel then px else 0) + x.toRat, py)
          (#[.line (pt p.1 p.2)], p, none, none)
        | .vert rel y =>
          let p := (px, (if rel then py else 0) + y.toRat)
          (#[.line (pt p.1 p.2)], p, none, none)
        | .cubic rel x1 y1 x2 y2 x y =>
          let (bx, by_) := base rel
          let c1 := (bx + x1.toRat, by_ + y1.toRat)
          let c2 := (bx + x2.toRat, by_ + y2.toRat)
          let p := (bx + x.toRat, by_ + y.toRat)
          (#[.cubic (pt c1.1 c1.2) (pt c2.1 c2.2) (pt p.1 p.2)], p, some c2, none)
        | .smooth rel x2 y2 x y =>
          let (bx, by_) := base rel
          let c1 := match lastCubic with
            | some (cx, cy) => (2 * px - cx, 2 * py - cy)
            | none => (px, py)
          let c2 := (bx + x2.toRat, by_ + y2.toRat)
          let p := (bx + x.toRat, by_ + y.toRat)
          (#[.cubic (pt c1.1 c1.2) (pt c2.1 c2.2) (pt p.1 p.2)], p, some c2, none)
        | .quad rel x1 y1 x y =>
          let (bx, by_) := base rel
          let q := (bx + x1.toRat, by_ + y1.toRat)
          let p := (bx + x.toRat, by_ + y.toRat)
          (#[quadSeg (px, py) q p], p, none, some q)
        | .smoothQuad rel x y =>
          let (bx, by_) := base rel
          let q := match lastQuad with
            | some (qx, qy) => (2 * px - qx, 2 * py - qy)
            | none => (px, py)
          let p := (bx + x.toRat, by_ + y.toRat)
          (#[quadSeg (px, py) q p], p, none, some q)
        | .arc rel rx ry rot large sweep x y =>
          let (bx, by_) := base rel
          let p := (bx + x.toRat, by_ + y.toRat)
          let φ := Trig.divRound (rot.toRat.num * Trig.pi) (180 * (rot.toRat.den : Int))
          (Kit.arcEndpoint (pt px py) (spOf rx.toRat).natAbs (spOf ry.toRat).natAbs φ large sweep
            (pt p.1 p.2), p, none, none)
        | .move _ _ _ | .close => (#[], (px, py), none, none)
      cur := some { s with segs := s.segs ++ segs }
      px := np.1
      py := np.2
      lastCubic := cubic
      lastQuad := quad
  if let some s := cur then
    if !s.segs.isEmpty || s.closed then done := done.push s
  return done.filter fun s => !s.segs.isEmpty || s.closed
where
  /-- A quadratic as the cubic that draws it, its controls computed in
  pixels and rounded once. -/
  quadSeg (p0 q p1 : Rat × Rat) : Seg :=
    .cubic (pt (p0.1 + 2 * (q.1 - p0.1) / 3) (p0.2 + 2 * (q.2 - p0.2) / 3))
      (pt (p1.1 + 2 * (q.1 - p1.1) / 3) (p1.2 + 2 * (q.2 - p1.2) / 3)) (pt p1.1 p1.2)

/-- An attribute's length in pixels against a percentage basis, or `dflt`. -/
public def lenAttr (attrs : Array Xml.Attr) (name : String) (em base : Rat) (dflt : Rat) : Rat :=
  ((Xml.Attr.get? attrs "" name).bind length?).map (·.toPx em base) |>.getD dflt

/-- The loss a path is where a number past the reader's range cut it
short (`PathData.Stop.range`), which a browser's double reads on past. -/
@[expose] public def pathRangeLoss : Gfx.Loss := .budget "a path number's range"

/-- A basic shape other than a path (SVG 2 §10), in user space. -/
public def basicGeom (name : String) (attrs : Array Xml.Attr) (em : Rat) (vp : Viewport) :
    Option Geom :=
  let l (n : String) (base : Rat) := lenAttr attrs n em base 0
  match name with
  | "rect" =>
    let w := l "width" vp.w
    let h := l "height" vp.h
    if w ≤ 0 || h ≤ 0 then none else
    let rx? := ((Xml.Attr.get? attrs "" "rx").bind length?).map (·.toPx em vp.w)
    let ry? := ((Xml.Attr.get? attrs "" "ry").bind length?).map (·.toPx em vp.h)
    let (rx, ry) := match rx?, ry? with
      | some a, some b => (a, b)
      | some a, none => (a, a)
      | none, some b => (b, b)
      | none, none => (0, 0)
    let x := l "x" vp.w
    let y := l "y" vp.h
    if rx ≤ 0 || ry ≤ 0 then some (.rect (spOf x) (spOf y) (spOf w) (spOf h))
    else some (.path #[Kit.roundedRect (spOf x) (spOf y) (spOf w) (spOf h) (spOf rx) (spOf ry)])
  | "circle" =>
    let r := l "r" vp.diag
    if r ≤ 0 then none else some (.ellipse (spOf (l "cx" vp.w)) (spOf (l "cy" vp.h)) (spOf r) (spOf r))
  | "ellipse" =>
    let rx := l "rx" vp.w
    let ry := l "ry" vp.h
    if rx ≤ 0 || ry ≤ 0 then none
    else some (.ellipse (spOf (l "cx" vp.w)) (spOf (l "cy" vp.h)) (spOf rx) (spOf ry))
  | "line" =>
    some (.path #[{ start := pt (l "x1" vp.w) (l "y1" vp.h), segs := #[.line (pt (l "x2" vp.w) (l "y2" vp.h))]
                    closed := false }])
  | "polyline" | "polygon" =>
    let ps := ((Xml.Attr.get? attrs "" "points").bind numList?).getD #[]
    let ps := if ps.size % 2 == 1 then ps.pop else ps
    if ps.size < 4 then none else
    let pts := (Array.range (ps.size / 2)).map fun k => pt (ps[2 * k]?.getD 0) (ps[2 * k + 1]?.getD 0)
    some (.path #[{ start := pts[0]?.getD (0, 0), segs := (pts.extract 1 pts.size).map Seg.line
                    closed := name == "polygon" }])
  | _ => none

/-- A basic shape's geometry (SVG 2 §10), in user space; `none` where the
shape draws nothing (a zero or negative extent, too few points). The flag
is false where a number past the reader's range cut a path short. -/
public def shapeGeom (name : String) (attrs : Array Xml.Attr) (em : Rat) (vp : Viewport) :
    Option Geom × Bool :=
  if name == "path" then
    let (cmds, stop) := PathData.parse ((Xml.Attr.get? attrs "" "d").getD "")
    let subs := subpathsOf cmds
    (if subs.isEmpty then none else some (.path subs), stop != .range)
  else (basicGeom name attrs em vp, true)

/-- A geometry's box in its own frame, the fill box (SVG 2 §8.10's
object bounding box, by its control points). -/
public def bboxOf (g : Geom) : Option Box := g.hull

/-! ## The walk -/

/-- An element the walk can reach by its id: the element, and its
ancestors in the tree, innermost first, for selector matching. -/
public structure Entry where
  item : Xml.Item
  up : List Css.Subject
  deriving Inhabited

/-- What every step of the walk reads: the elements by id, the sheets'
rules, the document language. -/
public structure Env where
  ids : Std.HashMap String Entry
  rules : Array Css.Rule
  lang : String

/-- A `use` the walk met, to be read later: the element it names, the
style its clone inherits, and whether it reads the element's children (a
symbol's, whose viewport the use site placed) or the element itself. -/
public structure Request where
  id : String
  style : Style
  vp : Viewport
  children : Bool
  deriving Inhabited, BEq

/-- What the walk accumulates. -/
public structure St where
  losses : Array Gfx.Loss
  notes : Array String
  rasters : Array Raster
  requests : Array Request
  nodes : Nat
  animated : Bool
  text : Bool
  deriving Inhabited

/-- The most nodes one import emits, and the most references it reads:
past either the drawing stops, and the budget is named. -/
public structure Budget where
  nodes : Nat
  requests : Nat
  /-- The nodes a figure may paint once its uses are expanded: a use
  nested in a use multiplies, so a few dozen symbols can name millions. -/
  expanded : Nat
  deriving Repr, Inhabited

@[expose] public def Budget.standard : Budget :=
  { nodes := 2000000, requests := 100000, expanded := 200000 }

/-- The request a `use` makes, shared with an equal one already made: one
symbol per element, inherited style and viewport. -/
public def St.request (s : St) (r : Request) : St × Nat :=
  match s.requests.findIdx? (· == r) with
  | some k => (s, k)
  | none => ({ s with requests := s.requests.push r }, s.requests.size)

@[expose] public def St.lose (s : St) (l : Gfx.Loss) : St :=
  if s.losses.contains l then s else { s with losses := s.losses.push l }

/-- The walk's place: the original ancestors (selectors), the parent's
style (inheritance), the viewport (percentages). -/
public structure Ctx where
  up : List Css.Subject
  parent : Style
  vp : Viewport
  deriving Inhabited

/-- The fill and stroke a style paints with, for a geometry whose box is
`bbox`, its paint servers resolved. -/
public structure Paints where
  fill : Option Fill
  stroke : Option Stroke
  deriving Inhabited

/-- Base64 (RFC 4648 §4) decoded; `none` on a byte outside the alphabet. -/
public def unbase64 (s : String) : Option ByteArray := Id.run do
  let val (c : Char) : Option Nat :=
    if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 65)
    else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 71)
    else if '0' ≤ c && c ≤ '9' then some (c.toNat + 4)
    else if c == '+' || c == '-' then some 62
    else if c == '/' || c == '_' then some 63
    else none
  let mut out := ByteArray.emptyWithCapacity (s.length * 3 / 4)
  let mut acc : Nat := 0
  let mut bits : Nat := 0
  for c in s.toList do
    if c == '=' then break
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then continue
    let some v := val c | return none
    acc := (acc * 64 + v) % 16777216
    bits := bits + 6
    if bits ≥ 8 then
      bits := bits - 8
      out := out.push ((acc / (2 ^ bits)) % 256).toUInt8
  return some out

/-- `%XX` escapes decoded, for a `data:` URI that is not base64. -/
public def unpercent (s : String) : ByteArray := Id.run do
  let b := s.toUTF8
  let mut out := ByteArray.emptyWithCapacity b.size
  let mut i := 0
  for _ in [0:b.size + 1] do
    if i ≥ b.size then break
    let c := (Xml.at? b i).toUInt8
    if c == 37 then
      match Xml.hexVal (Xml.at? b (i + 1)), Xml.hexVal (Xml.at? b (i + 2)) with
      | some h, some l =>
        out := out.push (h * 16 + l).toUInt8
        i := i + 3
      | _, _ =>
        out := out.push c
        i := i + 1
    else
      out := out.push c
      i := i + 1
  return out

/-- An `image`'s raster: its `data:` URI's bytes, sniffed as PNG or JPEG
whatever the declared type, with its pixel size. -/
public def rasterOf (href : String) (smooth : Bool) : Option Raster := do
  let (_, b64, payload) ← dataUri href
  let bytes ← if b64 then unbase64 payload else some (unpercent payload)
  let src ← (Image.probe bytes).toOption
  match src.format with
  | .png => some { bytes, jpeg := false, pxW := src.pxW, pxH := src.pxH, smooth }
  | .jpeg => some { bytes, jpeg := true, pxW := src.pxW, pxH := src.pxH, smooth }
  | _ => none

/-- A gradient element's own attribute, or the one its `href` chain
supplies first (SVG 2 §14.2.3): at most one step per element the file
defines, so a cycle ends. -/
public def gradientAttr (env : Env) (start : Xml.Item) (name : String) : Option String := Id.run do
  let mut cur := start
  for _ in [0:env.ids.size + 1] do
    match cur with
    | .elem _ _ attrs _ =>
      if let some v := Xml.Attr.get? attrs "" name then return some v
      let href := (Xml.Attr.get? attrs "" "href").orElse fun _ => Xml.Attr.get? attrs xlinkNs "href"
      match href with
      | some h =>
        match env.ids.get? ((normalizeSpace h).drop 1).toString with
        | some e => cur := e.item
        | none => return none
      | none => return none
    | .text _ => return none
  return none

/-- A gradient's stops: its own, or the first in its `href` chain that has
any. -/
public def gradientStops (env : Env) (start : Xml.Item) : Array Xml.Item := Id.run do
  let mut cur := start
  for _ in [0:env.ids.size + 1] do
    match cur with
    | .elem _ _ attrs kids =>
      let stops := kids.filter fun k => match k with
        | .elem ns n _ _ => ns == svgNs && n == "stop"
        | .text _ => false
      if !stops.isEmpty then return stops
      let href := (Xml.Attr.get? attrs "" "href").orElse fun _ => Xml.Attr.get? attrs xlinkNs "href"
      match href with
      | some h =>
        match env.ids.get? ((normalizeSpace h).drop 1).toString with
        | some e => cur := e.item
        | none => return #[]
      | none => return #[]
    | .text _ => return #[]
  return #[]

/-- A stop's offset in 65536ths, clamped (SVG 2 §14.4.2). -/
public def stopOffset (s : String) : Nat :=
  let t := s.trimAscii.toString
  let q := if t.endsWith "%" then ((num? (t.dropEnd 1).toString).getD 0) / 100 else (num? t).getD 0
  let q := if q < 0 then 0 else if q > 1 then 1 else q
  (q * 65536 + 1 / 2).floor.toNat

/-- A paint server, resolved for a shape whose fill box is `bbox`: a
gradient, a solid colour (one stop), nothing (no stop, an empty box under
`objectBoundingBox`), or the loss it meets. -/
public def gradientOf (env : Env) (cx : Ctx) (id : String) (bbox : Option Box) (alpha : Nat) :
    Except Gfx.Loss (Option (Paint × Nat)) := do
  let some e := env.ids.get? id | return none
  let .elem ns name _ _ := e.item | return none
  unless ns == svgNs do return none
  if name == "pattern" then throw (.element "pattern")
  unless name == "linearGradient" || name == "radialGradient" do return none
  let attr (n : String) := gradientAttr env e.item n
  let spread := (attr "spreadMethod").getD "pad"
  unless spread.trimAscii.toString == "pad" do throw (.attribute "spreadMethod")
  -- Stops: offsets non-decreasing, colours opaque.
  let mut stops : Array Stop := #[]
  let mut last := 0
  for s in gradientStops env e.item do
    let .elem _ _ sattrs _ := s | continue
    let (d, _) := declsOf env.rules (subjectOf "stop" sattrs) [] sattrs
    let col := pick d "stop-color" false (black, 1000) (black, 1000) (colorValue? cx.parent.color)
    let op := pick d "stop-opacity" false 1000 1000 opacity?
    if op * col.2 / 1000 < 1000 then throw (.property "stop-opacity")
    let off := max last (stopOffset ((Xml.Attr.get? sattrs "" "offset").getD "0"))
    last := off
    stops := stops.push { offset := ⟨min off 65536, by omega⟩, color := col.1 }
  if stops.isEmpty then return none
  if let #[only] := stops then return some (.solid only.color, alpha)
  let bboxUnits := ((attr "gradientUnits").getD "objectBoundingBox").trimAscii.toString != "userSpaceOnUse"
  let gxf := ((attr "gradientTransform").bind transform?).getD Affine.unit
  -- The gradient's frame: user space, or the box's unit square at 65536
  -- per side, which `xf` maps onto the box.
  let frameOpt : Option (Affine × Rat × Rat × Rat) :=
    if bboxUnits then
      bbox.bind fun ((x0, y0), (x1, y1)) =>
        if x1 ≤ x0 || y1 ≤ y0 then none
        else some (⟨((x1 - x0 : Int) : Rat) / 65536, 0, 0, ((y1 - y0 : Int) : Rat) / 65536,
          (x0 : Rat), (y0 : Rat)⟩, (65536 : Rat), (1 : Rat), (1 : Rat))
    else some (Affine.unit, (pxSp : Rat), cx.vp.w, cx.vp.h)
  let some (frame, scale, bw, bh) := frameOpt | return none
  -- In box units a length is a fraction of the box; in user units a
  -- percentage reads the viewport.
  let coord (n : String) (dflt : Rat) (base : Rat) : Sp :=
    let v : Rat := match (attr n).bind length? with
      | some l => if bboxUnits then (if l.unit == .pct then l.value / 100 else l.value)
        else l.toPx cx.parent.fontSize base
      | none => dflt * (if bboxUnits then 1 else base)
    let s := v * scale
    (s + 1 / 2).floor
  -- A box-unit gradient's own transform reads its translation in box units.
  let gxf := if bboxUnits then { gxf with e := gxf.e / (pxSp : Rat) * 65536, f := gxf.f / (pxSp : Rat) * 65536 }
    else gxf
  let xf := frame.compose gxf
  if name == "linearGradient" then
    let p0 := (coord "x1" 0 bw, coord "y1" 0 bh)
    let p1 := (coord "x2" 1 bw, coord "y2" 0 bh)
    return some (.gradient (.linear p0 p1 stops xf), alpha)
  else
    let diag := if bboxUnits then (1 : Rat) else cx.vp.diag
    let c1 := (coord "cx" (1 / 2) bw, coord "cy" (1 / 2) bh)
    let r1 := coord "r" (1 / 2) diag
    let fx := match attr "fx" with
      | some _ => coord "fx" 0 bw
      | none => c1.1
    let fy := match attr "fy" with
      | some _ => coord "fy" 0 bh
      | none => c1.2
    let r0 := coord "fr" 0 diag
    if r1 ≤ 0 then return some (.solid ((stops.back?.map (·.color)).getD black), alpha)
    -- The focal circle must lie inside the end circle, the one geometry
    -- both formats draw alike.
    let dx := fx - c1.1
    let dy := fy - c1.2
    if (Nat.sqrt (dx * dx + dy * dy).toNat : Int) + r0 ≥ r1 then throw (.attribute "fx")
    return some (.gradient (.radial (fx, fy) r0 c1 r1 stops xf), alpha)

/-- A paint spec as a model paint and its alpha, for a shape with fill box
`bbox`; a server's failure falls back as SVG 2 §13.2.3 says. -/
public def resolvePaint (env : Env) (cx : Ctx) (st : St) (color : Ir.Color × Nat)
    (spec : PaintSpec) (bbox : Option Box) : Option (Paint × Nat) × St :=
  match spec with
  | .none => (none, st)
  | .color c a => (some (.solid c, a), st)
  | .current => (some (.solid color.1, color.2), st)
  | .url id fallback =>
    match gradientOf env cx id bbox 1000 with
    | .ok (some p) => (some p, st)
    | .ok none =>
      match fallback with
      | some (.color c a) => (some (.solid c, a), st)
      | some .current => (some (.solid color.1, color.2), st)
      | _ => (none, st)
    | .error l => (none, st.lose l)

/-- Thousandths times thousandths, as one alpha. -/
@[expose] public def mulAlpha (a b : Nat) : Alpha :=
  let v := min 1000 ((a * b + 500) / 1000)
  ⟨v, by omega⟩

/-- A shape's paints under its style. -/
public def paintsOf (env : Env) (cx : Ctx) (st : St) (s : Style) (bbox : Option Box) : Paints × St :=
  let (fp, st) := resolvePaint env cx st s.color s.fill bbox
  let (sp, st) := resolvePaint env cx st s.color s.stroke bbox
  let fill := fp.map fun (p, a) => { paint := p, rule := s.fillRule, alpha := mulAlpha a s.fillOpacity }
  let stroke := sp.bind fun (p, a) =>
    if s.strokeWidth ≤ 0 then none else
    some { paint := p, width := s.strokeWidth, cap := s.cap, join := s.join, miterLimit := s.miter
           dash := s.dash, phase := s.dashOffset, alpha := mulAlpha a s.strokeOpacity }
  ({ fill := fill, stroke := stroke }, st)

/-- A `clip-path` reference resolved for an element whose fill box is
`bbox`: the clip, and the frame it stands in relative to the element's —
the clip child's transform, the clipPath's own, and under
`objectBoundingBox` the box's — or what stops it. `none` inside means the
clip region is empty: nothing paints. -/
public def clipOf (env : Env) (cx : Ctx) (id : String) (bbox : Option Box) :
    Except Gfx.Loss (Option (Affine × Clip)) := do
  let some e := env.ids.get? id | throw (.resource "clip-path")
  let .elem ns name attrs kids := e.item | throw (.resource "clip-path")
  unless ns == svgNs && name == "clipPath" do throw (.resource "clip-path")
  if (Xml.Attr.get? attrs "" "clip-path").isSome then throw (.attribute "clip-path")
  let (dc, _) := declsOf env.rules (subjectOf name attrs) e.up attrs
  let rc := computeStyle dc cx.parent cx.vp attrs
  let own := aroundOrigin (((Xml.Attr.get? attrs "" "transform").bind transform?).getD Affine.unit)
    rc.origin
  let units := ((Xml.Attr.get? attrs "" "clipPathUnits").getD "userSpaceOnUse").trimAscii.toString
  let unitOpt : Option Affine :=
    if units == "objectBoundingBox" then
      bbox.map fun ((x0, y0), (x1, y1)) =>
        ⟨((x1 - x0 : Int) : Rat) / (pxSp : Rat), 0, 0, ((y1 - y0 : Int) : Rat) / (pxSp : Rat),
          (x0 : Rat), (y0 : Rat)⟩
    else some Affine.unit
  let some unitFrame := unitOpt | return none
  let shapes := kids.filter fun k => match k with
    | .elem kns _ _ _ => kns == svgNs
    | .text _ => false
  let mut found : Option (Affine × Clip) := none
  for k in shapes do
    let .elem _ kn kattrs _ := k | continue
    if kn == "title" || kn == "desc" || kn == "metadata" then continue
    let (d, _) := declsOf env.rules (subjectOf kn kattrs) e.up kattrs
    let r := computeStyle d cx.parent cx.vp kattrs
    if !r.display || !r.style.visible then continue
    if r.clipPath.isSome then throw (.attribute "clip-path")
    let (some g, inRange) := shapeGeom kn kattrs r.style.fontSize cx.vp | throw (.element s!"clipPath {kn}")
    unless inRange do throw pathRangeLoss
    if found.isSome then throw (.element "clipPath with several shapes")
    let kxf := aroundOrigin (((Xml.Attr.get? kattrs "" "transform").bind transform?).getD Affine.unit)
      r.origin
    found := some ((unitFrame.compose own).compose kxf, { geom := g, rule := r.style.clipRule })
  return found

/-- The figure-wide budget check before a node is emitted. -/
@[expose] public def St.room (s : St) (bud : Budget) : Bool := s.nodes < bud.nodes

/-! ### Text -/

/-- One character of a text element after white-space processing, with
the style it is set in and the positions its elements give it. -/
public structure TChar where
  c : Char
  style : Style
  x : Option Rat
  y : Option Rat
  dx : Rat
  dy : Rat
  deriving Inhabited

/-- One piece of a text element's content as the walk meets it: its text,
the style it is set in, and for each enclosing positioning element — the
innermost last — its x, y, dx and dy lists and how many characters it had
already given out. -/
public structure Piece where
  text : String
  style : Style
  deriving Inhabited

/-- One positioning element's lists, and the number that tells it apart
from its siblings. -/
public structure PosLists where
  id : Nat
  x : Array Rat
  y : Array Rat
  dx : Array Rat
  dy : Array Rat
  deriving Inhabited

mutual

-- conserves: none — a flattening of a text element's content into pieces;
-- its text census is the pieces' (`text_pieces` reads them in order).
/-- A text element's content flattened: each character-data piece with its
style and the position-list stack in force, in order; a `tspan` opens its
own lists; any other element is a loss. -/
public def piecesOne (env : Env) (cx : Ctx) (lists : Array PosLists)
    (acc : Array (Piece × Array PosLists) × Array Gfx.Loss × Nat) : Xml.Item →
    Array (Piece × Array PosLists) × Array Gfx.Loss × Nat
  | .text s => (acc.1.push ({ text := s, style := cx.parent }, lists), acc.2)
  | .elem ns name attrs kids =>
    if ns != svgNs then acc
    else if name == "tspan" then
      let (d, _) := declsOf env.rules (subjectOf name attrs) cx.up attrs
      let r := computeStyle d cx.parent cx.vp attrs
      if !r.display then acc else
      let em := r.style.fontSize
      let ls (n : String) (base : Rat) : Array Rat :=
        (((Xml.Attr.get? attrs "" n).bind lengthList?).getD #[]).map (·.toPx em base)
      let pl : PosLists := { id := acc.2.2, x := ls "x" cx.vp.w, y := ls "y" cx.vp.h
                             dx := ls "dx" cx.vp.w, dy := ls "dy" cx.vp.h }
      let losses := acc.2.1 ++ r.losses ++
        (if (Xml.Attr.get? attrs "" "rotate").isSome then #[Gfx.Loss.attribute "rotate"] else #[]) ++
        (if (Xml.Attr.get? attrs "" "textLength").isSome then #[Gfx.Loss.attribute "textLength"] else #[]) ++
        (if r.opacity < 1000 then #[Gfx.Loss.property "opacity on tspan"] else #[]) ++
        (if r.clipPath.isSome then #[Gfx.Loss.property "clip-path on tspan"] else #[])
      piecesList env { cx with up := subjectOf name attrs :: cx.up, parent := r.style } (lists.push pl)
        (acc.1, losses, acc.2.2 + 1) kids.toList
    else if name == "title" || name == "desc" || name == "metadata" then acc
    else if name.startsWith "animate" || name == "set" then acc
    else (acc.1, acc.2.1.push (.element s!"{name} in text"), acc.2.2)

public def piecesList (env : Env) (cx : Ctx) (lists : Array PosLists)
    (acc : Array (Piece × Array PosLists) × Array Gfx.Loss × Nat) :
    List Xml.Item → Array (Piece × Array PosLists) × Array Gfx.Loss × Nat
  | [] => acc
  | n :: rest => piecesList env cx lists (piecesOne env cx lists acc n) rest

end

/-- The characters a text element sets, after SVG 1.1 §10.15's white-space
rules — `xml:space="default"` drops line feeds, makes tabs spaces, trims
the element's ends and collapses runs of spaces; `preserve` makes each a
space — each with the position its innermost positioning element gives it
by index. -/
public def textChars (pieces : Array (Piece × Array PosLists)) : Array TChar := Id.run do
  let mut out : Array TChar := #[]
  -- How many addressable characters each positioning element has given
  -- out, by its id.
  let mut counts : Std.HashMap Nat Nat := {}
  let mut prevSpace := true
  for (p, lists) in pieces do
    for c in p.text.toList do
      let c := if c == '\t' then ' ' else c
      let keep : Option Char :=
        if p.style.preserve then some (if c == '\n' || c == '\r' then ' ' else c)
        else if c == '\n' || c == '\r' then none
        else if c == ' ' && prevSpace then none
        else some c
      let some ch := keep | continue
      prevSpace := ch == ' '
      -- The innermost element whose list reaches this character's index in
      -- it gives the position.
      let mut x : Option Rat := none
      let mut y : Option Rat := none
      let mut dx : Option Rat := none
      let mut dy : Option Rat := none
      for l in lists do
        let n := counts.getD l.id 0
        counts := counts.insert l.id (n + 1)
        if let some v := l.x[n]? then x := some v
        if let some v := l.y[n]? then y := some v
        if let some v := l.dx[n]? then dx := some v
        if let some v := l.dy[n]? then dy := some v
      out := out.push { c := ch, style := p.style, x, y, dx := dx.getD 0, dy := dy.getD 0 }
  -- The element's trailing spaces go, under the default rule.
  let mut n := out.size
  for _ in [0:out.size] do
    if n > 0 && (out[n - 1]?.any fun t => t.c == ' ' && !t.style.preserve) then n := n - 1 else break
  return out.extract 0 n

/-- Two paints alike, field by field — a colour's PDF rider included, which
the colour's own `==` leaves out. -/
public def PaintSpec.same : PaintSpec → PaintSpec → Bool
  | .none, .none => true
  | .color c a, .color c' a' => decide (c = c') && a == a'
  | .current, .current => true
  | .url i none, .url i' none => i == i'
  | .url i (some f), .url i' (some f') => i == i' && PaintSpec.same f f'
  | _, _ => false

/-- Two styles that set text alike: one face request, one size, one paint. -/
public def sameText (a b : Style) : Bool :=
  a.families == b.families && a.fontSize == b.fontSize && a.weight == b.weight &&
    a.italic == b.italic && a.fillOpacity == b.fillOpacity && a.strokeOpacity == b.strokeOpacity &&
    a.strokeWidth == b.strokeWidth && a.visible == b.visible && a.lang == b.lang &&
    a.fill.same b.fill && a.stroke.same b.stroke &&
    a.anchor == b.anchor && decide (a.color.1 = b.color.1) && a.color.2 == b.color.2

/-- A text element's runs: a new run wherever a character is positioned or
its style changes, a new chunk wherever one has an absolute x. The
current y is known exactly, since horizontal text never moves it by an
advance; the current x is the pen's, which only shaping knows, so a run
without an absolute x `follows`. -/
public def textRuns (env : Env) (cx : Ctx) (st : St) (x0 y0 : Rat) (cs : Array TChar) :
    Array (Node Run) × St := Id.run do
  let mut out : Array (Node Run) := #[]
  let mut st := st
  let mut y := y0
  let mut i := 0
  let mut first := true
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs[i]?.getD default
    let absX := if first then some (c.x.getD x0) else c.x
    let yy := (c.y.getD y) + c.dy
    y := yy
    -- The run extends over the following characters that set alike and
    -- carry no position of their own.
    let mut j := i + 1
    for _ in [0:cs.size] do
      if j ≥ cs.size then break
      let d := cs[j]?.getD default
      if d.x.isNone && d.y.isNone && d.dx == 0 && d.dy == 0 && sameText d.style c.style then j := j + 1
      else break
    let text := String.ofList ((cs.extract i j).toList.map (·.c))
    let s := c.style
    let (p, st') := paintsOf env cx st s none
    st := st'
    let follows := absX.isNone
    let xf : Affine := match absX with
      | some ax => ⟨1, 0, 0, -1, (ax + c.dx) * (pxSp : Rat), yy * (pxSp : Rat)⟩
      | none => ⟨1, 0, 0, -1, c.dx * (pxSp : Rat), yy * (pxSp : Rat)⟩
    -- A wholly transparent fill paints nothing: the run keeps its place in
    -- its chunk, its advance moving what follows, and paints no fill.
    let fill := p.fill.filter (·.alpha.val != 0)
    if s.visible && !text.isEmpty then
      out := out.push (.label { xf, follows, size := spOf s.fontSize, text
                                face := { families := s.families, weight := s.weight, italic := s.italic }
                                anchor := s.anchor, fill, stroke := p.stroke, lang := s.lang })
      -- Engine-set text paints a solid fill only: a paint server's colours
      -- and an outline stroke are features of the run the page would not
      -- show, however they resolve.
      match s.fill with
      | .url _ _ => st := st.lose (.value "gradient on text")
      | .none | .color _ _ | .current => pure ()
      match s.stroke with
      | .none => pure ()
      | .url _ _ | .color _ _ | .current =>
        if s.strokeWidth > 0 then st := st.lose (.property "stroke on text")
    first := false
    i := j
  return (out, { st with text := true })

/-! ### Elements -/

/-- Do the element's conditional attributes hold (SVG 2 §5.8.4)? No
extension is supported; a language list holds when one of its tags starts
the document's. -/
public def conditionsHold (env : Env) (attrs : Array Xml.Attr) : Bool :=
  let ext := match Xml.Attr.get? attrs "" "requiredExtensions" with
    | some _ => false
    | none => true
  let lang := match Xml.Attr.get? attrs "" "systemLanguage" with
    | some l =>
      ((l.splitOn ",").map (·.trimAscii.toString.toLower)).any fun t =>
        !t.isEmpty && (env.lang.toLower.startsWith t || t.startsWith env.lang.toLower)
    | none => true
  ext && lang

/-- An element's own transform. -/
@[expose] public def ownTransform (attrs : Array Xml.Attr) : Affine :=
  ((Xml.Attr.get? attrs "" "transform").bind transform?).getD Affine.unit

/-- Wrap what an element paints in the group its transform, clip and
opacity make, if any. The clip stands in the element's frame after its
transform, through its own frame map, inverted back for the content. -/
public def wrap (xf : Affine) (clip : Option (Affine × Clip)) (alpha : Nat) (kids : Array (Node Run)) :
    Array (Node Run) :=
  let a := mulAlpha alpha 1000
  -- A wholly transparent group paints nothing, and its text is none of the
  -- figure's words: a reader extracting the page's text would read words
  -- no viewer shows.
  if a.val == 0 then #[] else
  let inner : Array (Node Run) := match clip with
    | none => kids
    | some (m, c) =>
      if m == Affine.unit then #[.group Affine.unit #[c] Alpha.opaque kids]
      else match Affine.inverse? m with
        | some mi => #[.group m #[c] Alpha.opaque #[.group mi #[] Alpha.opaque kids]]
        | none => #[]
  if xf == Affine.unit && a == Alpha.opaque then
    match clip with
    | none => inner
    | some _ => inner
  else #[.group xf #[] a inner]

/-- The element names whose subtree paints nothing in place. -/
@[expose] public def definitions : List String :=
  ["defs", "symbol", "clipPath", "mask", "pattern", "marker", "linearGradient", "radialGradient",
   "filter", "style", "title", "desc", "metadata", "script", "font", "font-face", "glyph",
   "missing-glyph", "cursor", "view", "solidcolor", "hatch", "meshgradient"]

/-- The element names that are animation, which a static pose ignores. -/
@[expose] public def animations : List String :=
  ["animate", "set", "animateTransform", "animateMotion", "animateColor", "discard", "mpath"]

/-- Whether a tree moves: whether it holds an animation element. Read off
the authored tree — a pose projected to its end holds none, and the figure
still moves. -/
@[expose] public def moves (t : Xml.Item) : Bool := (elemsOne #[] t).any (animations.contains ·.1)

mutual

-- conserves: none — an importer: what it keeps is the figure's marks, held
-- against an independent renderer by the oracles (`scripts/svg-diff.lean`).
/-- One node of the tree onto `acc`, under `cx`. -/
public def walkOne (env : Env) (bud : Budget) (cx : Ctx) (acc : St × Array (Node Run)) :
    Xml.Item → St × Array (Node Run)
  | .text _ => acc
  | .elem ns name attrs kids =>
    let (st, out) := acc
    if ns != svgNs then acc
    else if animations.contains name then ({ st with animated := true }, out)
    else if definitions.contains name then acc
    else if !st.room bud then (st.lose (.budget "node count"), out)
    else if !conditionsHold env attrs then acc
    else
    let subject := subjectOf name attrs
    let (d, problems) := declsOf env.rules subject cx.up attrs
    let st := problems.foldl (fun s p => s.lose (.property s!"style: {p}")) st
    let r := computeStyle d cx.parent cx.vp attrs
    if !r.display then (st, out) else
    let st := r.losses.foldl St.lose st
    let st := { st with nodes := st.nodes + 1 }
    let s := r.style
    let inner : Ctx := { up := subject :: cx.up, parent := s, vp := cx.vp }
    let xf := aroundOrigin (ownTransform attrs) r.origin
    let clipFor (st : St) (bbox : Option Box) : Option (Option (Affine × Clip)) × St :=
      match r.clipPath with
      | none => (some none, st)
      | some id =>
        match clipOf env cx id bbox with
        | .ok (some c) => (some (some c), st)
        | .ok none => (none, st)
        | .error l => (some none, st.lose l)
    match name with
    | "g" | "a" | "switch" =>
      let st := if name == "a" then { st with notes := st.notes.push "a link inside the SVG" } else st
      let (st, body) := walkList env bud inner (name == "switch") (st, #[]) kids.toList
      let (clip, st) := clipFor st (hullOf (Mark.geomBox rasterUnit)
        ({ box := ((0, 0), (0, 0)), clipToBox := false, nodes := body, outlines := #[], symbols := #[]
           rasters := #[], title := none, losses := #[] } : Figure Run).marks)
      match clip with
      | none => (st, out)
      | some c => (st, out.append (wrap xf c r.opacity body))
    | "svg" =>
      let em := s.fontSize
      let x := lenAttr attrs "x" em cx.vp.w 0
      let y := lenAttr attrs "y" em cx.vp.h 0
      let w := lenAttr attrs "width" em cx.vp.w cx.vp.w
      let h := lenAttr attrs "height" em cx.vp.h cx.vp.h
      if w ≤ 0 || h ≤ 0 then (st, out) else
      let vb := (Xml.Attr.get? attrs "" "viewBox").bind viewBox?
      let par := ((Xml.Attr.get? attrs "" "preserveAspectRatio").map par?).getD Par.default
      let m : Affine := match vb with
        | some v => viewMap v par x y w h
        | none => shift x y
      let vp : Viewport := match vb with
        | some v => { w := v.w, h := v.h }
        | none => { w, h }
      let (st, body) := walkList env bud { inner with vp } false (st, #[]) kids.toList
      let clip : Option Clip := if r.overflowVisible == some true then none
        else some { geom := .rect (spOf x) (spOf y) (spOf w) (spOf h), rule := .nonzero }
      let viewport := #[Node.group Affine.unit (clip.toArray) Alpha.opaque #[.group m #[] Alpha.opaque body]]
      (st, out.append (wrap Affine.unit none r.opacity viewport))
    | "use" =>
      let href := (Xml.Attr.get? attrs "" "href").orElse fun _ => Xml.Attr.get? attrs xlinkNs "href"
      match href with
      | none => (st, out)
      | some h =>
        let id := ((normalizeSpace h).drop 1).toString
        match env.ids.get? id with
        | none => (st, out)
        | some target =>
          let em := s.fontSize
          let ux := lenAttr attrs "x" em cx.vp.w 0
          let uy := lenAttr attrs "y" em cx.vp.h 0
          if st.requests.size ≥ bud.requests then (st.lose (.budget "references"), out) else
          match target.item with
          | .text _ => (st, out)
          | .elem tns tname tattrs _ =>
          if tns != svgNs then (st, out) else
          let place := xf.compose (shift ux uy)
          if tname == "symbol" || tname == "svg" then
            let w := match Xml.Attr.get? attrs "" "width" with
              | some _ => lenAttr attrs "width" em cx.vp.w cx.vp.w
              | none => lenAttr tattrs "width" em cx.vp.w cx.vp.w
            let hh := match Xml.Attr.get? attrs "" "height" with
              | some _ => lenAttr attrs "height" em cx.vp.h cx.vp.h
              | none => lenAttr tattrs "height" em cx.vp.h cx.vp.h
            if w ≤ 0 || hh ≤ 0 then (st, out) else
            let vb := (Xml.Attr.get? tattrs "" "viewBox").bind viewBox?
            let par := ((Xml.Attr.get? tattrs "" "preserveAspectRatio").map par?).getD Par.default
            let m : Affine := match vb with
              | some v => viewMap v par 0 0 w hh
              | none => Affine.unit
            let vp : Viewport := match vb with
              | some v => { w := v.w, h := v.h }
              | none => { w, h := hh }
            let (st, k) := st.request { id, style := s, vp, children := true }
            let overflowHidden := match Xml.Attr.get? tattrs "" "overflow" with
              | some v => v.trimAscii.toString != "visible" && v.trimAscii.toString != "auto"
              | none => true
            let clip : Array Clip := if overflowHidden
              then #[{ geom := .rect 0 0 (spOf w) (spOf hh), rule := .nonzero }] else #[]
            let (clipR, st) := clipFor st none
            match clipR with
            | none => (st, out)
            | some c =>
              (st, out.append (wrap place c r.opacity
                #[.group Affine.unit clip Alpha.opaque #[.use k m]]))
          else
            let (st, k) := st.request { id, style := s, vp := cx.vp, children := false }
            let (clipR, st) := clipFor st none
            match clipR with
            | none => (st, out)
            | some c => (st, out.append (wrap place c r.opacity #[.use k Affine.unit]))
    | "text" =>
      let em := s.fontSize
      let ls (n : String) (base : Rat) : Array Rat :=
        (((Xml.Attr.get? attrs "" n).bind lengthList?).getD #[]).map (·.toPx em base)
      let pl : PosLists := { id := 0, x := ls "x" cx.vp.w, y := ls "y" cx.vp.h
                             dx := ls "dx" cx.vp.w, dy := ls "dy" cx.vp.h }
      let (pieces, losses, _) := piecesList env inner #[pl] (#[], #[], 1) kids.toList
      let st := losses.foldl St.lose st
      let st := if (Xml.Attr.get? attrs "" "rotate").isSome then st.lose (.attribute "rotate") else st
      let st := if (Xml.Attr.get? attrs "" "textLength").isSome then st.lose (.attribute "textLength") else st
      let chars := textChars pieces
      let (runs, st) := textRuns env inner st 0 0 chars
      let (clip, st) := clipFor st none
      match clip with
      | none => (st, out)
      | some c => (st, out.append (wrap xf c r.opacity runs))
    | "image" =>
      let href := (Xml.Attr.get? attrs "" "href").orElse fun _ => Xml.Attr.get? attrs xlinkNs "href"
      match href.bind fun h => rasterOf h s.smooth with
      | none => (st.lose (.resource "image"), out)
      | some ras =>
        let em := s.fontSize
        let x := lenAttr attrs "x" em cx.vp.w 0
        let y := lenAttr attrs "y" em cx.vp.h 0
        let w := lenAttr attrs "width" em cx.vp.w ras.pxW
        let h := lenAttr attrs "height" em cx.vp.h ras.pxH
        if w ≤ 0 || h ≤ 0 || ras.pxW == 0 || ras.pxH == 0 || !s.visible then (st, out) else
        let par := ((Xml.Attr.get? attrs "" "preserveAspectRatio").map par?).getD Par.default
        let m := viewMap { x := 0, y := 0, w := ras.pxW, h := ras.pxH } par x y w h
        -- The raster's unit square, bottom-left at its origin, onto the
        -- image's pixel grid: y flips, one frame unit per pixel.
        let unitToPx : Affine := ⟨(pxSp : Rat) * ras.pxW / 65536, 0, 0, -(pxSp : Rat) * ras.pxH / 65536,
          0, (pxSp : Rat) * ras.pxH⟩
        let k := st.rasters.size
        let st := { st with rasters := st.rasters.push ras }
        let clip : Array Clip := if par.slice && par.align.isSome
          then #[{ geom := .rect (spOf x) (spOf y) (spOf w) (spOf h), rule := .nonzero }] else #[]
        let (clipR, st) := clipFor st none
        match clipR with
        | none => (st, out)
        | some c =>
          (st, out.append (wrap xf c r.opacity #[.group Affine.unit clip Alpha.opaque
            #[.image k (m.compose unitToPx)]]))
    | "textPath" => (st.lose (.element "textPath"), out)
    | "foreignObject" => (st.lose (.element "foreignObject"), out)
    | _ =>
      let (geom, inRange) := shapeGeom name attrs s.fontSize cx.vp
      let st := if inRange then st else st.lose pathRangeLoss
      match geom with
      | none =>
        if ["rect", "circle", "ellipse", "line", "polyline", "polygon", "path"].contains name then (st, out)
        else (st.lose (.element name), out)
      | some g =>
        if !s.visible then (st, out) else
        let bbox := bboxOf g
        let (p, st) := paintsOf env inner st s bbox
        -- A line has no interior: `fill` has no effect on it (SVG 2 §10.5).
        let p := if name == "line" then { p with fill := none } else p
        let (clip, st) := clipFor st bbox
        match clip with
        | none => (st, out)
        | some c =>
          if p.fill.isNone && p.stroke.isNone then (st, out)
          else (st, out.append (wrap xf c r.opacity #[.draw g p.fill p.stroke]))

/-- Each node of a list onto `acc`; under a `switch`, only the first
whose conditions hold (SVG 2 §5.8.2). -/
public def walkList (env : Env) (bud : Budget) (cx : Ctx) (switch : Bool)
    (acc : St × Array (Node Run)) : List Xml.Item → St × Array (Node Run)
  | [] => acc
  | n :: rest =>
    if switch then
      match n with
      | .elem ns _ attrs _ =>
        if ns == svgNs && conditionsHold env attrs then walkOne env bud cx acc n
        else walkList env bud cx switch acc rest
      | .text _ => walkList env bud cx switch acc rest
    else walkList env bud cx switch (walkOne env bud cx acc n) rest

end

/-! ## The figure -/

mutual

-- conserves: none — an index of a tree's ids, which the walk reads.
/-- Every element with an id onto `m`, the first in document order winning
(`getElementById`), with its ancestors. -/
public def idsOne (m : Std.HashMap String Entry) (up : List Css.Subject) :
    Xml.Item → Std.HashMap String Entry
  | .text _ => m
  | n@(.elem _ name attrs kids) =>
    let m := match Xml.Attr.get? attrs "" "id" with
      | some id => if m.contains id then m else m.insert id { item := n, up := up }
      | none => m
    idsList m (subjectOf name attrs :: up) kids.toList

public def idsList (m : Std.HashMap String Entry) (up : List Css.Subject) :
    List Xml.Item → Std.HashMap String Entry
  | [] => m
  | n :: rest => idsList (idsOne m up n) up rest

end

/-- Every element of a tree with an id, with its ancestors. -/
public def indexIds (t : Xml.Item) : Std.HashMap String Entry := idsOne {} [] t

/-- Every `style` element's sheet, in document order, with what each said
outside the subset. -/
public def sheetsOf (t : Xml.Item) : Array Css.Rule × Array String :=
  let styles := (elemsOne #[] t).filter (·.1 == "style")
  styles.foldl (fun (rules, dropped) (_, text) =>
    match Css.parseSheet text with
    | .ok (rs, ds) => (rules ++ rs, dropped ++ ds)
    | .error why => (rules, dropped.push why)) (#[], #[])

mutual

-- conserves: none — a census of a tree's symbol uses.
/-- The symbols a node uses, onto `acc`. -/
public def usesOne (acc : Array Nat) : Node Run → Array Nat
  | .use k _ => acc.push k
  | .group _ _ _ kids => usesList acc kids.toList
  | .draw _ _ _ => acc
  | .stamp _ _ _ _ => acc
  | .image _ _ => acc
  | .label _ => acc
  | .words _ => acc

public def usesList (acc : Array Nat) : List (Node Run) → Array Nat
  | [] => acc
  | n :: rest => usesList (usesOne acc n) rest

end

/-- The symbols the requests painted, ordered so that each body uses only
symbols before it (`Figure.wf`): repeatedly take every request whose uses
are all placed. A request left over stands in a reference cycle; its uses
are dropped and the cycle named. Returns the order, old index to new. -/
public def orderRequests (bodies : Array (Array (Node Run))) : Array (Option Nat) × Bool := Id.run do
  let deps := bodies.map fun b => usesList #[] b.toList
  let mut placed : Array (Option Nat) := Array.replicate bodies.size none
  let mut next := 0
  for _ in [0:bodies.size + 1] do
    let mut progress := false
    for k in [0:bodies.size] do
      if (placed[k]?.join).isNone && ((deps[k]?.getD #[]).all fun j => (placed[j]?.join).isSome) then
        placed := placed.set! k (some next)
        next := next + 1
        progress := true
    if !progress then break
  return (placed, placed.all Option.isSome)

mutual

-- conserves: none — a renumbering of a tree's symbol uses.
/-- A tree with each use renumbered, a use of an unplaced symbol dropped. -/
public def renumberOne (order : Array (Option Nat)) (acc : Array (Node Run)) : Node Run → Array (Node Run)
  | .use k xf =>
    match order[k]?.join with
    | some j => acc.push (.use j xf)
    | none => acc
  | .group xf clips alpha kids => acc.push (.group xf clips alpha (renumberList order #[] kids.toList))
  | .draw g f s => acc.push (.draw g f s)
  | .stamp o xf f s => acc.push (.stamp o xf f s)
  | .image k xf => acc.push (.image k xf)
  | .label l => acc.push (.label l)
  | .words w => acc.push (.words w)

public def renumberList (order : Array (Option Nat)) (acc : Array (Node Run)) :
    List (Node Run) → Array (Node Run)
  | [] => acc
  | n :: rest => renumberList order (renumberOne order acc n) rest

end

/-- The root's size in pixels (SVG 2 §8.2's intrinsic size): its width and
height in any absolute unit, `em`/`ex` against its font size; a percentage
reads the viewBox (100% is the viewBox's own extent); without them, the
viewBox at one pixel per user unit; without that, CSS's 300 × 150. -/
public def rootSize (attrs : Array Xml.Attr) (em : Rat) : Rat × Rat :=
  let vb := (Xml.Attr.get? attrs "" "viewBox").bind viewBox?
  let dim (name : String) (fromVb : ViewBox → Rat) (dflt : Rat) : Rat :=
    match (Xml.Attr.get? attrs "" name).bind length? with
    | some l =>
      match l.unit with
      | .pct => match vb with
        | some v => l.value * fromVb v / 100
        | none => l.value * dflt / 100
      | _ => l.toPx em 0
    | none =>
      match vb with
      | some v => fromVb v
      | none => dflt
  let w := dim "width" (·.w) 300
  let h := dim "height" (·.h) 150
  -- One declared, the other from the viewBox's ratio.
  match vb, (Xml.Attr.get? attrs "" "width").bind length?, (Xml.Attr.get? attrs "" "height").bind length? with
  | some v, some _, none => (w, w * v.h / v.w)
  | some v, none, some _ => (h * v.w / v.h, h)
  | _, _, _ => (w, h)

/-- The words a figure's title gives it: the root's first `title` child's
text, trimmed. -/
public def titleOf (t : Xml.Item) : Option String :=
  match t with
  | .elem _ _ _ kids =>
    kids.findSome? fun k => match k with
      | .elem ns "title" _ _ => if ns == svgNs then
          let s := normalizeSpace (k.textOne "")
          if s.isEmpty then none else some s
        else none
      | _ => none
  | .text _ => none

/-- An import: the figure, what was dropped with no loss of ink (a note
each), whether the file animates, and whether it sets text. -/
public structure Import where
  fig : Figure Run
  notes : Array String
  animated : Bool
  text : Bool
  deriving Inhabited

/-- The root's attributes and children. -/
@[expose] public def rootParts : Xml.Item → Array Xml.Attr × Array Xml.Item
  | .elem _ _ attrs kids => (attrs, kids)
  | .text _ => (#[], #[])

/-- The root viewport's size in pixels, its font size read through the
cascade. -/
@[expose] public def rootPx (rules : Array Css.Rule) (attrs : Array Xml.Attr) : Rat × Rat :=
  let (d, _) := declsOf rules (subjectOf "svg" attrs) [] attrs
  rootSize attrs (computeStyle d Style.initial { w := 300, h := 150 } attrs).style.fontSize

/-- **The figure box an SVG tree reserves**: its root viewport, from the
origin, in `Sp` (`rootSize`). -/
@[expose] public def rootBox (t : Xml.Item) : Box :=
  let px := rootPx (sheetsOf t).1 (rootParts t).1
  ((0, 0), (spOf px.1, spOf px.2))

mutual

-- conserves: none — a measure: the nodes a list paints once its uses are
-- expanded, saturating at `cap`.
/-- The nodes one node paints expanded onto `acc`, a use counting its
symbol's expanded size (`sizes`), every sum held at `cap` at most. -/
@[expose] public def expandedOne (sizes : Array Nat) (cap : Nat) (acc : Nat) : Node Run → Nat
  | .use k _ => min cap (acc + 1 + (sizes[k]?.getD 0))
  | .group _ _ _ kids => expandedList sizes cap (min cap (acc + 1)) kids.toList
  | .draw _ _ _ | .stamp _ _ _ _ | .image _ _ | .label _ | .words _ => min cap (acc + 1)

@[expose] public def expandedList (sizes : Array Nat) (cap : Nat) (acc : Nat) : List (Node Run) → Nat
  | [] => acc
  | n :: rest => expandedList sizes cap (expandedOne sizes cap acc n) rest

end

mutual

-- conserves: none — a rewriting that drops every use, which a figure over
-- its expansion budget cannot carry.
/-- One node onto `acc`, its uses dropped. -/
@[expose] public def unuseOne (acc : Array (Node Run)) : Node Run → Array (Node Run)
  | .use _ _ => acc
  | .group xf clips alpha kids => acc.push (.group xf clips alpha (unuseList #[] kids.toList))
  | .draw g f st => acc.push (.draw g f st)
  | .stamp o xf f st => acc.push (.stamp o xf f st)
  | .image k xf => acc.push (.image k xf)
  | .label r => acc.push (.label r)
  | .words w => acc.push (.words w)

@[expose] public def unuseList (acc : Array (Node Run)) : List (Node Run) → Array (Node Run)
  | [] => acc
  | n :: rest => unuseList (unuseOne acc n) rest

end

/-- The expanded size of a body, its symbols' sizes read in order — a use
in symbol `j` names a lower symbol, so one pass sizes them all. -/
@[expose] public def expandedSize (symbols : Array (Array (Node Run))) (cap : Nat) (body : Array (Node Run)) : Nat :=
  let sizes := symbols.foldl (fun acc b => acc.push (expandedList acc cap 0 b.toList)) #[]
  expandedList sizes cap 0 body.toList

/-- **A drawing's uses held to the expansion budget**: within it, the
symbols and body as they stand; past it, the body with every use dropped and
no symbol — what the drawing paints itself — and whether it was past. -/
@[expose] public def boundUses (bud : Budget) (symbols : Array (Array (Node Run)))
    (body : Array (Node Run)) : Array (Array (Node Run)) × Array (Node Run) × Bool :=
  if expandedSize symbols (bud.expanded + 1) body > bud.expanded then (#[], unuseList #[] body.toList, true)
  else (symbols, body, false)

/-- **An accepted SVG tree as a figure** (`Svg.import_box_exact`: its box
is the root viewport). -/
public def importTree (t : Xml.Item) (lang : String := "en") (bud : Budget := Budget.standard) : Import :=
  let ids := indexIds t
  let (rules, dropped) := sheetsOf t
  let env : Env := { ids, rules, lang }
  let (attrs, rootKids) := rootParts t
  let rootSubject := subjectOf "svg" attrs
  let (d, problems) := declsOf rules rootSubject [] attrs
  let (w, h) := rootPx rules attrs
  let vb := (Xml.Attr.get? attrs "" "viewBox").bind viewBox?
  let par := ((Xml.Attr.get? attrs "" "preserveAspectRatio").map par?).getD Par.default
  let vp : Viewport := match vb with
    | some v => { w := v.w, h := v.h }
    | none => { w, h }
  let r := computeStyle d Style.initial vp attrs
  let st0 : St := { losses := #[], notes := #[], rasters := #[], requests := #[], nodes := 0
                    animated := false, text := false }
  let st0 := (dropped ++ problems).foldl (fun s p => s.lose (.property s!"style: {p}")) st0
  let st0 := r.losses.foldl St.lose st0
  let cx : Ctx := { up := [rootSubject], parent := r.style, vp }
  let (st, body) := walkList env bud cx false (st0, #[]) rootKids.toList
  -- The requests, read one by one; each may make more, under the budget.
  let (st, bodies) := Id.run do
    let mut st := st
    let mut bodies : Array (Array (Node Run)) := #[]
    for k in [0:bud.requests] do
      if k ≥ st.requests.size then break
      let req := st.requests[k]?.getD default
      let some e := ids.get? req.id | do bodies := bodies.push #[]; continue
      let rcx : Ctx := { up := e.up, parent := req.style, vp := req.vp }
      let (st', b) := if req.children then
          match e.item with
          | .elem _ name tattrs kids =>
            walkList env bud { rcx with up := subjectOf name tattrs :: e.up } false (st, #[]) kids.toList
          | .text _ => (st, #[])
        else walkOne env bud rcx (st, #[]) e.item
      st := st'
      bodies := bodies.push b
    return (st, bodies)
  let (order, complete) := orderRequests bodies
  let st := if complete then st else st.lose (.element "use cycle")
  let symbolsByNew : Array (Array (Node Run)) := Id.run do
    let mut out : Array (Array (Node Run)) := Array.replicate bodies.size #[]
    for h : k in [0:bodies.size] do
      if let some j := order[k]?.join then
        out := out.set! j (renumberList order #[] bodies[k].toList)
    return out
  let placed := (order.filterMap id).size
  let symbols := symbolsByNew.extract 0 placed
  let body := renumberList order #[] body.toList
  -- Uses nested in uses multiply: past the budget the drawing keeps what
  -- it paints itself and drops its uses, the drop named (`expand_between`).
  let bounded := boundUses bud symbols body
  let st := if bounded.2.2 then st.lose (.budget "expanded uses") else st
  let m := match vb with
    | some v => viewMap v par 0 0 w h
    | none => Affine.unit
  let wsp := spOf w
  let hsp := spOf h
  let flip : Affine := ⟨1, 0, 0, -1, 0, (hsp : Rat)⟩
  let rootXf := flip.compose m
  let clip := r.clipPath.isSome
  let st := if clip then st.lose (.property "clip-path on the root") else st
  let nodes := #[Node.group rootXf #[] (mulAlpha r.opacity 1000) bounded.2.1]
  { fig := { box := ((0, 0), (wsp, hsp)), clipToBox := true, nodes, outlines := #[]
             symbols := bounded.1, rasters := st.rasters, title := titleOf t, losses := st.losses }
    notes := st.notes, animated := moves t, text := st.text }

/-- The import's figure is a root group over the body its uses were held
to, with the symbols held with them: what `expand_between` reads. -/
public theorem importTree_shape (t : Xml.Item) (lang : String) (bud : Budget) :
    ∃ (symbols : Array (Array (Node Run))) (body : Array (Node Run)) (xf : Affine) (a : Alpha),
      (importTree t lang bud).fig.symbols = (boundUses bud symbols body).1 ∧
        (importTree t lang bud).fig.nodes = #[Node.group xf #[] a (boundUses bud symbols body).2.1] :=
  ⟨_, _, _, _, rfl, rfl⟩

/-- **The import's box is the root viewport** (`_exact`): what layout
reserves for an SVG is the size its root declares — its width and height,
else its viewBox at one pixel per unit, else 300 × 150 — in `Sp`, from the
origin, whatever the figure paints. -/
public theorem import_box_exact (t : Xml.Item) (lang : String) (bud : Budget) :
    (importTree t lang bud).fig.box = rootBox t := by
  simp only [importTree, rootBox]

/-- What an import answers for bytes: the judge's refusal, or the figure
with the losses that keep it from being exact. -/
public inductive Verdict where
  | exact (i : Import)
  | lossy (i : Import)
  | refused (r : Refused)
  deriving Inhabited

/-- **SVG bytes as a figure**: judged (`judge`), then imported. -/
public def importBytes (bytes : ByteArray) (lang : String := "en") : Verdict :=
  match judge bytes with
  | .error r => .refused r
  | .ok t =>
    let i := importTree t lang
    if i.fig.losses.isEmpty then .exact i else .lossy i

end LeanTex.Core.Svg
