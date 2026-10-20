module

public import LeanTex.Core.Gfx
public import LeanTex.Core.Xml
public import LeanTex.Core.Css
public import LeanTex.Core.CssColor
public import LeanTex.Core.PathData
public import LeanTex.Core.SvgJudge
import LeanTex.Core.Image
public import Std.Data.HashMap
import LeanTex.Core.DeriveBEq
import LeanTex.Core.Split

/-! SVG read into the vector figure model: an accepted tree's viewports, shapes, paints, text and
symbol uses, every meaning it cannot give a keyed loss, and a dropped link a note. -/

namespace LeanTex.Core.Svg

open LeanTex.Core LeanTex.Core.Dim LeanTex.Core.Gfx

/-- One user unit, the CSS pixel: 0.75 pt. -/
@[expose] public def pxSp : Length := px 1

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

/-- How many CSS pixels one unit is (CSS Values 4 §6.2); font- and box-relative units are the caller's. -/
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
public structure SvgLength where
  value : Rat
  unit : LenUnit
  deriving Repr, BEq, Inhabited

/-- A number alone, white space around it allowed. -/
public def num? (s : String) : Option Rat :=
  (PathData.number (PathData.skipWs s.toList)).bind fun (d, rest) =>
    if (PathData.skipWs rest).isEmpty then some d.toRat else none

/-- A length: a decimal, then a unit suffix, white space around it. -/
@[expose] public def length? (s : String) : Option SvgLength :=
  (PathData.number (PathData.skipWs s.toList)).bind fun (d, rest) =>
    let suffix := String.ofList (rest.takeWhile (!PathData.isWsp ·))
    if (PathData.skipWs (rest.dropWhile (!PathData.isWsp ·))).isEmpty then
      (LenUnit.ofSuffix suffix).map fun u => { value := d.toRat, unit := u }
    else none

/-- A length in CSS pixels against the font size `em` and the percentage basis `base`; `1ex` is half an em. -/
@[expose] public def SvgLength.toPx (l : SvgLength) (em base : Rat) : Rat :=
  match l.unit with
  | .em => l.value * em
  | .ex => l.value * em / 2
  | .pct => l.value * base / 100
  | u => l.value * u.factor

/-- Pixels as `Length` of user space, rounded once, half away from zero. -/
@[expose] public def pxLen (px : Rat) : Length := Length.ofRatRound (px * pxSp.toRat)

/-- The fixed-point factor a bounding-box frame carries: one big point, the side of a raster's
unit square. -/
private def bboxScale : Rat := (bp 1).toRat

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
public def lengthList? (s : String) : Option (Array SvgLength) :=
  let parts := (s.replace "," " ").splitOn " " |>.filter (!·.trimAscii.isEmpty)
  parts.toArray.mapM length?

/-- A rotation by `deg` degrees, exact on every multiple of a right angle. -/
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
@[expose] public def shift (x y : Rat) : Affine := ⟨1, 0, 0, 1, x * pxSp.toRat, y * pxSp.toRat⟩

/-- One transform function (SVG 2 §8.5), its arguments in user units. -/
public def transformFn (name : String) (args : Array Rat) : Option Affine :=
  match name, args.toList with
  | "matrix", [a, b, c, d, e, f] => some ⟨a, b, c, d, e * pxSp.toRat, f * pxSp.toRat⟩
  | "translate", [x] => some (shift x 0)
  | "translate", [x, y] => some (shift x y)
  | "scale", [s] => some (Affine.scale s s)
  | "scale", [x, y] => some (Affine.scale x y)
  | "rotate", [a] => some (rotation a)
  | "rotate", [a, cx, cy] => some ((shift cx cy).compose ((rotation a).compose (shift (-cx) (-cy))))
  | "skewX", [a] => some ⟨1, 0, tangentOf a, 1, 0, 0⟩
  | "skewY", [a] => some ⟨1, tangentOf a, 0, 1, 0, 0⟩
  | _, _ => none

/-- A transform list composed left to right, the first function outermost; an unreadable list is none. -/
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

/-- The viewBox transform's scale on each axis (SVG 2 §8.2), equal unless the alignment is `none`. -/
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
  ⟨sx, 0, 0, sy, (vx + ox - vb.x * sx) * pxSp.toRat, (vy + oy - vb.y * sy) * pxSp.toRat⟩

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

/-- A paint as the cascade leaves it (SVG 2 §13.2): none, a colour with its
alpha, the `color` property's, or a paint server with its fallback. -/
public inductive PaintSpec where
  | none
  | color (c : Ir.Color) (alpha : Nat)
  | current
  | url (id : String) (fallback : Option PaintSpec)
  deriving Repr, Inhabited

deriving_structural_beq PaintSpec

@[expose] public def black : Ir.Color := { r := 0, g := 0, b := 0, origin := .declared }

/-- The inherited properties the importer reads, computed. -/
public structure Style where
  fill : PaintSpec
  fillOpacity : Nat
  fillRule : Rule
  stroke : PaintSpec
  strokeOpacity : Nat
  strokeWidth : Length
  cap : Cap
  join : Join
  miter : Rat
  dash : Array Length
  dashOffset : Length
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

/-- An element's declarations from every source of the cascade: property, key, value. -/
public abbrev Decls := Array (String × Css.Key × String)

/-- How the importer treats a property: read with its meaning, inert, or a loss unless its value
changes nothing. -/
public inductive Treatment where
  | honoured
  | inert
  | lossUnless (harmless : List String)
  deriving Repr, BEq, Inhabited

/-- Every property the importer reads or reports wherever it is set, with its treatment (SVG 2
§6.6); those it reports only from a sheet are `cssLost`'s. -/
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

/-- The properties CSS may set that the importer reads only as attributes or not at all, each with
the values that change nothing. -/
@[expose] public def cssLost : List (String × List String) :=
  (["x", "y", "width", "height", "cx", "cy", "r", "rx", "ry", "d"].map (·, [])) ++
  (["transform", "translate", "rotate", "scale", "offset-path", "mask-image",
    "backdrop-filter"].map (·, ["none"])) ++
  (["offset", "offset-distance", "offset-rotate", "offset-anchor", "offset-position",
    "mask-mode", "mask-position", "mask-size", "mask-repeat", "mask-origin", "mask-clip",
    "mask-composite"].map (·, [])) ++
  [("text-transform", ["none"]), ("text-decoration-line", ["none"]),
   ("text-shadow", ["none"]), ("font-variant-caps", ["normal"]),
   ("font-variant-ligatures", ["normal"]), ("font-variant-numeric", ["normal"]),
   ("font-variant-east-asian", ["normal"]), ("font-variant-position", ["normal"]),
   ("font-variant-alternates", ["normal"]), ("font-feature-settings", ["normal"]),
   ("font-variation-settings", ["normal"]), ("font-kerning", ["auto", "normal"]),
   ("background", ["none", "transparent"]), ("background-color", ["transparent"]),
   ("background-image", ["none"]), ("border", ["none", "0"]), ("box-shadow", ["none"]),
   ("outline", ["none", "0"])]

/-- The system font keywords: a face only the host names. -/
@[expose] public def systemFonts : List String :=
  ["caption", "icon", "menu", "message-box", "small-caption", "status-bar"]

/-- The longhands a `font` shorthand sets (CSS Fonts 4 §2.7), unsaid ones reset; `none` for a value
this reader does not read. -/
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
      (splitWhere c Css.isWs).filter (!·.isEmpty) |>.toArray).getD #[]
    id := Xml.Attr.get? attrs "" "id" }

/-- What an element declares: its presentation attributes, the sheet rules matching it, and its
`style` attribute, by level. -/
public def declsOf (ix : Css.RuleIndex) (subject : Css.Subject) (up : List Css.Subject)
    (attrs : Array Xml.Attr) : Decls × Array Css.Unread := Id.run do
  let mut out : Decls := #[]
  let mut problems : Array Css.Unread := #[]
  for h : i in [0:attrs.size] do
    let a := attrs[i]
    if a.ns == "" && properties.contains a.name then
      out := out.push (a.name, { important := false, level := 0, spec := (0, 0, 0), order := i },
        a.value.trimAscii.toString)
  let mut best : Std.HashMap Nat (Nat × Nat × Nat) := {}
  for (i, j) in ix.candidates subject up do
    let some s := (ix.rules[i]?.bind (·.selectors[j]?)) | continue
    if s.matches subject up then
      let sp := s.specificity
      match best.get? i with
      | none => best := best.insert i sp
      | some b =>
        if Css.Key.lt { important := false, level := 1, spec := b, order := 0 }
            { important := false, level := 1, spec := sp, order := 0 } then
          best := best.insert i sp
  for (i, sp) in best.toArray.qsort (·.1 < ·.1) do
    let some r := ix.rules[i]? | continue
    let base := ix.offsets[i]?.getD 0
    for h : k in [0:r.decls.size] do
      let d := r.decls[k]
      out := out.push (d.prop, { important := d.important, level := 1, spec := sp, order := base + k },
        d.value)
  if let some st := Xml.Attr.get? attrs "" "style" then
    match Css.parseDecls st with
    | .ok ds =>
      for h : j in [0:ds.size] do
        let d := ds[j]
        out := out.push (d.prop, { important := d.important, level := 2, spec := (0, 0, 0), order := j },
          d.value)
    | .error (.unsupported why) => problems := problems.push why
    | .error (.refused why) => problems := problems.push why
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

/-- A property's value through the cascade, reading `inherit`, `initial` and `unset` (CSS Cascading 4
§7.3), else the parent's or the initial value. -/
public def pick {α : Type} (d : Decls) (prop : String) (inherited : Bool) (parent initial : α)
    (parse : String → Option α) : α :=
  let keyword (v : String) : Option α :=
    match v.toLower with
    | "inherit" => some parent
    | "initial" => some initial
    | "unset" => some (if inherited then parent else initial)
    | _ => none
  let read (v : String) : Option α := (keyword v).orElse fun _ => parse v
  -- An unreadable value is dropped before it can win, as CSS drops it.
  let valid := (d.filterMap fun (p, k, v) => if p == prop && (read v).isSome then some (k, v) else none)
  match (Css.cascade valid).bind read with
  | some v => v
  | none => if inherited then parent else initial

@[expose] public def declares (d : Decls) (prop : String) : Bool := d.any (·.1 == prop)

/-- A colour value with its alpha, `currentColor` the caller's. -/
public def colorValue? (current : Ir.Color × Nat) (s : String) : Option (Ir.Color × Nat) :=
  if s.trimAscii.toString.toLower == "currentcolor" then some current
  else (CssColor.parse s).map fun v => (v.color.declared, v.alpha)

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
        else (CssColor.parse fb).map fun v => .color v.color.declared v.alpha
      some (.url (inner.drop 1).toString fallback)
    | [] => none
  else (CssColor.parse t).map fun v => .color v.color.declared v.alpha

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

/-- The generic families CSS Fonts 4 §2.1.5 names. -/
@[expose] public def generics : List String :=
  ["serif", "sans-serif", "monospace", "cursive", "fantasy", "system-ui", "ui-serif",
   "ui-sans-serif", "ui-monospace", "ui-rounded", "math", "emoji", "fangsong"]

/-- The keywords no unquoted family name may hold (CSS Values 4 §4.2, CSS Fonts 4 §2.1). -/
@[expose] public def reservedFamilyWords : List String :=
  ["inherit", "initial", "unset", "revert", "revert-layer", "default"]

/-- One family of a `font-family` list (CSS Fonts 4 §2.1): a string its quote closes, its text
unescaped, or identifiers joined by single blanks, unescaped, a generic family's keyword in lower
case; `none` for anything else. -/
public def family? (t : String) : Option String :=
  match Css.atoms t with
  | [q :: body] =>
    if (q == '"' || q == '\'') && Css.closedAtom (q :: body) && body.getLast? == some q then
      some (String.ofList (Css.unescape body.dropLast))
    else ident? t
  | _ => ident? t
where
  ident? (t : String) : Option String :=
    let words := Css.words t
    let names := words.map fun w => String.ofList (Css.unescape w.toList)
    if words.isEmpty || !words.all (Css.identifier ·.toList) ||
        names.any (reservedFamilyWords.contains ·.toLower) then none
    else match names with
      | [n] => some (if generics.contains n.toLower then n.toLower else n)
      | _ => some (" ".intercalate names)

/-- A `font-family` list, its comments removed and cut at its commas outside strings and blocks,
each family as `family?` reads it; `none` when one is no family, as CSS then drops the
declaration. -/
public def families? (s : String) : Option (Array String) := do
  let mut out : Array String := #[]
  for f in Css.splitList ',' (Css.stripComments s) do
    out := out.push (← family? f.trimAscii.toString)
  if out.isEmpty then none else some out

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

/-- A `transform-origin` (CSS Transforms 1 §6.1) in user units, against the reference box `(w, h)`. -/
public def origin? (em w h : Rat) (s : String) : Option (Rat × Rat) :=
  let toks := (splitWhere s.trimAscii.toString PathData.isWsp).filter
    (!·.isEmpty)
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

/-- One element's computed style: its declarations over its parent's style, in the viewport `vp`. -/
public def computeStyle (d : Decls) (parent : Style) (vp : Viewport) (attrs : Array Xml.Attr) : Read :=
  let fontSize := pick d "font-size" true parent.fontSize Style.initial.fontSize (fontSize? parent.fontSize)
  let len (base : Rat) (s : String) : Option Length :=
    (length? s).bind fun l => let v := l.toPx fontSize base; if v < 0 then none else some (pxLen v)
  let color := pick d "color" true parent.color Style.initial.color (colorValue? parent.color)
  let dash? (s : String) : Option (Array Length) :=
    if s.trimAscii.toString.toLower == "none" then some #[] else
    (lengthList? s).bind fun ls =>
      let vs := ls.map fun l => pxLen (l.toPx fontSize vp.diag)
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
        (length? s).map fun l => pxLen (l.toPx fontSize vp.diag)
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

/-- A point of user space, in `Length`. -/
@[expose] public def pt (x y : Rat) : Pt := (pxLen x, pxLen y)

/-- Path commands as absolute subpaths of user space, quadratics elevated and arcs as cubics. -/
public def subpathsOf (cmds : Array PathData.Cmd) : Array Subpath := Id.run do
  let mut done : Array Subpath := #[]
  let mut cur : Option Subpath := none
  let mut px : Rat := 0
  let mut py : Rat := 0
  let mut sx : Rat := 0
  let mut sy : Rat := 0
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
          (Kit.arcEndpoint (pt px py) (pxLen rx.toRat).abs (pxLen ry.toRat).abs φ large sweep
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

/-- The loss of a path cut short by a number past the reader's range. -/
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
    if rx ≤ 0 || ry ≤ 0 then some (.rect (pxLen x) (pxLen y) (pxLen w) (pxLen h))
    else some (.path #[Kit.roundedRect (pxLen x) (pxLen y) (pxLen w) (pxLen h) (pxLen rx) (pxLen ry)])
  | "circle" =>
    let r := l "r" vp.diag
    if r ≤ 0 then none else some (.ellipse (pxLen (l "cx" vp.w)) (pxLen (l "cy" vp.h)) (pxLen r) (pxLen r))
  | "ellipse" =>
    let rx := l "rx" vp.w
    let ry := l "ry" vp.h
    if rx ≤ 0 || ry ≤ 0 then none
    else some (.ellipse (pxLen (l "cx" vp.w)) (pxLen (l "cy" vp.h)) (pxLen rx) (pxLen ry))
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

/-- A basic shape's geometry (SVG 2 §10): `none` where it draws nothing, flagged false where a
number past the reader's range cut a path short. -/
public def shapeGeom (name : String) (attrs : Array Xml.Attr) (em : Rat) (vp : Viewport) :
    Option Geom × Bool :=
  if name == "path" then
    let (cmds, stop) := PathData.parse ((Xml.Attr.get? attrs "" "d").getD "")
    let subs := subpathsOf cmds
    (if subs.isEmpty then none else some (.path subs), stop != .range)
  else (basicGeom name attrs em vp, true)

/-- A geometry's object bounding box, by its control points (SVG 2 §8.10). -/
public def bboxOf (g : Geom) : Option Box := g.hull

/-- An element the walk reaches by id, with its ancestors innermost first. -/
public structure Entry where
  item : Xml.Item
  up : List Css.Subject
  /-- The ancestors' items, innermost first, for inherited properties. -/
  upItems : List (String × Array Xml.Attr)
  deriving Inhabited

/-- What every step of the walk reads: the elements by id, the sheets'
rules, the document language. -/
public structure Env where
  ids : Std.HashMap String Entry
  rules : Css.RuleIndex
  lang : String

/-- A `use` the walk met: the element it names, the style its clone inherits, and whether it reads
the element's children. -/
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
  /-- The requests by the id each names, to share an equal one. -/
  requestIds : Std.HashMap String (Array Nat)
  nodes : Nat
  animated : Bool
  text : Bool
  deriving Inhabited

/-- The most nodes one import emits and references it reads; past either, drawing stops and the
budget is named. -/
public structure Budget where
  nodes : Nat
  requests : Nat
  /-- The nodes a figure may paint once its uses are expanded. -/
  expanded : Nat
  deriving Repr, Inhabited

@[expose] public def Budget.standard : Budget :=
  { nodes := 2000000, requests := 100000, expanded := 200000 }

/-- The request a `use` makes, shared with an equal one already made. -/
public def St.request (s : St) (r : Request) : St × Nat :=
  let same := s.requestIds.getD r.id #[]
  match same.find? (fun k => s.requests[k]? == some r) with
  | some k => (s, k)
  | none =>
    let k := s.requests.size
    ({ s with requests := s.requests.push r, requestIds := s.requestIds.insert r.id (same.push k) }, k)

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
  let mut acc : UInt32 := 0
  let mut bits : UInt32 := 0
  for c in s.toList do
    if c == '=' then break
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then continue
    let some v := val c | return none
    acc := ((acc <<< 6) ||| v.toUInt32) &&& 0xFFFFFF
    bits := bits + 6
    if bits ≥ 8 then
      bits := bits - 8
      out := out.push ((acc >>> bits) &&& 0xFF).toUInt8
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
      match Hex.val? (Xml.at? b (i + 1)), Hex.val? (Xml.at? b (i + 2)) with
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

/-- A gradient's own attribute, or the first its `href` chain supplies (SVG 2 §14.2.3), a cycle cut. -/
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

/-- A gradient's stops, its own or the first in its `href` chain, with the element that holds them. -/
public def gradientStops (env : Env) (start : Entry) : Array Xml.Item × Entry := Id.run do
  let mut cur := start
  for _ in [0:env.ids.size + 1] do
    match cur.item with
    | .elem _ _ attrs kids =>
      let stops := kids.filter fun k => match k with
        | .elem ns n _ _ => ns == svgNs && n == "stop"
        | .text _ => false
      if !stops.isEmpty then return (stops, cur)
      let href := (Xml.Attr.get? attrs "" "href").orElse fun _ => Xml.Attr.get? attrs xlinkNs "href"
      match href with
      | some h =>
        match env.ids.get? ((normalizeSpace h).drop 1).toString with
        | some e => cur := e
        | none => return (#[], cur)
      | none => return (#[], cur)
    | .text _ => return (#[], cur)
  return (#[], cur)

/-- The `color` an element computes down its ancestors; the lists hold the element and its
ancestors, innermost first. -/
public def colorDown (ix : Css.RuleIndex) : List (String × Array Xml.Attr) → List Css.Subject →
    Ir.Color × Nat
  | (_, attrs) :: items, s :: up =>
    let parent := colorDown ix items up
    let (d, _) := declsOf ix s up attrs
    pick d "color" true parent (black, 1000) (colorValue? parent)
  | _, _ => (black, 1000)

/-- A stop's offset in 65536ths, clamped (SVG 2 §14.4.2). -/
public def stopOffset (s : String) : Nat :=
  let t := s.trimAscii.toString
  let q := if t.endsWith "%" then ((num? (t.dropEnd 1).toString).getD 0) / 100 else (num? t).getD 0
  let q := if q < 0 then 0 else if q > 1 then 1 else q
  (q * 65536 + 1 / 2).floor.toNat

/-- A paint server resolved for a fill box `bbox`: a gradient, a solid colour, nothing, or the loss it meets. -/
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
  let mut stops : Array Stop := #[]
  let mut last := 0
  let (stopItems, owner) := gradientStops env e
  let (oname, oattrs) := match owner.item with
    | .elem _ n a _ => (n, a)
    | .text _ => ("", #[])
  let ownerUp := subjectOf oname oattrs :: owner.up
  let ownerColor := colorDown env.rules ((oname, oattrs) :: owner.upItems) ownerUp
  for s in stopItems do
    let .elem _ _ sattrs _ := s | continue
    let (d, _) := declsOf env.rules (subjectOf "stop" sattrs) ownerUp sattrs
    let stopColor := pick d "color" true ownerColor (black, 1000) (colorValue? ownerColor)
    let col := pick d "stop-color" false (black, 1000) (black, 1000) (colorValue? stopColor)
    let op := pick d "stop-opacity" false 1000 1000 opacity?
    if op * col.2 / 1000 < 1000 then throw (.property "stop-opacity")
    let off := max last (stopOffset ((Xml.Attr.get? sattrs "" "offset").getD "0"))
    last := off
    stops := stops.push { offset := ⟨min off 65536, by omega⟩, color := col.1 }
  if stops.isEmpty then return none
  if let #[only] := stops then return some (.solid only.color, alpha)
  let bboxUnits := ((attr "gradientUnits").getD "objectBoundingBox").trimAscii.toString != "userSpaceOnUse"
  let gxf := ((attr "gradientTransform").bind transform?).getD Affine.unit
  let frameOpt : Option (Affine × Rat × Rat × Rat) :=
    if bboxUnits then
      bbox.bind fun ((x0, y0), (x1, y1)) =>
        if x1 ≤ x0 || y1 ≤ y0 then none
        else some (⟨(x1 - x0).toRat / bboxScale, 0, 0, (y1 - y0).toRat / bboxScale,
          x0.toRat, y0.toRat⟩, bboxScale, (1 : Rat), (1 : Rat))
    else some (Affine.unit, pxSp.toRat, cx.vp.w, cx.vp.h)
  let some (frame, scale, bw, bh) := frameOpt | return none
  let coord (n : String) (dflt : Rat) (base : Rat) : Length :=
    let v : Rat := match (attr n).bind length? with
      | some l => if bboxUnits then (if l.unit == .pct then l.value / 100 else l.value)
        else l.toPx cx.parent.fontSize base
      | none => dflt * (if bboxUnits then 1 else base)
    let s := v * scale
    Length.ofRatFloor (s + 1 / 2)
  let gxf := if bboxUnits then { gxf with e := gxf.e / pxSp.toRat * bboxScale, f := gxf.f / pxSp.toRat * bboxScale }
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
    -- The focal circle must lie inside the end circle, the one geometry both formats draw alike.
    let dx := fx - c1.1
    let dy := fy - c1.2
    if Length.ofUnits (Nat.sqrt (dx * dx + dy * dy).toNat : Int) + r0 ≥ r1 then
      throw (.attribute "fx")
    return some (.gradient (.radial (fx, fy) r0 c1 r1 stops xf), alpha)

/-- A paint spec as a model paint and its alpha; a failing server falls back as SVG 2 §13.2.3 says. -/
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

/-- A `clip-path` reference resolved for an element: the clip and its frame relative to the
element's, or what stops it; `none` inside is an empty clip. -/
public def clipOf (env : Env) (cx : Ctx) (id : String) (bbox : Unit → Except Gfx.Loss (Option Box)) :
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
  let unitOpt : Option Affine ←
    if units == "objectBoundingBox" then do
      let b ← bbox ()
      pure (b.map fun ((x0, y0), (x1, y1)) =>
        ⟨(x1 - x0).toRat / pxSp.toRat, 0, 0, (y1 - y0).toRat / pxSp.toRat,
          x0.toRat, y0.toRat⟩)
    else pure (some Affine.unit)
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

/-- One piece of a text element's content: its text and the style it is set in. -/
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

-- conserves: none — a flattening of a text element's content into pieces.
/-- A text element's content flattened into pieces with their style and position lists; a `tspan`
opens its own lists. -/
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

/-- The characters a text element sets after SVG 2 §11.11's white-space rules, each positioned by
its innermost positioning element. -/
public def textChars (pieces : Array (Piece × Array PosLists)) : Array TChar := Id.run do
  let mut out : Array TChar := #[]
  let mut counts : Std.HashMap Nat Nat := {}
  let mut prevSpace := true
  for (p, lists) in pieces do
    for c in p.text.toList do
      let c := if c == '\t' then ' ' else c
      let keep : Option Char :=
        let c := if c == '\n' || c == '\r' then ' ' else c
        if p.style.preserve then some c
        else if c == ' ' && prevSpace then none
        else some c
      let some ch := keep | continue
      prevSpace := ch == ' '
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
  let mut n := out.size
  for _ in [0:out.size] do
    if n > 0 && (out[n - 1]?.any fun t => t.c == ' ' && !t.style.preserve) then n := n - 1 else break
  return out.extract 0 n

/-- Two paints alike field by field, a colour's PDF rider included. -/
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

/-- Whether a character's script is set right to left or joined by contextual shaping. -/
@[expose] public def needsShaping (c : Char) : Bool :=
  let n := c.toNat
  (0x0590 ≤ n && n ≤ 0x08FF) || (0x0900 ≤ n && n ≤ 0x0DFF) || (0x0F00 ≤ n && n ≤ 0x109F) ||
    (0x1780 ≤ n && n ≤ 0x18AF) || (0xFB1D ≤ n && n ≤ 0xFDFF) || (0xFE70 ≤ n && n ≤ 0xFEFE) ||
    (0x10800 ≤ n && n ≤ 0x10FFF) || (0x1E800 ≤ n && n ≤ 0x1EFFF)

/-- The loss of text set in logical order, unjoined, where its script needs shaping. -/
@[expose] public def shapingLoss : Gfx.Loss := .value "text in a right-to-left or joined script"

/-- A text element's runs: a new run where a character is positioned or its style changes, a new
chunk at each absolute x. -/
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
      | some ax => ⟨1, 0, 0, -1, (ax + c.dx) * pxSp.toRat, yy * pxSp.toRat⟩
      | none => ⟨1, 0, 0, -1, c.dx * pxSp.toRat, yy * pxSp.toRat⟩
    -- A transparent fill paints nothing; the run still advances what follows.
    let fill := p.fill.filter (·.alpha.val != 0)
    if text.any needsShaping then st := st.lose shapingLoss
    if s.visible && !text.isEmpty then
      out := out.push (.label { xf, follows, size := pxLen s.fontSize, text
                                face := { families := s.families, weight := s.weight, italic := s.italic }
                                anchor := s.anchor, fill, stroke := p.stroke, lang := s.lang })
      -- Engine-set text paints a solid fill only.
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

/-- Whether an element's conditional attributes hold (SVG 2 §5.8.4); no extension is supported. -/
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

@[expose] public def ownTransform (attrs : Array Xml.Attr) : Affine :=
  ((Xml.Attr.get? attrs "" "transform").bind transform?).getD Affine.unit

/-- Wraps what an element paints in the group its transform, clip and opacity make, if any. -/
public def wrap (xf : Affine) (clip : Option (Affine × Clip)) (alpha : Nat) (kids : Array (Node Run)) :
    Array (Node Run) :=
  let a := mulAlpha alpha 1000
  -- A transparent group paints nothing, and its text is none of the figure's words.
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

/-- Whether a tree holds an animation element, read off the authored tree. -/
@[expose] public def moves (t : Xml.Item) : Bool := (elemsOne #[] t).any (animations.contains ·.1)

/-- The loss of a clip in object units on an element whose box is known only once the figure is set. -/
@[expose] public def unmeasuredClip (what : String) : Gfx.Loss :=
  .value s!"clip-path in object units on {what}"

/-- The geometry box of what a container painted, or the loss of an object-unit clip where it sets
text or uses a symbol. -/
public def bodyBox (body : Array (Node Run)) : Except Gfx.Loss (Option Box) :=
  let fig : Figure Run := { box := ((0, 0), (0, 0)), clipToBox := false, nodes := body, outlines := #[]
                            symbols := #[], rasters := #[], title := none, losses := #[] }
  if Node.useFreeList body.toList && fig.labels.isEmpty then
    .ok (hullOf (Mark.geomBox rasterUnit) fig.marks)
  else .error (unmeasuredClip "a group holding text or a use")

mutual

-- conserves: none — a measure of an element's geometry box.
/-- The geometry box an element adds to `acc` in its parent's frame (SVG 2 §8.10, without stroke,
clip or filter). -/
public def itemBoxOne (env : Env) (cx : Ctx) (acc : Except Gfx.Loss (Option Box)) :
    Xml.Item → Except Gfx.Loss (Option Box)
  | .text _ => acc
  | .elem ns name attrs kids =>
    match acc with
    | .error l => .error l
    | .ok b =>
      if ns != svgNs || animations.contains name || definitions.contains name then .ok b else
      let (d, _) := declsOf env.rules (subjectOf name attrs) cx.up attrs
      let r := computeStyle d cx.parent cx.vp attrs
      if !r.display then .ok b else
      let xf := aroundOrigin (ownTransform attrs) r.origin
      let em := r.style.fontSize
      match name with
      | "g" | "a" =>
        let inner : Ctx := { up := subjectOf name attrs :: cx.up, parent := r.style, vp := cx.vp }
        match itemBoxList env inner (.ok none) kids.toList with
        | .error l => .error l
        | .ok kb => .ok (Box.joinOpt b (kb.map (Box.image xf)))
      | "image" =>
        let x := lenAttr attrs "x" em cx.vp.w 0
        let y := lenAttr attrs "y" em cx.vp.h 0
        let w := lenAttr attrs "width" em cx.vp.w 0
        let h := lenAttr attrs "height" em cx.vp.h 0
        if w ≤ 0 || h ≤ 0 then .ok b
        else .ok (Box.joinOpt b (some (Box.image xf ((pxLen x, pxLen y), (pxLen (x + w), pxLen (y + h))))))
      | "use" | "text" | "svg" | "switch" | "foreignObject" | "textPath" =>
        .error (unmeasuredClip "a use whose content holds text, a use or a viewport")
      | _ =>
        match (shapeGeom name attrs em cx.vp).1 with
        | some g => .ok (Box.joinOpt b ((bboxOf g).map (Box.image xf)))
        | none => .ok b

public def itemBoxList (env : Env) (cx : Ctx) (acc : Except Gfx.Loss (Option Box)) :
    List Xml.Item → Except Gfx.Loss (Option Box)
  | [] => acc
  | n :: rest => itemBoxList env cx (itemBoxOne env cx acc n) rest

end

mutual

-- conserves: none — an importer.
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
    let st := problems.foldl (fun s p => s.lose (.css p.words)) st
    let r := computeStyle d cx.parent cx.vp attrs
    if !r.display then (st, out) else
    let st := r.losses.foldl St.lose st
    let st := { st with nodes := st.nodes + 1 }
    let s := r.style
    let inner : Ctx := { up := subject :: cx.up, parent := s, vp := cx.vp }
    let xf := aroundOrigin (ownTransform attrs) r.origin
    let clipFor (st : St) (bbox : Unit → Except Gfx.Loss (Option Box)) :
        Option (Option (Affine × Clip)) × St :=
      match r.clipPath with
      | none => (some none, st)
      | some id =>
        match clipOf env cx id bbox with
        | .ok (some c) => (some (some c), st)
        | .ok none => (none, st)
        | .error l => (some none, st.lose l)
    match name with
    | "g" | "a" | "switch" =>
      let st := if name == "a" && !st.notes.contains "a link" then
          { st with notes := st.notes.push "a link" } else st
      let (st, body) := walkList env bud inner (name == "switch") (st, #[]) kids.toList
      let (clip, st) := clipFor st fun _ => bodyBox body
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
        else some { geom := .rect (pxLen x) (pxLen y) (pxLen w) (pxLen h), rule := .nonzero }
      let viewport := #[Node.group Affine.unit (clip.toArray) Alpha.opaque #[.group m #[] Alpha.opaque body]]
      -- A nested viewport takes its own transform and clip-path (SVG 2 §8.5).
      let (clipR, st) := clipFor st fun _ => .ok (some ((pxLen x, pxLen y), (pxLen (x + w), pxLen (y + h))))
      match clipR with
      | none => (st, out)
      | some c => (st, out.append (wrap xf c r.opacity viewport))
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
              then #[{ geom := .rect 0 0 (pxLen w) (pxLen hh), rule := .nonzero }] else #[]
            let content : Ctx := { up := subjectOf tname tattrs :: target.up, parent := s, vp }
            let contentBox : Except Gfx.Loss (Option Box) := match target.item with
              | .elem _ _ _ tkids => itemBoxList env content (.ok none) tkids.toList
              | .text _ => .ok none
            let (clipR, st) := clipFor st fun _ => contentBox.map (·.map (Box.image m))
            match clipR with
            | none => (st, out)
            | some c =>
              (st, out.append (wrap place c r.opacity
                #[.group Affine.unit clip Alpha.opaque #[.use k m]]))
          else
            let (st, k) := st.request { id, style := s, vp := cx.vp, children := false }
            let (clipR, st) := clipFor st fun _ =>
              itemBoxOne env { up := target.up, parent := s, vp := cx.vp } (.ok none) target.item
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
      let (clip, st) := clipFor st fun _ => .error (unmeasuredClip "text")
      match clip with
      | none => (st, out)
      | some c => (st, out.append (wrap xf c r.opacity runs))
    | "image" =>
      let href := (Xml.Attr.get? attrs "" "href").orElse fun _ => Xml.Attr.get? attrs xlinkNs "href"
      -- An image that names nothing draws nothing, in a browser as here.
      match href.filter (!·.trimAscii.isEmpty), href.bind fun h => rasterOf h s.smooth with
      | none, _ => (st, out)
      | some _, none => (st.lose (.resource "image"), out)
      | some _, some ras =>
        let em := s.fontSize
        let x := lenAttr attrs "x" em cx.vp.w 0
        let y := lenAttr attrs "y" em cx.vp.h 0
        let w := lenAttr attrs "width" em cx.vp.w ras.pxW
        let h := lenAttr attrs "height" em cx.vp.h ras.pxH
        if w ≤ 0 || h ≤ 0 || ras.pxW == 0 || ras.pxH == 0 || !s.visible then (st, out) else
        let par := ((Xml.Attr.get? attrs "" "preserveAspectRatio").map par?).getD Par.default
        let m := viewMap { x := 0, y := 0, w := ras.pxW, h := ras.pxH } par x y w h
        let unitToPx : Affine := ⟨pxSp.toRat * ras.pxW / bboxScale, 0, 0, -pxSp.toRat * ras.pxH / bboxScale,
          0, pxSp.toRat * ras.pxH⟩
        let k := st.rasters.size
        let st := { st with rasters := st.rasters.push ras }
        let clip : Array Clip := if par.slice && par.align.isSome
          then #[{ geom := .rect (pxLen x) (pxLen y) (pxLen w) (pxLen h), rule := .nonzero }] else #[]
        let (clipR, st) := clipFor st fun _ => .ok (some ((pxLen x, pxLen y), (pxLen (x + w), pxLen (y + h))))
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
        let (clip, st) := clipFor st fun _ => .ok bbox
        match clip with
        | none => (st, out)
        | some c =>
          if p.fill.isNone && p.stroke.isNone then (st, out)
          else (st, out.append (wrap xf c r.opacity #[.draw g p.fill p.stroke]))

/-- Each node of a list onto `acc`; under a `switch`, only the first whose conditions hold (SVG 2 §5.8.2). -/
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

mutual

-- conserves: none — an index of a tree's ids, which the walk reads.
/-- Every element with an id onto `m`, with its ancestors; the first in document order wins. -/
public def idsOne (m : Std.HashMap String Entry) (up : List Css.Subject)
    (upItems : List (String × Array Xml.Attr)) : Xml.Item → Std.HashMap String Entry
  | .text _ => m
  | n@(.elem _ name attrs kids) =>
    let m := match Xml.Attr.get? attrs "" "id" with
      | some id => if m.contains id then m else m.insert id { item := n, up, upItems }
      | none => m
    idsList m (subjectOf name attrs :: up) ((name, attrs) :: upItems) kids.toList

public def idsList (m : Std.HashMap String Entry) (up : List Css.Subject)
    (upItems : List (String × Array Xml.Attr)) : List Xml.Item → Std.HashMap String Entry
  | [] => m
  | n :: rest => idsList (idsOne m up upItems n) up upItems rest

end

public def indexIds (t : Xml.Item) : Std.HashMap String Entry := idsOne {} [] [] t

mutual

-- conserves: none — a census of a tree's symbol uses.
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

/-- The requests ordered so each body uses only symbols before it (Kahn's order), old index to new,
and whether every request was placed, which a reference cycle prevents. -/
public def orderRequests (bodies : Array (Array (Node Run))) : Array (Option Nat) × Bool := Id.run do
  let n := bodies.size
  let deps := bodies.map fun b => (usesList #[] b.toList).filter (· < n)
  let mut waiting : Array Nat := deps.map (·.size)
  let mut users : Array (Array Nat) := Array.replicate n #[]
  for h : k in [0:deps.size] do
    for j in deps[k] do
      users := users.modify j (·.push k)
  let mut ready : Array Nat := (Array.range n).filter fun k => waiting[k]?.getD 0 == 0
  let mut placed : Array (Option Nat) := Array.replicate n none
  let mut next := 0
  let mut head := 0
  for _ in [0:n + 1] do
    let some k := ready[head]? | break
    head := head + 1
    placed := placed.set! k (some next)
    next := next + 1
    for u in users[k]?.getD #[] do
      let w := (waiting[u]?.getD 1) - 1
      waiting := waiting.set! u w
      if w == 0 then ready := ready.push u
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

/-- The root's intrinsic size in pixels (SVG 2 §8.2): its width and height, else its viewBox, else 300 × 150. -/
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

/-- Whether a title reads as words a person wrote: two words at least, no underscore, and no
exporter boilerplate. -/
@[expose] public def describes (t : String) : Bool :=
  let l := t.toLower
  ((t.splitOn " ").filter (!·.isEmpty)).length ≥ 2 && !t.contains '_' &&
    !(["produced by", "created with", "created by", "generated by", "made with", "gnuplot"].any
      fun (p : String) => l.startsWith p)

/-- The root's first `title` child's trimmed text, where it describes the figure. -/
public def titleOf (t : Xml.Item) : Option String :=
  match t with
  | .elem _ _ _ kids =>
    kids.findSome? fun k => match k with
      | .elem ns "title" _ _ => if ns == svgNs then
          let s := normalizeSpace (k.textOne "")
          if s.isEmpty || !describes s then none else some s
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

@[expose] public def rootParts : Xml.Item → Array Xml.Attr × Array Xml.Item
  | .elem _ _ attrs kids => (attrs, kids)
  | .text _ => (#[], #[])

/-- The root viewport's size in pixels, its font size read through the
cascade. -/
@[expose] public def rootPx (rules : Css.RuleIndex) (attrs : Array Xml.Attr) : Rat × Rat :=
  let (d, _) := declsOf rules (subjectOf "svg" attrs) [] attrs
  rootSize attrs (computeStyle d Style.initial { w := 300, h := 150 } attrs).style.fontSize

/-- The figure box an SVG tree reserves: its root viewport from the origin, in `Length`. -/
@[expose] public def rootBox (t : Xml.Item) : Box :=
  let px := rootPx (Css.RuleIndex.ofRules (sheetsOf t).1) (rootParts t).1
  ((0, 0), (pxLen px.1, pxLen px.2))

mutual

-- conserves: none — a measure of the nodes a list paints expanded.
/-- The nodes one node paints expanded onto `acc`, each sum capped at `cap`. -/
@[expose] public def expandedOne (sizes : Array Nat) (cap : Nat) (acc : Nat) : Node Run → Nat
  | .use k _ => min cap (acc + 1 + (sizes[k]?.getD 0))
  | .group _ _ _ kids => expandedList sizes cap (min cap (acc + 1)) kids.toList
  | .draw _ _ _ | .stamp _ _ _ _ | .image _ _ | .label _ | .words _ => min cap (acc + 1)

@[expose] public def expandedList (sizes : Array Nat) (cap : Nat) (acc : Nat) : List (Node Run) → Nat
  | [] => acc
  | n :: rest => expandedList sizes cap (expandedOne sizes cap acc n) rest

end

mutual

-- conserves: none — a rewriting that drops every use.
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

/-- The expanded size of a body, its symbols sized in order in one pass. -/
@[expose] public def expandedSize (symbols : Array (Array (Node Run))) (cap : Nat) (body : Array (Node Run)) : Nat :=
  let sizes := symbols.foldl (fun acc b => acc.push (expandedList acc cap 0 b.toList)) #[]
  expandedList sizes cap 0 body.toList

/-- A drawing's uses held to the expansion budget: past it, every use and symbol dropped, and
whether it was past. -/
@[expose] public def boundUses (bud : Budget) (symbols : Array (Array (Node Run)))
    (body : Array (Node Run)) : Array (Array (Node Run)) × Array (Node Run) × Bool :=
  if expandedSize symbols (bud.expanded + 1) body > bud.expanded then (#[], unuseList #[] body.toList, true)
  else (symbols, body, false)

/-- An accepted SVG tree as a figure whose box is its root viewport, read through its sheets. -/
public def importTree (t : Xml.Item) (lang : String := "en") (bud : Budget := Budget.standard)
    (sheets : Array Css.Rule × Array Css.Unread := sheetsOf t) : Import :=
  let ids := indexIds t
  let (sheet, dropped) := sheets
  let rules := Css.RuleIndex.ofRules sheet
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
  let st0 : St := { losses := #[], notes := #[], rasters := #[], requests := #[], requestIds := {}
                    nodes := 0, animated := false, text := false }
  let st0 := (dropped ++ problems).foldl (fun s p => s.lose (.css p.words)) st0
  let st0 := r.losses.foldl St.lose st0
  let cx : Ctx := { up := [rootSubject], parent := r.style, vp }
  let (st, body) := walkList env bud cx false (st0, #[]) rootKids.toList
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
            -- The instantiated element stands in the use's shadow tree (SVG 2 §5.6.3).
            let subject := subjectOf name tattrs
            let (d, problems) := declsOf env.rules subject e.up tattrs
            let st := problems.foldl (fun s p => s.lose (.css p.words)) st
            let r := computeStyle d req.style req.vp tattrs
            if name != "symbol" && !r.display then (st, #[]) else
            let st := r.losses.foldl St.lose st
            let st := if r.clipPath.isSome then st.lose (.property s!"clip-path on a {name} a use names")
              else st
            let (st, body) := walkList env bud { up := subject :: e.up, parent := r.style, vp := req.vp }
              false (st, #[]) kids.toList
            (st, wrap Affine.unit none r.opacity body)
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
  let bounded := boundUses bud symbols body
  let st := if bounded.2.2 then st.lose (.budget "expanded uses") else st
  let m := match vb with
    | some v => viewMap v par 0 0 w h
    | none => Affine.unit
  let wsp := pxLen w
  let hsp := pxLen h
  let flip : Affine := ⟨1, 0, 0, -1, 0, hsp.toRat⟩
  let rootXf := flip.compose m
  let clip := r.clipPath.isSome
  let st := if clip then st.lose (.property "clip-path on the root") else st
  let nodes := #[Node.group rootXf #[] (mulAlpha r.opacity 1000) bounded.2.1]
  { fig := { box := ((0, 0), (wsp, hsp)), clipToBox := true, nodes, outlines := #[]
             symbols := bounded.1, rasters := st.rasters, title := titleOf t, losses := st.losses }
    notes := st.notes, animated := moves t, text := st.text }

public theorem importTree_shape (t : Xml.Item) (lang : String) (bud : Budget) :
    ∃ (symbols : Array (Array (Node Run))) (body : Array (Node Run)) (xf : Affine) (a : Alpha),
      (importTree t lang bud).fig.symbols = (boundUses bud symbols body).1 ∧
        (importTree t lang bud).fig.nodes = #[Node.group xf #[] a (boundUses bud symbols body).2.1] :=
  ⟨_, _, _, _, rfl, rfl⟩

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

/-- SVG bytes as a figure: judged, then imported. -/
public def importBytes (bytes : ByteArray) (lang : String := "en") : Verdict :=
  match judged bytes with
  | .error r => .refused r
  | .ok (t, sheets) =>
    let i := importTree t lang (sheets := sheets)
    if i.fig.losses.isEmpty then .exact i else .lossy i

end LeanTex.Core.Svg
