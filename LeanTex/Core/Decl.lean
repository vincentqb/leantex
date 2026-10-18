module

public import LeanTex.Core.Diag
public import LeanTex.Core.Dim
public import LeanTex.Core.Oklab
import LeanTex.Core.Hex
import LeanTex.Core.KeyVal

namespace LeanTex.Core.Decl

/-- The native declarations that take a `{...}` block and are read in the preamble. -/
@[expose] public def blockDeclarations : List String :=
  ["page", "pdfmeta", "assert", "fonts", "palette", "tokens", "style", "output",
   "theme", "chrome", "pictures", "figures", "allow"]

/-- The native preamble declarations that take one inline-content group. -/
@[expose] public def runningDeclarations : List String := ["runninghead", "runningfoot"]

open LeanTex.Core LeanTex.Core.Dim

/-- A parsed declaration value; absolute dimensions resolve immediately,
font-relative ones and glue keep their symbolic components. -/
public inductive Value where
  | str (s : String)
  | dim (sp : Sp)
  | int (n : Int)
  | ident (s : String)
  | block (src : String)
  | color (r g b : UInt8)
  /-- A colour declared in CMYK, components in thousandths. -/
  | cmyk (c m y k : Nat)
  /-- A glue expression, possibly font-relative or scaled from a token. -/
  | glue (g : SymGlue)
  deriving Repr, BEq

public def Value.kindName : Value → String
  | .str _ => "string"
  | .dim _ => "dimension"
  | .int _ => "number"
  | .ident _ => "name"
  | .block _ => "block"
  | .color _ _ _ => "color"
  | .cmyk _ _ _ _ => "color"
  | .glue _ => "length"

public structure Entry where
  key : String
  value : Value
  deriving Repr, BEq

/-- One non-negative decimal component, kept as the exact
rational the source wrote. -/
public structure ColorComponent where
  num : Nat
  scale : Nat
  deriving Repr

public instance : BEq ColorComponent where
  beq a b := a.num * b.scale == b.num * a.scale

private def decimalFraction (num scale : Nat) : String :=
  if num == 0 then "0"
  else if num == scale then "1"
  else
    let places := (toString scale).length - 1
    let raw := toString num
    let digits := "".pushn '0' (places - raw.length) ++ raw
    let digits := (digits.dropEndWhile (· == '0')).toString
    "0." ++ digits

/-- A unit component as a canonical PDF decimal. -/
public def ColorComponent.pdfUnit (c : ColorComponent) : String :=
  decimalFraction c.num c.scale

/-- The value xcolor stores for a `\definecolor` unit
component: five fractional digits, truncated. -/
public def ColorComponent.xcolorDefined (c : ColorComponent) : ColorComponent :=
  { num := c.num * 100000 / c.scale, scale := 100000 }

/-- TeX's printer of scaled points: the whole part and the
fraction's decimal digits it prints. -/
public def texScaledParts (sp : Nat) : Nat × List Nat := Id.run do
  let mut digits : Array Nat := #[]
  let mut rem := 10 * (sp % 65536) + 5
  let mut delta := 10
  for _ in [0:6] do
    if delta > 65536 then rem := rem - 17232
    digits := digits.push (rem / 65536)
    rem := 10 * (rem % 65536)
    delta := delta * 10
    if rem ≤ delta then break
  return (sp / 65536, digits.toList)

/-- The printed scaled points as `\strip@pt` leaves them. -/
private def texScaledDecimal (sp : Nat) : String :=
  let (whole, digits) := texScaledParts sp
  if digits == [0] then toString whole
  else toString whole ++ "." ++ String.join (digits.map toString)

/-- The printed scaled points as a component. -/
private def texScaledComponent (sp : Nat) : ColorComponent :=
  let (whole, digits) := texScaledParts sp
  if digits == [0] then { num := whole, scale := 1 }
  else { num := digits.foldl (fun n d => n * 10 + d) whole, scale := 10 ^ digits.length }

/-- TeX's rounding of a decimal fraction to scaled points. -/
public def roundDecimals (digits : List Nat) : Nat :=
  (digits.foldr (fun d a => (a + d * 131072) / 10) 0 + 1) / 2

/-- xcolor's `\rdivide` of two scaled-point values. -/
private def xcolorDivide (a b : Nat) : Nat := Id.run do
  let q := a / b
  let mut rem := a - q * b
  let mut digits : Array Nat := #[]
  for _ in [0:5] do
    rem := rem * 10
    digits := digits.push (rem / b)
    rem := rem - (rem / b) * b
  let sixth := rem * 10 / b
  return q * 65536 + roundDecimals digits.toList + (if sixth > 4 then 1 else 0)

/-- The graphics driver's conversion of an RGB-range component used directly. -/
public def ColorComponent.pdfRgb (c : ColorComponent) : String :=
  let sourceSp := (c.num * 65536 + c.scale / 2) / c.scale
  texScaledDecimal (sourceSp / 255)

/-- The scaled points xcolor's own conversion of an
RGB-range component arrives at. -/
private def ColorComponent.xcolorRgbSp (c : ColorComponent) : Nat :=
  xcolorDivide ((c.num * 65536 + c.scale / 2) / c.scale) (255 * 65536)

/-- xcolor's own conversion of an RGB-range component, as TeX prints it. -/
public def ColorComponent.xcolorRgb (c : ColorComponent) : String :=
  texScaledDecimal c.xcolorRgbSp

/-- The unit value xcolor stores for an RGB-range component it converts. -/
public def ColorComponent.xcolorRgbUnit (c : ColorComponent) : ColorComponent :=
  texScaledComponent c.xcolorRgbSp

/-- xcolor's HTML projection of a unit component, through
TeX's 16-bit fixed point. -/
public def ColorComponent.unitByte (c : ColorComponent) : UInt8 :=
  let sp := (c.num * 65536 + c.scale / 2) / c.scale
  UInt8.ofNat ((sp * 255 + 32768) / 65536)

/-- An RGB-range component projected to the nearest byte. -/
public def ColorComponent.rgbByte (c : ColorComponent) : UInt8 :=
  UInt8.ofNat ((c.num + c.scale / 2) / c.scale)

public def ColorComponent.milli (c : ColorComponent) : Nat :=
  (c.num * 1000 + c.scale / 2) / c.scale

/-- The source model of one xcolor specification, each model one the engine
projects without guessing. -/
public inductive ColorSpec where
  | named (expr : String)
  | html (r g b : UInt8)
  | rgbByte (r g b : ColorComponent)
  | rgbUnit (r g b : ColorComponent)
  | gray (v : ColorComponent)
  | cmyk (c m y k : ColorComponent)
  /-- CSS Color 4's `oklab(L a b)`: lightness as a fraction
  of 1, `a` and `b` in Oklab units. -/
  | oklab (L a b : Int × Nat)
  /-- CSS Color 4's `oklch(L C H)`: lightness as a fraction of 1, chroma in
  Oklab units, hue in degrees. -/
  | oklch (L C H : Int × Nat)
  /-- `spot("name", cmyk(c, m, y, k))`: an ink by its colorant name and its CMYK alternate. -/
  | spot (name : String) (c m y k : ColorComponent)
  deriving Repr, BEq

/-- A specification as xcolor's definitions store it. -/
public def ColorSpec.xcolorDefined : ColorSpec → ColorSpec
  | .named expr => .named expr
  | .html r g b => .html r g b
  | .rgbByte r g b => .rgbUnit r.xcolorRgbUnit g.xcolorRgbUnit b.xcolorRgbUnit
  | .rgbUnit r g b => .rgbUnit r.xcolorDefined g.xcolorDefined b.xcolorDefined
  | .gray v => .gray v.xcolorDefined
  | .cmyk c m y k =>
    .cmyk c.xcolorDefined m.xcolorDefined y.xcolorDefined k.xcolorDefined
  | .oklab L a b => .oklab L a b
  | .oklch L C H => .oklch L C H
  | .spot n c m y k => .spot n c.xcolorDefined m.xcolorDefined y.xcolorDefined k.xcolorDefined

/-- `1 - c`, at `c`'s scale. -/
private def ColorComponent.complement (c : ColorComponent) : ColorComponent :=
  { num := c.scale - min c.num c.scale, scale := c.scale }

/-- `a - b`, floored at zero, at the product of their scales. -/
private def ColorComponent.sub (a b : ColorComponent) : ColorComponent :=
  { num := a.num * b.scale - b.num * a.scale, scale := a.scale * b.scale }

private def ColorComponent.min (a b : ColorComponent) : ColorComponent :=
  if a.num * b.scale ≤ b.num * a.scale then a else b

/-- xcolor's RGB to CMYK (manual §6.3): cmy as the complements, black generation and undercolour
removal at their defaults, `k` the least of them taken from each. -/
private def rgbToCmyk (r g b : ColorComponent) :
    ColorComponent × ColorComponent × ColorComponent × ColorComponent :=
  let c := r.complement
  let m := g.complement
  let y := b.complement
  let k := (c.min m).min y
  (c.sub k, m.sub k, y.sub k, k)

/-- The CMYK a definition converts into as xcolor's `cmyk:<model>` does, the model's own digits
first passed through xcolor's storage; `none` for a model with no such conversion here. -/
public def ColorSpec.cmykOf? : ColorSpec →
    Option (ColorComponent × ColorComponent × ColorComponent × ColorComponent)
  | .cmyk c m y k => some (c, m, y, k)
  | .gray v => some (⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, v.complement)
  | .rgbUnit r g b => some (rgbToCmyk r g b)
  | .rgbByte r g b => some (rgbToCmyk r.xcolorRgbUnit g.xcolorRgbUnit b.xcolorRgbUnit)
  | .html r g b =>
    let unit (v : UInt8) : ColorComponent := ({ num := v.toNat, scale := 1 } : ColorComponent).xcolorRgbUnit
    some (rgbToCmyk (unit r) (unit g) (unit b))
  | .named _ | .oklab .. | .oklch .. | .spot .. => none

/-- A signed decimal (mantissa, scale) at `Oklab.labOf`'s 10¹⁸ scale. -/
private def okScaled (d : Int × Nat) : Int := d.1 * 10 ^ 18 / (d.2 : Int)

/-- The Oklab value an `oklab()` or `oklch()` source states. -/
public def ColorSpec.okLab? : ColorSpec → Option Oklab.Lab
  | .oklab L a b => some { L := okScaled L, a := okScaled a, b := okScaled b }
  | .oklch L C H => some (Oklab.ofLch (okScaled L) (okScaled C) (H.1 * 1000 / (H.2 : Int)))
  | .named _ | .html .. | .rgbByte .. | .rgbUnit .. | .gray _ | .cmyk .. | .spot .. => none

/-- The marker of a modelled value that passed through
xcolor's `\definecolor` storage. -/
public def xcolorDefinitionPrefix : String := "@xcolor-definition:"

public inductive ColorSpecError where
  | unsupported (model : String)
  | malformed (model detail : String)
  deriving Repr, BEq

/-- The model names `parseColorSpec` accepts, with xcolor's
case-sensitive spellings. -/
public def colorModelNames : List String := ["HTML", "RGB", "rgb", "gray", "cmyk"]

public def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.'

/-- A declaration's text as its atoms: a quoted string whole, every other character alone. -/
private def quoteAtoms : List Char → Array (List Char) → Array (List Char)
  | [], acc => acc
  | '"' :: rest, acc =>
    let body := rest.takeWhile (· != '"')
    let closed := body.length < rest.length
    quoteAtoms (rest.drop (body.length + 1))
      (acc.push ('"' :: body ++ if closed then ['"'] else []))
  | c :: rest, acc => quoteAtoms rest (acc.push [c])
termination_by l => l.length
decreasing_by all_goals simp only [List.length_cons, List.length_drop]; omega

/-- Text trimmed as `String.trimAscii` trims it. -/
public def trimChars (cs : List Char) : List Char :=
  ((cs.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

private def entryOpens (a : List Char) : Bool := a == ['{'] || a == ['['] || a == ['(']

private def entryCloses (a : List Char) : Bool := a == ['}'] || a == [']'] || a == [')']

/-- Splits on commas outside braces, brackets, parentheses and quotes. -/
public def splitEntries (s : String) : List String :=
  ((KeyVal.splitTopAt entryOpens entryCloses (· == [',']) (quoteAtoms s.toList #[]).toList).toList.filterMap
    fun e =>
      let t := trimChars (e.toList.flatMap id)
      if t.isEmpty then none else some (String.ofList t))

/-- An entry's key and value: the text before its first `=` and the text after it, each trimmed. -/
public def entryOf (e : String) : String × String :=
  let cut := KeyVal.cutAt '=' e.toList
  (String.ofList (trimChars cut.1), String.ofList (trimChars (cut.2.getD [])))

/-- Whether a character leaves an entry's split and its cut alike: no space, `=`, comma, quote or
bracket. -/
public def plainChar (c : Char) : Bool :=
  !(c.isWhitespace || c == '=' || c == ',' || c == '"' || c == '{' || c == '}' || c == '[' ||
    c == ']' || c == '(' || c == ')')

/-- Whether a key reads back from an entry beside any others. -/
public def plainKey (k : String) : Bool := !k.toList.isEmpty && k.toList.all plainChar

private def closedAtom (a : List Char) : Bool :=
  a.head? != some '"' || (2 ≤ a.length && a.getLast? == some '"')

/-- Whether a value reads back whole from an entry beside any others: written, trimmed, every quote
closed, and no comma or open bracket left outside them. -/
public def wholeValue (v : String) : Bool :=
  let atoms := (quoteAtoms v.toList #[]).toList
  !v.toList.isEmpty && !(v.toList.head?.any Char.isWhitespace) &&
    !(v.toList.getLast?.any Char.isWhitespace) && atoms.all closedAtom &&
    atoms.foldl (KeyVal.cutStep entryOpens entryCloses (· == [','])) (some 0) == some 0

/-- Decimal literal as mantissa and scale: "0.5" ↦ (5, 10). -/
public def parseDecimal (s : String) : Option (Int × Nat) := Id.run do
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, cs)
  if cs.isEmpty then
    return none
  let mut mantissa : Nat := 0
  let mut scale : Nat := 1
  let mut seenDot := false
  let mut digits := 0
  for c in cs do
    if c == '.' then
      if seenDot then return none
      seenDot := true
    else if c.isDigit then
      mantissa := mantissa * 10 + (c.toNat - '0'.toNat)
      digits := digits + 1
      if seenDot then scale := scale * 10
    else
      return none
  if digits == 0 then
    return none
  return some (if neg then -(mantissa : Int) else mantissa, scale)

/-- Color components separated by commas or runs of ASCII whitespace, as
xcolor's `XC@clean` reads them. -/
private def colorParts (s : String) : Option (List String) :=
  let commaParts := s.splitOn ","
  if commaParts.any (fun p => p.trimAscii.isEmpty) then none
  else
    some (commaParts.flatMap fun part =>
      let normalized := String.ofList (part.toList.map fun c =>
        if c == '\t' || c == '\n' || c == '\r' then ' ' else c)
      (normalized.splitOn " ").filterMap fun p =>
        let p := p.trimAscii.toString
        if p.isEmpty then none else some p)

private def malformedColor (model detail : String) : Except ColorSpecError α :=
  .error (.malformed model detail)

private def colorComponents (model value : String) (count : Nat) :
    Except ColorSpecError (List String) := do
  let some parts := colorParts value
    | return ← malformedColor model s!"expected {count} components"
  if parts.length == count then return parts
  else malformedColor model s!"expected {count} components, got {parts.length}"

private def unitComponent (model src : String) : Except ColorSpecError ColorComponent := do
  let some (m, scale) := parseDecimal src
    | return ← malformedColor model s!"'{src}' is not a decimal"
  if m < 0 || (scale : Int) < m then
    malformedColor model s!"'{src}' is outside 0–1"
  else
    return { num := m.toNat, scale := scale }

private def rgbComponent (model src : String) : Except ColorSpecError ColorComponent := do
  let some (m, scale) := parseDecimal src
    | return ← malformedColor model s!"'{src}' is not a decimal"
  if m < 0 || (255 * scale : Int) < m then
    malformedColor model s!"'{src}' is outside 0–255"
  else
    return { num := m.toNat, scale := scale }

private def htmlBytes (value : String) : Except ColorSpecError (UInt8 × UInt8 × UInt8) := do
  let digits ← match value.toList.mapM Hex.digit? with
    | some ds => pure ds
    | none => malformedColor "HTML" "expected six hexadecimal digits"
  match digits with
  | [r1, r2, g1, g2, b1, b2] =>
    return (UInt8.ofNat (r1 * 16 + r2), UInt8.ofNat (g1 * 16 + g2),
      UInt8.ofNat (b1 * 16 + b2))
  | _ => malformedColor "HTML" s!"expected six hexadecimal digits, got {digits.length}"

private def wrappedColor (s : String) : Option (String × String) :=
  match s.splitOn "(" with
  | [model, rest] =>
    let model := model.trimAscii.toString
    if !model.isEmpty && model.toList.all Char.isAlpha && rest.endsWith ")" then
      some (model, (rest.dropEnd 1).toString)
    else none
  | _ => none

private def parseModeledColor (model value : String) : Except ColorSpecError ColorSpec := do
  match model with
  | "HTML" =>
    let (r, g, b) ← htmlBytes value.trimAscii.toString
    return .html r g b
  | "RGB" =>
    let parts ← colorComponents model value 3
    let vals ← parts.mapM (rgbComponent model)
    match vals with
    | [r, g, b] => return .rgbByte r g b
    | _ => malformedColor model "expected three components"
  | "rgb" =>
    let parts ← colorComponents model value 3
    let vals ← parts.mapM (unitComponent model)
    match vals with
    | [r, g, b] => return .rgbUnit r g b
    | _ => malformedColor model "expected three components"
  | "gray" =>
    let parts ← colorComponents model value 1
    match parts with
    | [v] => return .gray (← unitComponent model v)
    | _ => malformedColor model "expected one component"
  | "cmyk" =>
    let parts ← colorComponents model value 4
    let vals ← parts.mapM (unitComponent model)
    match vals with
    | [c, m, y, k] => return .cmyk c m y k
    | _ => malformedColor model "expected four components"
  | _ => .error (.unsupported model)

/-- One `oklab()`/`oklch()` component: a decimal, or a percentage of `full`. -/
private def okComponent (model src : String) (full : Int × Nat) (signed : Bool) :
    Except ColorSpecError (Int × Nat) := do
  let (pct, body) := if src.endsWith "%" then (true, (src.dropEnd 1).toString) else (false, src)
  let some (m, scale) := parseDecimal body
    | return ← malformedColor model s!"'{src}' is not a number"
  if !signed && m < 0 then return ← malformedColor model s!"'{src}' is negative"
  if pct then return (m * full.1, scale * 100 * full.2) else return (m, scale)

/-- `oklab(L a b)` and `oklch(L C H)`, space-separated; an alpha is refused. -/
private def parseOkColor (model value : String) : Except ColorSpecError ColorSpec := do
  if value.contains '/' then
    return ← malformedColor model "an alpha has no meaning for a page colour"
  let parts := (value.splitOn " ").filterMap fun p =>
    let p := p.trimAscii.toString
    if p.isEmpty then none else some p
  let [l, x, y] := parts
    | return ← malformedColor model s!"expected 3 components, got {parts.length}"
  let L ← okComponent model l (1, 1) false
  if L.1 > (L.2 : Int) then return ← malformedColor model s!"'{l}' is above 1"
  if model == "oklab" then
    return .oklab L (← okComponent model x (4, 10) true) (← okComponent model y (4, 10) true)
  else
    let h := if y.endsWith "deg" then (y.dropEnd 3).toString else y
    let some H := parseDecimal h | return ← malformedColor model s!"'{y}' is not a hue in degrees"
    return .oklch L (← okComponent model x (4, 10) false) H

/-- Whether a source spells the `spot(...)` form. -/
private def spotSource (value : String) : Bool := value.startsWith "spot(" && value.endsWith ")"

/-- `spot("name", cmyk(c, m, y, k))`: a quoted colorant name, then its alternate in CMYK. -/
private def parseSpot (value : String) : Except ColorSpecError ColorSpec := do
  let inner := ((value.drop "spot(".length).dropEnd 1).toString
  let [nameSrc, altSrc] := splitEntries inner
    | return ← malformedColor "spot" "expected a quoted colorant name and a cmyk(...) alternate"
  let some name := (if nameSrc.startsWith "\"" && nameSrc.endsWith "\"" && nameSrc.length ≥ 2 then
      some (String.ofList (nameSrc.toList.drop 1).dropLast).trimAscii.toString else none)
    | return ← malformedColor "spot" s!"the colorant name {nameSrc} is not a quoted string"
  if name.isEmpty || name.contains '"' then
    return ← malformedColor "spot" "the colorant name is empty or holds a quote"
  match wrappedColor altSrc with
  | some ("cmyk", v) =>
    match ← parseModeledColor "cmyk" v with
    | .cmyk c m y k => return .spot name c m y k
    | _ => malformedColor "spot" "the alternate is not a cmyk(...) colour"
  | _ => malformedColor "spot" s!"the alternate {altSrc} is not a cmyk(...) colour"

/-- A no-model source: `#RGB`/`#RRGGBB`, `oklab()`, `oklch()`, `spot()`, the modelled
`MODEL(...)` carrier, or a named xcolor expression. -/
private def parsePlainColor (value : String) : Except ColorSpecError ColorSpec :=
  if spotSource value then parseSpot value
  else if value.startsWith "#" then
    let hex := (value.drop 1).toString
    match hex.toList with
    | [r, g, b] =>
      match [r, g, b].mapM Hex.digit? with
      | some [rv, gv, bv] =>
        .ok (.html (UInt8.ofNat (rv * 17)) (UInt8.ofNat (gv * 17))
          (UInt8.ofNat (bv * 17)))
      | _ => .error (.malformed "HTML" "expected three or six hexadecimal digits")
    | _ =>
      match htmlBytes hex with
      | .ok (r, g, b) => .ok (.html r g b)
      | .error e => .error e
  else
    match wrappedColor value with
    | some ("oklab", v) => parseOkColor "oklab" v
    | some ("oklch", v) => parseOkColor "oklch" v
    | some (m, v) => parseModeledColor m v
    | none => .ok (.named value)

/-- Parses one colour source; an explicit model follows
xcolor's case-sensitive model grammar. -/
public def parseColorSpec (model : Option String) (raw : String) :
    Except ColorSpecError ColorSpec :=
  let value := raw.trimAscii.toString
  match model with
  | some model => parseModeledColor model.trimAscii.toString value
  | none =>
    if value.startsWith xcolorDefinitionPrefix then
      let source := (value.drop xcolorDefinitionPrefix.length).toString.trimAscii.toString
      if spotSource source then (parseSpot source).map ColorSpec.xcolorDefined
      else match wrappedColor source with
      | some (m, v) => (parseModeledColor m v).map ColorSpec.xcolorDefined
      | none => parsePlainColor source
    else parsePlainColor value

/-- Scaled points per unit, as an exact fraction. -/
private def unitScaleBase : String → Option (Int × Nat)
  | "sp" => some (1, 1)
  | "pt" => some (spPerPt, 1)
  | "bp" => some (spPerPt, 1)
  | "in" => some (72 * spPerPt, 1)
  | "cm" => some (7200 * spPerPt, 254)
  | "mm" => some (7200 * spPerPt, 2540)
  | "pc" => some (12 * spPerPt, 1)
  -- The CSS pixel: 1px = 1/96 in (CSS Values and Units 4 §6.2).
  | "px" => some (72 * spPerPt, 96)
  -- The didot point: 1157 dd = 1238 TeX pt (TeXbook ch. 10).
  | "dd" => some (8913600 * spPerPt, 8361639)
  | "cc" => some (12 * 8913600 * spPerPt, 8361639)
  | _ => none

/-- Scaled points per unit, a `true` unit its plain counterpart exactly. -/
private def unitScale : String → Option (Int × Nat)
  | "truesp" => unitScaleBase "sp"
  | "truept" => unitScaleBase "pt"
  | "truebp" => unitScaleBase "bp"
  | "truein" => unitScaleBase "in"
  | "truecm" => unitScaleBase "cm"
  | "truemm" => unitScaleBase "mm"
  | "truepc" => unitScaleBase "pc"
  | "truepx" => unitScaleBase "px"
  | "truedd" => unitScaleBase "dd"
  | "truecc" => unitScaleBase "cc"
  | u => unitScaleBase u

private theorem unitScale_consistent :
    unitScale "bp" = unitScale "pt" ∧
    unitScale "pt" = (unitScale "sp").map (fun u => (spPerPt * u.1, u.2)) ∧
    unitScale "in" = (unitScale "pt").map (fun u => (72 * u.1, u.2)) ∧
    unitScale "pc" = (unitScale "pt").map (fun u => (12 * u.1, u.2)) ∧
    unitScale "cm" = (unitScale "in").map (fun u => (100 * u.1, 254 * u.2)) ∧
    unitScale "mm" = (unitScale "cm").map (fun u => (u.1, 10 * u.2)) ∧
    unitScale "px" = (unitScale "in").map (fun u => (u.1, 96 * u.2)) ∧
    unitScale "dd" = (unitScale "in").map (fun u => (123800 * u.1, 8361639 * u.2)) ∧
    unitScale "cc" = (unitScale "dd").map (fun u => (12 * u.1, u.2)) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [unitScale, unitScaleBase, spPerPt]

private theorem unitScale_true :
    unitScale "truesp" = unitScale "sp" ∧ unitScale "truept" = unitScale "pt" ∧
    unitScale "truebp" = unitScale "bp" ∧ unitScale "truein" = unitScale "in" ∧
    unitScale "truecm" = unitScale "cm" ∧ unitScale "truemm" = unitScale "mm" ∧
    unitScale "truepc" = unitScale "pc" ∧ unitScale "truepx" = unitScale "px" ∧
    unitScale "truedd" = unitScale "dd" ∧ unitScale "truecc" = unitScale "cc" := by
  decide

/-- One term's length from its mantissa, scale and unit name. -/
private def lengthOfUnit (mantissa : Int) (scale : Nat) (unit : String) :
    Option Length :=
  if unit == "em" then
    some { em := mantissa * 1000 / scale }
  else if unit == "ex" then
    some { ex := mantissa * 1000 / scale }
  else
    (unitScale unit).map fun (num, den) =>
      Length.ofSp (mantissa * num / (scale * den : Nat))

/-- A single length term: a number with an absolute or font-relative unit. -/
public def parseLength (s : String) : Option Length :=
  let s := s.trimAscii.toString
  let digits := s.toList.takeWhile fun c => c.isDigit || c == '.' || c == '-' || c == '+'
  let unit := (String.ofList (s.toList.drop digits.length)).trimAscii.toString
  match parseDecimal (String.ofList digits) with
  | none => none
  | some (mantissa, scale) => lengthOfUnit mantissa scale unit

/-- A stretch in one of TeX's infinite units, and its order. -/
public def filFactor? (s : String) : Option ((Int × Nat) × Nat) :=
  let t := s.trimAscii.toString
  let digits := t.toList.takeWhile fun c => c.isDigit || c == '.' || c == '+'
  let order := match String.ofList (t.toList.drop digits.length) with
    | "fil" => some 1
    | "fill" => some 2
    | "filll" => some 3
    | _ => none
  order.bind fun o => (parseDecimal (String.ofList digits)).map (·, o)

/-- `<len> [plus <len>] [minus <len>]`, TeX's glue spelling. -/
public def parseGlue (s : String) : Option SymGlue := do
  let words := (s.trimAscii.toString.splitOn " ").filterMap fun w =>
    let t := w.trimAscii.toString
    if t.isEmpty then none else some t
  match words with
  | [] => none
  | base :: rest =>
    let g : SymGlue := { width := ← parseLength base }
    let rec go (g : SymGlue) : List String → Option SymGlue
      | [] => some g
      | "plus" :: v :: tl => do
        let l ← parseLength v
        go { g with stretch := l } tl
      | "minus" :: v :: tl => do
        let l ← parseLength v
        go { g with shrink := l } tl
      | _ => none
    go g rest

/-- A scale factor `0.6 * name`, resolved against already-declared tokens. -/
private def parseScaled (tokens : Array (String × SymGlue)) (s : String) : Option Value :=
  match s.splitOn "*" with
  | [factor, name] => do
    let (mantissa, scale) ← parseDecimal (factor.trimAscii.toString)
    let key := name.trimAscii.toString
    let (_, g) ← tokens.find? (·.1 == key)
    some (.glue (g.scale mantissa scale))
  | _ => none

/-- A parsed length expression whose references are still source names. -/
public abbrev LenExpr := Affine String

namespace LenExpr

/-- Whether an expression reads a token name. -/
public def reads : LenExpr → String → Bool
  | .lit _, _ => false
  | .ref m, n => m == n
  | .scale _ _ e, n => reads e n
  | .add a b, n | .sub a b, n => reads a n || reads b n

/-- Evaluates against a lookup of declared tokens; an
unknown name is an error carrying that name. -/
public def eval (look : String → Option SymGlue) : LenExpr → Except String SymGlue
  | .lit g => .ok g
  | .ref n =>
    match look n with
    | some g => .ok g
    | none => .error n
  | .scale num den e =>
    match eval look e with
    | .ok g => .ok (g.scale num den)
    | .error m => .error m
  | .add a b =>
    match eval look a, eval look b with
    | .ok ga, .ok gb => .ok (ga.add gb)
    | .error m, _ => .error m
    | _, .error m => .error m
  | .sub a b =>
    match eval look a, eval look b with
    | .ok ga, .ok gb => .ok (ga.sub gb)
    | .error m, _ => .error m
    | _, .error m => .error m

public theorem eval_names_agree (l₁ l₂ : String → Option SymGlue) (e : LenExpr)
    (h : ∀ n, l₁ n = l₂ n) : eval l₁ e = eval l₂ e := by
  induction e with
  | lit g => rfl
  | ref n => simp [eval, h n]
  | scale num den e ih => simp only [eval, ih]
  | add a b iha ihb => simp only [eval, iha, ihb]
  | sub a b iha ihb => simp only [eval, iha, ihb]

/-- The expression evaluated in ℤ over one fixed-point component. -/
public def evalInt (look : String → Option Int) : LenExpr → (Length → Int) → Except String Int
  | .lit g, part => .ok (part g.width)
  | .ref n, _ =>
    match look n with
    | some v => .ok v
    | none => .error n
  | .scale num den e, part =>
    match evalInt look e part with
    | .ok v => .ok ((v * num).tdiv den)
    | .error m => .error m
  | .add a b, part =>
    match evalInt look a part, evalInt look b part with
    | .ok va, .ok vb => .ok (va + vb)
    | .error m, _ => .error m
    | _, .error m => .error m
  | .sub a b, part =>
    match evalInt look a part, evalInt look b part with
    | .ok va, .ok vb => .ok (va - vb)
    | .error m, _ => .error m
    | _, .error m => .error m

public theorem eval_exact_sp (look : String → Option SymGlue) (e : LenExpr) :
    (eval look e).map (fun g => g.width.sp)
      = evalInt (fun n => (look n).map (fun g => g.width.sp)) e (fun l => l.sp) := by
  induction e with
  | lit l => rfl
  | ref n => simp only [eval, evalInt]; cases look n <;> rfl
  | scale num den e ih =>
    simp only [eval, evalInt]
    cases h : eval look e with
    | error m => rw [h] at ih; simp [← ih, Except.map]
    | ok g => rw [h] at ih; simp [← ih, Except.map, SymGlue.scale, Length.scale]
  | add a b iha ihb =>
    simp only [eval, evalInt]
    cases ha : eval look a with
    | error m => rw [ha] at iha; simp [← iha, Except.map]
    | ok ga =>
      rw [ha] at iha
      cases hb : eval look b with
      | error m => rw [hb] at ihb; simp [← iha, ← ihb, Except.map]
      | ok gb =>
        rw [hb] at ihb
        simp [← iha, ← ihb, Except.map, SymGlue.add, Length.add]
  | sub a b iha ihb =>
    simp only [eval, evalInt]
    cases ha : eval look a with
    | error m => rw [ha] at iha; simp [← iha, Except.map]
    | ok ga =>
      rw [ha] at iha
      cases hb : eval look b with
      | error m => rw [hb] at ihb; simp [← iha, ← ihb, Except.map]
      | ok gb =>
        rw [hb] at ihb
        simp [← iha, ← ihb, Except.map, SymGlue.sub, Length.sub]

public theorem eval_absent_named (look : String → Option SymGlue) (n : String)
    (h : look n = none) : eval look (.ref n) = .error n := by
  simp [eval, h]

end LenExpr

/-- The expression tokenizer's alphabet. -/
private inductive ETok where
  | num (mantissa : Int) (scale : Nat)
  | ident (s : String)
  | plus | minus | times | divide | lparen | rparen | dimexpr | relax
  deriving Repr, BEq

/-- Scans a length expression into tokens; `none` when a
character fits no token. -/
private def exprToks (s : String) : Option (Array ETok) := Id.run do
  let cs : Array Char := s.toList.toArray
  let mut out : Array ETok := #[]
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      if c == ' ' || c == '\t' then
        i := i + 1
      else if c.isDigit || c == '.' then
        let mut j := i
        for _ in [i:cs.size] do
          if h' : j < cs.size then
            if cs[j].isDigit || cs[j] == '.' then j := j + 1 else break
          else break
        let some (m, sc) := parseDecimal (String.ofList (cs.extract i j).toList)
          | return none
        out := out.push (.num m sc)
        i := j
      else if c == '\\' then
        let mut j := i + 1
        for _ in [i + 1:cs.size] do
          if h' : j < cs.size then
            if cs[j].isAlpha || cs[j] == '@' then j := j + 1 else break
          else break
        if j == i + 1 then return none
        let n := String.ofList (cs.extract (i + 1) j).toList
        if n == "dimexpr" then out := out.push .dimexpr
        else if n == "relax" then out := out.push .relax
        else out := out.push (.ident n)
        i := j
      else if c.isAlpha || c == '_' || c == '@' then
        let mut j := i
        for _ in [i:cs.size] do
          if h' : j < cs.size then
            if cs[j].isAlphanum || cs[j] == '_' || cs[j] == '@' then j := j + 1 else break
          else break
        out := out.push (.ident (String.ofList (cs.extract i j).toList))
        i := j
      else if c == '+' then out := out.push .plus; i := i + 1
      else if c == '-' then out := out.push .minus; i := i + 1
      else if c == '*' then out := out.push .times; i := i + 1
      else if c == '/' then out := out.push .divide; i := i + 1
      else if c == '(' then out := out.push .lparen; i := i + 1
      else if c == ')' then out := out.push .rparen; i := i + 1
      else return none
  return some out

/-- An operand mid-parse: a bare number, or a length expression. -/
private inductive EVal where
  | scalar (mantissa : Int) (scale : Nat)
  | len (e : LenExpr)

private def applyBinOp (op : Char) (a b : EVal) : Except String EVal :=
  match op, a, b with
  | '+', .len x, .len y => .ok (.len (.add x y))
  | '-', .len x, .len y => .ok (.len (.sub x y))
  | '+', .scalar m s, .scalar m' s' => .ok (.scalar (m * s' + m' * s) (s * s'))
  | '-', .scalar m s, .scalar m' s' => .ok (.scalar (m * s' - m' * s) (s * s'))
  | '*', .scalar m s, .len e => .ok (.len (Affine.scaleQ m s e))
  | '*', .len e, .scalar m s => .ok (.len (Affine.scaleQ m s e))
  | '*', .scalar m s, .scalar m' s' => .ok (.scalar (m * m') (s * s'))
  | '*', .len _, .len _ => .error "a length times a length has no meaning"
  | '/', _, .scalar 0 _ => .error "division by zero"
  | '/', .len e, .scalar m s =>
    .ok (.len (Affine.scaleQ (if m < 0 then -(s : Int) else (s : Int)) m.natAbs e))
  | '/', .scalar m s, .scalar m' s' =>
    .ok (.scalar (if m' < 0 then -(m * s') else m * s') (s * m'.natAbs))
  | '/', _, .len _ => .error "dividing by a length has no meaning"
  | _, _, _ => .error "a bare number in a length expression needs a unit"

private def opPrec (op : Char) : Nat :=
  if op == 'u' then 3 else if op == '*' || op == '/' then 2 else 1

/-- Pop and apply one operator from the stack. -/
private def popOne (vals : Array EVal) (op : Char) : Except String (Array EVal) := do
  if op == 'u' then
    match vals.back? with
    | some (.scalar m s) => return vals.pop.push (.scalar (-m) s)
    | some (.len e) => return vals.pop.push (.len (Affine.scaleQ (-1) 1 e))
    | none => throw "malformed expression"
  else
    match vals.back?, vals.pop.back? with
    | some b, some a => return (vals.pop.pop).push (← applyBinOp op a b)
    | _, _ => throw "malformed expression"

/-- Stacks `c`, first draining every operator on the stack
that binds at least as tightly. -/
private def pushOp (vals : Array EVal) (ops : Array Char) (c : Char) :
    Except String (Array EVal × Array Char) := do
  let mut vals := vals
  let mut ops := ops
  for _ in [0:ops.size + 1] do
    match ops.back? with
    | some top =>
      if top != '(' && top != 'd' && opPrec top ≥ opPrec c then
        vals ← popOne vals top
        ops := ops.pop
      else break
    | none => break
  return (vals, ops.push c)

/-- Parses a token stream into an expression: shunting-yard with unary minus,
implicit coefficients and units. -/
private def exprParse (toks : Array ETok) : Except String LenExpr := do
  let mut vals : Array EVal := #[]
  let mut ops : Array Char := #[]
  let mut prevOperand := false
  for t in toks do
    match t with
    | .num m s =>
      if prevOperand then throw "malformed expression"
      vals := vals.push (.scalar m s)
      prevOperand := true
    | .ident n =>
      match vals.back?, prevOperand with
      | some (.scalar m s), true =>
        -- The number before it binds: a unit makes a literal, a token name a coefficient.
        match lengthOfUnit m s n with
        | some l => vals := vals.pop.push (.len (.lit { width := l }))
        | none => vals := vals.pop.push (.len (Affine.scaleQ m s (.ref n)))
      | _, true => throw "malformed expression"
      | _, false =>
        vals := vals.push (.len (.ref n))
        prevOperand := true
    | .dimexpr =>
      if prevOperand then
        match vals.back? with
        | some (.scalar _ _) =>
          let (vals', ops') ← pushOp vals ops '*'
          vals := vals'
          ops := ops'
        | _ => throw "a length times a length has no meaning"
      ops := ops.push 'd'
      prevOperand := false
    | .relax =>
      unless prevOperand do throw "empty \\dimexpr"
      let mut closed := false
      for _ in [0:ops.size + 1] do
        match ops.back? with
        | some 'd' =>
          ops := ops.pop
          closed := true
          break
        | some '(' => throw "unbalanced '(' before \\relax"
        | some top =>
          vals ← popOne vals top
          ops := ops.pop
        | none => break
      unless closed do throw "unexpected \\relax"
      prevOperand := true
    | .plus | .minus =>
      let isMinus := t == ETok.minus
      if prevOperand then
        let (vals', ops') ← pushOp vals ops (if isMinus then '-' else '+')
        vals := vals'
        ops := ops'
        prevOperand := false
      else if isMinus then
        -- Unary: highest precedence, applied to the next operand alone.
        ops := ops.push 'u'
      -- A unary plus says nothing; it is skipped.
    | .times =>
      unless prevOperand do throw "malformed expression"
      let (vals', ops') ← pushOp vals ops '*'
      vals := vals'
      ops := ops'
      prevOperand := false
    | .divide =>
      unless prevOperand do throw "malformed expression"
      if ops.contains 'd' then
        throw "'\\dimexpr' division rounds to nearest"
      let (vals', ops') ← pushOp vals ops '/'
      vals := vals'
      ops := ops'
      prevOperand := false
    | .lparen =>
      if prevOperand then throw "malformed expression"
      ops := ops.push '('
      prevOperand := false
    | .rparen =>
      unless prevOperand do throw "malformed expression"
      let mut closed := false
      for _ in [0:ops.size + 1] do
        match ops.back? with
        | some '(' =>
          ops := ops.pop
          closed := true
          break
        | some 'd' => throw "unbalanced ')'"
        | some top =>
          vals ← popOne vals top
          ops := ops.pop
        | none => break
      unless closed do throw "unbalanced ')'"
      prevOperand := true
  unless prevOperand do throw "malformed expression"
  for _ in [0:ops.size + 1] do
    match ops.back? with
    | some '(' => throw "unbalanced '('"
    | some 'd' => ops := ops.pop
    | some top =>
      vals ← popOne vals top
      ops := ops.pop
    | none => break
  match vals.back?, vals.size with
  | some (.len e), 1 => return e
  | some (.scalar _ _), 1 => throw "a bare number in a length expression needs a unit"
  | _, _ => throw "malformed expression"

/-- Inches per unit, exactly as the engine reads the unit everywhere (`unitScale`), so a point is a
big point; `none` for a font-relative or unknown unit. -/
public def unitInches (u : String) : Option Rat :=
  (unitScale u).map fun (n, d) => (n : Rat) / ((d : Rat) * 72 * (spPerPt : Rat))

/-- An operand of an exact evaluation: a bare number, or a length in inches. -/
private inductive XVal where
  | scalar (v : Rat)
  | len (v : Rat)

private def xApply (op : Char) (a b : XVal) : Option XVal :=
  match op, a, b with
  | '+', .len x, .len y => some (.len (x + y))
  | '-', .len x, .len y => some (.len (x - y))
  | '+', .scalar x, .scalar y => some (.scalar (x + y))
  | '-', .scalar x, .scalar y => some (.scalar (x - y))
  | '*', .scalar x, .len y => some (.len (x * y))
  | '*', .len x, .scalar y => some (.len (x * y))
  | '*', .scalar x, .scalar y => some (.scalar (x * y))
  | '/', .len x, .scalar y => if y == 0 then none else some (.len (x / y))
  | '/', .scalar x, .scalar y => if y == 0 then none else some (.scalar (x / y))
  | _, _, _ => none

private def xPop (vals : Array XVal) (op : Char) : Option (Array XVal) :=
  if op == 'u' then
    vals.back?.map fun x => match x with
      | .scalar v => vals.pop.push (.scalar (-v))
      | .len v => vals.pop.push (.len (-v))
  else
    match vals.back?, vals.pop.back? with
    | some b, some a => (xApply op a b).map fun v => vals.pop.pop.push v
    | _, _ => none

/-- Stacks `c` after applying every stacked operator binding at least as tightly. -/
private def xPush (vals : Array XVal) (ops : Array Char) (c : Char) :
    Option (Array XVal × Array Char) := do
  let mut vals := vals
  let mut ops := ops
  for _ in [0:ops.size + 1] do
    match ops.back? with
    | some top =>
      if top != '(' && top != 'd' && opPrec top ≥ opPrec c then
        vals ← xPop vals top
        ops := ops.pop
      else break
    | none => break
  return (vals, ops.push c)

/-- Applies stacked operators down to the bracket `stop`, which it removes. -/
private def xClose (vals : Array XVal) (ops : Array Char) (stop : Char) :
    Option (Array XVal × Array Char) := do
  let mut vals := vals
  let mut ops := ops
  for _ in [0:ops.size + 1] do
    match ops.back? with
    | some top =>
      ops := ops.pop
      if top == stop then return (vals, ops)
      if top == '(' || top == 'd' then failure
      vals ← xPop vals top
    | none => failure
  failure

/-- A length expression's exact value in inches, every unit as `unitInches` reads it and every name
through `look`, with no rounding at any step; `none` outside the grammar `exprParse` reads or at a
font-relative unit. -/
public def exactLength (look : String → Option Rat) (s : String) : Option Rat := do
  let toks ← exprToks s.trimAscii.toString
  let mut vals : Array XVal := #[]
  let mut ops : Array Char := #[]
  let mut prev := false
  for t in toks do
    match t with
    | .num m sc =>
      if prev then failure
      vals := vals.push (.scalar ((m : Rat) / (sc : Rat)))
      prev := true
    | .ident n =>
      match vals.back?, prev with
      | some (.scalar v), true =>
        match unitInches n with
        | some u => vals := vals.pop.push (.len (v * u))
        | none => vals := vals.pop.push (.len (v * (← look n)))
      | _, true => failure
      | _, false =>
        vals := vals.push (.len (← look n))
        prev := true
    | .dimexpr =>
      if prev then failure
      ops := ops.push 'd'
    | .relax =>
      unless prev do failure
      let (v, o) ← xClose vals ops 'd'
      vals := v
      ops := o
    | .plus | .minus =>
      if prev then
        let (v, o) ← xPush vals ops (if t == ETok.minus then '-' else '+')
        vals := v
        ops := o
        prev := false
      else if t == ETok.minus then ops := ops.push 'u'
    | .times | .divide =>
      unless prev do failure
      let (v, o) ← xPush vals ops (if t == ETok.times then '*' else '/')
      vals := v
      ops := o
      prev := false
    | .lparen =>
      if prev then failure
      ops := ops.push '('
    | .rparen =>
      unless prev do failure
      let (v, o) ← xClose vals ops '('
      vals := v
      ops := o
  unless prev do failure
  for _ in [0:ops.size + 1] do
    match ops.back? with
    | some '(' => failure
    | some 'd' => ops := ops.pop
    | some top =>
      vals ← xPop vals top
      ops := ops.pop
    | none => break
  match vals.toList with
  | [.len v] => return v
  | _ => failure

/-- Parses one length expression without resolving its references. -/
public def parseLengthSyntax (s : String) : Except String LenExpr := do
  let some toks := exprToks s.trimAscii.toString
    | throw "malformed expression"
  exprParse toks

/-- Reads a length expression against declared tokens. -/
public def parseLengthExpr (tokens : Array (String × SymGlue)) (s : String) :
    Except String SymGlue := do
  let e ← parseLengthSyntax s
  match e.eval (fun n => (tokens.find? (·.1 == n)).map (·.2)) with
  | .ok g => return g
  | .error n => throw s!"'{n}' is not a declared token"

/-- Parses a context-resolved length: declared tokens become literals, local
measures typed references. -/
public def parseAffineLengthExprFor (tokens : Array (String × SymGlue))
    (admits : Measure → Bool) (s : String) : Except String (Affine Measure) := do
  let e ← parseLengthSyntax s
  Affine.bind (fun n =>
    match Measure.ofName? n with
    | some m =>
      if admits m then .ok (.ref m)
      else .error s!"'{m.label}' is not available in this length context"
    | none =>
      match tokens.find? (·.1 == n) with
      | some (_, g) => .ok (.lit g)
      | none => .error s!"'{n}' is not a declared token or local measure") e

/-- The unrestricted typed parser, for consumers that supply all measures. -/
public def parseAffineLengthExpr (tokens : Array (String × SymGlue)) (s : String) :
    Except String (Affine Measure) :=
  parseAffineLengthExprFor tokens (fun _ => true) s

/-- Whether the length-expression grammar reads `s`, names unresolved. -/
public def readsAsLengthExpr (s : String) : Bool :=
  match exprToks s.trimAscii.toString with
  | some toks => (exprParse toks).isOk
  | none => false

/-- Whether a string looks like a length expression rather
than a single value. -/
public def looksLikeExpr (s : String) : Bool := Id.run do
  let cs := s.toList
  let mut prevDigit := false
  let mut i := 0
  for c in cs do
    if c == '(' || c == ')' || c == '*' || c == '/' then return true
    if (c == '+' || c == '-') && i > 0 then return true
    if prevDigit && (c.isAlpha || c == '_') then
      let rest := String.ofList (cs.drop i)
      let unit := String.ofList (rest.toList.takeWhile fun c => c.isAlphanum || c == '_')
      if (lengthOfUnit 1 1 unit).isNone then return true
    prevDigit := c.isDigit
    i := i + 1
  return false

/-- A modelled colour carried inside the native declaration grammar. -/
private def parseModeledValue (s : String) : Option Value :=
  match parseColorSpec none s with
  | .ok (.html r g b) => some (.color r g b)
  | .ok (.rgbByte r g b) => some (.color r.rgbByte g.rgbByte b.rgbByte)
  | .ok (.rgbUnit r g b) => some (.color r.unitByte g.unitByte b.unitByte)
  | .ok (.gray v) => some (.color v.unitByte v.unitByte v.unitByte)
  | .ok (.cmyk c m y k) => some (.cmyk c.milli m.milli y.milli k.milli)
  | .ok (.oklab L a b) =>
    (ColorSpec.oklab L a b).okLab?.map fun l => let c := Oklab.ofLab l; .color c.r c.g c.b
  | .ok (.oklch L C H) =>
    (ColorSpec.oklch L C H).okLab?.map fun l => let c := Oklab.ofLab l; .color c.r c.g c.b
  | .ok (.spot _ c m y k) => some (.cmyk c.milli m.milli y.milli k.milli)
  | .ok (.named _) | .error _ => none

/-- Whether `digits:digits` is a name, such as a slide stage `16:9`. -/
private def isRatioName (s : String) : Bool :=
  match s.splitOn ":" with
  | [a, b] =>
    !a.isEmpty && !b.isEmpty &&
      a.toList.all (·.isDigit) && b.toList.all (·.isDigit)
  | _ => false

/-- A string's characters as a string literal's body: each quote doubled. -/
public def doubleQuotes : List Char → List Char
  | [] => []
  | c :: rest => if c == '"' then '"' :: '"' :: doubleQuotes rest else c :: doubleQuotes rest

/-- A string literal's body read back: a doubled quote is one quote. -/
public def undoubleQuotes : List Char → List Char
  | '"' :: '"' :: rest => '"' :: undoubleQuotes rest
  | c :: rest => c :: undoubleQuotes rest
  | [] => []

/-- `s` as a declaration string literal, which `parseValue` reads back as `s` (`parseValue_quote`). -/
public def quote (s : String) : String := String.ofList ('"' :: doubleQuotes s.toList ++ ['"'])

/-- The text of a string literal trimmed as `trimAscii` trims, when it is one. -/
public def stringBody? (cs : List Char) : Option (List Char) :=
  match ((cs.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace) with
  | '"' :: rev =>
    match rev.reverse with
    | '"' :: body => some (undoubleQuotes body)
    | _ => none
  | _ => none

public def parseValue (raw : String) (tokens : Array (String × SymGlue) := #[]) : Option Value :=
  let s := raw.trimAscii.toString
  if let some body := stringBody? raw.toList then
    some (.str (String.ofList body))
  else if s.startsWith "#" || (wrappedColor s).isSome || spotSource s then
    parseModeledValue s
  else if s.startsWith "{" && s.endsWith "}" && s.length ≥ 2 then
    -- Nested blocks stay opaque; the declaration decides whether it takes one.
    some (.block (String.ofList (s.toList.drop 1).dropLast |>.trimAscii.toString))
  else if (s.splitOn "*").length == 2 then
    parseScaled tokens s <|>
      (if looksLikeExpr s then (parseLengthExpr tokens s).toOption.map .glue else none)
  else if (s.splitOn " plus ").length > 1 || (s.splitOn " minus ").length > 1 then
    (parseGlue s).map Value.glue
  else if s.endsWith "em" || s.endsWith "ex" then
    ((parseLength s).map fun l => Value.glue { width := l }) <|>
      (if looksLikeExpr s then (parseLengthExpr tokens s).toOption.map .glue else none)
  else if let some (_, g) := tokens.find? (·.1 == s) then
    some (.glue g)
  else if s == "fill" || s == "fil" then
    -- LaTeX's `\fill`: zero width, first-order infinite stretch.
    some (.glue { fil := true })
  else
    let digits := s.toList.takeWhile fun c => c.isDigit || c == '.' || c == '-' || c == '+'
    let unit := String.ofList (s.toList.drop digits.length) |>.trimAscii.toString
    match parseDecimal (String.ofList digits), unitScale unit with
    | some (mantissa, scale), some (num, den) =>
      some (.dim (mantissa * num / (scale * den : Nat)))
    | some (mantissa, 1), none =>
      if unit.isEmpty then some (.int mantissa)
      else if isRatioName s then some (.ident s)
      else if looksLikeExpr s then (parseLengthExpr tokens s).toOption.map .glue
      else none
    | _, _ =>
      if looksLikeExpr s then (parseLengthExpr tokens s).toOption.map .glue
      else if !s.isEmpty && s.toList.all isIdentChar then some (.ident s) else none

private theorem undoubleQuotes_cons (c : Char) (h : c ≠ '"') (x : List Char) :
    undoubleQuotes (c :: x) = c :: undoubleQuotes x := by
  cases x with
  | nil => simp [undoubleQuotes]
  | cons d y => simp [undoubleQuotes, h]

private theorem undoubleQuotes_doubleQuotes (cs : List Char) :
    undoubleQuotes (doubleQuotes cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    by_cases h : c = '"'
    · subst h
      simp only [doubleQuotes, BEq.rfl, ↓reduceIte, undoubleQuotes, ih]
    · have hb : (c == '"') = false := by simpa using h
      simp only [doubleQuotes, hb, Bool.false_eq_true, ↓reduceIte, undoubleQuotes_cons c h, ih]

private theorem stringBody?_quote (s : String) : stringBody? (quote s).toList = some s.toList := by
  have hq : ¬ Char.isWhitespace '"' = true := by decide
  simp [stringBody?, quote, hq, List.reverse_append, undoubleQuotes_doubleQuotes]

public theorem parseValue_quote (s : String) (tokens : Array (String × SymGlue)) :
    parseValue (quote s) tokens = some (.str s) := by
  simp only [parseValue, stringBody?_quote, String.ofList_toList]

/-- Parses a `key = value, ...` block, reporting malformed entries. -/
public def parseBlock (file : String) (src : String) (pos : Pos) (what : String)
    (tokens : Array (String × SymGlue) := #[]) : Array Entry × Array Diag := Id.run do
  let mut entries : Array Entry := #[]
  let mut diags : Array Diag := #[]
  for entry in splitEntries src do
    let (key, valueSrc) := entryOf entry
    -- Keys admit `-`; in values it is subtraction.
    if key.isEmpty || !key.toList.all (fun c => isIdentChar c || c == '-') then
      diags := diags.push (Diag.of .E0320
        s!"invalid key in '\\{what}': {entry.quote}" (some ⟨file, pos⟩)
        (help := "entries look like: key = value"))
    else if valueSrc.isEmpty then
      diags := diags.push (Diag.of .E0320
        s!"'{key}' in '\\{what}' has no value" (some ⟨file, pos⟩)
        (help := "entries look like: key = value"))
    else
      match parseValue valueSrc tokens with
      | some v => entries := entries.push ⟨key, v⟩
      | none =>
        let detail := if looksLikeExpr valueSrc then
            match parseLengthExpr tokens valueSrc with
            | .error e => s!": {e}"
            | .ok _ => ""
          else ""
        diags := diags.push (Diag.of .E0321
          s!"cannot read value for '{key}' in '\\{what}': {valueSrc.quote}{detail}"
          (some ⟨file, pos⟩) (help :=
            "values are \"strings\", dimensions (10pt, 0.5in), length expressions \
(a + 2b), numbers, names, or #RRGGBB colors"))
  return (entries, diags)

public def splitEntry (entry : String) : Option (String × String) :=
  let (k, v) := entryOf entry
  if k.isEmpty || v.isEmpty then none else some (k, v)

/-- Rejects keys the declaration does not define, naming the ones it does. -/
public def unknownKey (file : String) (what key : String) (known : List String)
    (pos : Pos) : Diag :=
  Diag.of .E0322 s!"'\\{what}' has no key '{key}'" (some ⟨file, pos⟩)
    (help := s!"known keys: {String.intercalate ", " known}")
    (subject := some s!"param:\\{what}:{key}")

public def wrongType (file : String) (what key expected : String) (got : Value)
    (pos : Pos) : Diag :=
  Diag.of .E0323 s!"'{key}' in '\\{what}' expects {expected}, got a {got.kindName}"
    (some ⟨file, pos⟩)

end LeanTex.Core.Decl
