import LeanTex.Core.Diag
import LeanTex.Core.Dim

namespace LeanTex.Core.Decl

open LeanTex.Core LeanTex.Core.Dim

/-- A declaration value. Absolute dimensions resolve here; font-relative
units (ex, em) are not accepted yet — they need the symbolic lengths that
arrive with `\tokens`. -/
inductive Value where
  | str (s : String)
  | dim (sp : Sp)
  | int (n : Int)
  | ident (s : String)
  | block (src : String)
  | color (r g b : UInt8)
  /-- A glue expression, possibly font-relative or scaled from a token. -/
  | glue (g : SymGlue)
  deriving Repr, BEq

def Value.kindName : Value → String
  | .str _ => "string"
  | .dim _ => "dimension"
  | .int _ => "number"
  | .ident _ => "name"
  | .block _ => "block"
  | .color _ _ _ => "color"
  | .glue _ => "length"

structure Entry where
  key : String
  value : Value
  deriving Repr, BEq

private def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `#RGB` or `#RRGGBB`. -/
private def parseColor (s : String) : Option Value := do
  let cs := s.toList
  match cs with
  | '#' :: rest =>
    let digits ← rest.mapM hexDigit?
    match digits with
    | [r, g, b] =>
      -- #abc means #aabbcc, as in CSS
      some (.color (UInt8.ofNat (r * 17)) (UInt8.ofNat (g * 17)) (UInt8.ofNat (b * 17)))
    | [r1, r2, g1, g2, b1, b2] =>
      some (.color (UInt8.ofNat (r1 * 16 + r2)) (UInt8.ofNat (g1 * 16 + g2))
        (UInt8.ofNat (b1 * 16 + b2)))
    | _ => none
  | _ => none

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.'

/-- Split on commas that are not inside braces, brackets, or quotes. Public
because a declaration whose entries may refer to earlier entries has to walk
them one at a time. -/
def splitEntries (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut cur := ""
  let mut depth := 0
  let mut inStr := false
  for c in s.toList do
    if inStr then
      cur := cur.push c
      if c == '"' then inStr := false
    else if c == '"' then
      cur := cur.push c
      inStr := true
    else if c == '{' || c == '[' then
      depth := depth + 1
      cur := cur.push c
    else if c == '}' || c == ']' then
      depth := depth - 1
      cur := cur.push c
    else if c == ',' && depth == 0 then
      out := out ++ [cur]
      cur := ""
    else
      cur := cur.push c
  out := out ++ [cur]
  return out.filterMap fun e =>
    let t := e.trimAscii.toString
    if t.isEmpty then none else some t

/-- Decimal literal as mantissa and scale: "0.5" ↦ (5, 10). -/
def parseDecimal (s : String) : Option (Int × Nat) := Id.run do
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

/-- sp per unit, expressed as a fraction so conversions stay exact. -/
private def unitScaleBase : String → Option (Int × Nat)
  | "sp" => some (1, 1)
  | "pt" => some (spPerPt, 1)
  | "bp" => some (spPerPt, 1)
  | "in" => some (72 * spPerPt, 1)
  | "cm" => some (7200 * spPerPt, 254)
  | "mm" => some (7200 * spPerPt, 2540)
  | "pc" => some (12 * spPerPt, 1)
  -- the CSS pixel: 1px = 1/96 in exactly (CSS Values and Units 4 §6.2),
  -- so 96 px = 72 pt — the unit a web-facing length (a scroll distance)
  -- is naturally written in
  | "px" => some (72 * spPerPt, 96)
  -- The didot point, TeX's continental unit: 1157 dd = 1238 TeX pt
  -- (TeXbook ch. 10), and 7227 TeX pt = 100 in, so
  -- dd = 1238·7200⁄(1157·7227) of this engine's 1⁄72-inch point —
  -- unreduced, so the relation to `in` is literal in the theorem below.
  | "dd" => some (8913600 * spPerPt, 8361639)
  | "cc" => some (12 * 8913600 * spPerPt, 8361639)
  | _ => none

/-- A `true` unit is its plain counterpart, exactly. TeX's `truept`,
`truein`, … mean "unscaled by magnification": "if you want an unmagnified
unit, you can say `true`" and true dimensions stay constant whatever `\mag`
is (TeXbook ch. 10). This engine has no magnification — every dimension is
already true — so the prefix denotes the identity. Reading it as part of a
unit *name* was the defect: `1.75truein` parsed as a name and E0323 said
"expects a length … got a name". A unit added to the base table gets its
`true` twin here, or `unitScale_true` below fails to extend. -/
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

/-- The unit table is one system, not ten constants: bp is the PDF point
(leantex's pt), an inch is 72 of them, a pica 12, cm and mm follow from
1 in = 2.54 cm exactly, sp is the fixed point itself, the CSS pixel is
1⁄96 inch, a cicero is 12 didots, and the didot keeps TeX's own ratio to
the inch (1157 dd = 1238 TeX pt and 7227 TeX pt = 100 in, TeXbook ch. 10;
the dd fraction is stored unreduced so its relation below is literal). A
typo in any one entry breaks a relation here. -/
theorem unitScale_consistent :
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

/-- Every `true` unit denotes exactly its plain counterpart — stated over
the whole table, so a unit added without this identity breaks the build,
not a document. -/
theorem unitScale_true :
    unitScale "truesp" = unitScale "sp" ∧ unitScale "truept" = unitScale "pt" ∧
    unitScale "truebp" = unitScale "bp" ∧ unitScale "truein" = unitScale "in" ∧
    unitScale "truecm" = unitScale "cm" ∧ unitScale "truemm" = unitScale "mm" ∧
    unitScale "truepc" = unitScale "pc" ∧ unitScale "truepx" = unitScale "px" ∧
    unitScale "truedd" = unitScale "dd" ∧ unitScale "truecc" = unitScale "cc" := by
  decide

/-- A single length term: a number with an absolute or font-relative unit. -/
def parseLength (s : String) : Option Length :=
  let s := s.trimAscii.toString
  let digits := s.toList.takeWhile fun c => c.isDigit || c == '.' || c == '-' || c == '+'
  let unit := (String.ofList (s.toList.drop digits.length)).trimAscii.toString
  match parseDecimal (String.ofList digits) with
  | none => none
  | some (mantissa, scale) =>
    if unit == "em" then
      some { em := mantissa * 1000 / scale }
    else if unit == "ex" then
      some { ex := mantissa * 1000 / scale }
    else
      match unitScale unit with
      | some (num, den) => some (Length.ofSp (mantissa * num / (scale * den : Nat)))
      | none => none

/-- `<len> [plus <len>] [minus <len>]`, TeX's glue spelling. -/
def parseGlue (s : String) : Option SymGlue := do
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
def parseScaled (tokens : Array (String × SymGlue)) (s : String) : Option Value :=
  match s.splitOn "*" with
  | [factor, name] => do
    let (mantissa, scale) ← parseDecimal (factor.trimAscii.toString)
    let key := name.trimAscii.toString
    let (_, g) ← tokens.find? (·.1 == key)
    some (.glue (g.scale mantissa scale))
  | _ => none

def parseValue (raw : String) (tokens : Array (String × SymGlue) := #[]) : Option Value :=
  let s := raw.trimAscii.toString
  if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2 then
    some (.str (String.ofList (s.toList.drop 1).dropLast))
  else if s.startsWith "#" then
    parseColor s
  else if s.startsWith "{" && s.endsWith "}" && s.length ≥ 2 then
    -- Nested blocks stay opaque; the declaration decides whether it takes one.
    some (.block (String.ofList (s.toList.drop 1).dropLast |>.trimAscii.toString))
  else if (s.splitOn "*").length == 2 then
    parseScaled tokens s
  else if (s.splitOn " plus ").length > 1 || (s.splitOn " minus ").length > 1 then
    (parseGlue s).map Value.glue
  else if s.endsWith "em" || s.endsWith "ex" then
    (parseLength s).map fun l => Value.glue { width := l }
  else if let some (_, g) := tokens.find? (·.1 == s) then
    some (.glue g)
  else
    -- dimension: digits then a unit suffix
    let digits := s.toList.takeWhile fun c => c.isDigit || c == '.' || c == '-' || c == '+'
    let unit := String.ofList (s.toList.drop digits.length) |>.trimAscii.toString
    match parseDecimal (String.ofList digits), unitScale unit with
    | some (mantissa, scale), some (num, den) =>
      some (.dim (mantissa * num / (scale * den : Nat)))
    | some (mantissa, 1), none =>
      if unit.isEmpty then some (.int mantissa) else none
    | _, _ =>
      if !s.isEmpty && s.toList.all isIdentChar then some (.ident s) else none

/-- Parse a `key = value, ...` block. Reports malformed entries; the caller
validates keys, so an unknown key is not an error here. -/
def parseBlock (file : String) (src : String) (pos : Pos) (what : String)
    (tokens : Array (String × SymGlue) := #[]) : Array Entry × Array Diag := Id.run do
  let mut entries : Array Entry := #[]
  let mut diags : Array Diag := #[]
  for entry in splitEntries src do
    match entry.splitOn "=" with
    | key :: rest =>
      let key := key.trimAscii.toString
      let valueSrc := String.intercalate "=" rest |>.trimAscii.toString
      if key.isEmpty || !key.toList.all isIdentChar then
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
          diags := diags.push (Diag.of .E0321
            s!"cannot read value for '{key}' in '\\{what}': {valueSrc.quote}"
            (some ⟨file, pos⟩) (help :=
              "values are \"strings\", dimensions (10pt, 0.5in), numbers, names, or #RRGGBB colors"))
    | [] => pure ()
  return (entries, diags)

/-- Split one `key = value` entry. -/
def splitEntry (entry : String) : Option (String × String) :=
  match entry.splitOn "=" with
  | key :: rest =>
    let k := key.trimAscii.toString
    let v := (String.intercalate "=" rest).trimAscii.toString
    if k.isEmpty || v.isEmpty then none else some (k, v)
  | [] => none

/-- Reject keys the declaration does not define, naming the ones it does. -/
def unknownKey (file : String) (what key : String) (known : List String)
    (pos : Pos) : Diag :=
  Diag.of .E0322 s!"'\\{what}' has no key '{key}'" (some ⟨file, pos⟩)
    (help := s!"known keys: {String.intercalate ", " known}")

def wrongType (file : String) (what key expected : String) (got : Value)
    (pos : Pos) : Diag :=
  Diag.of .E0323 s!"'{key}' in '\\{what}' expects {expected}, got a {got.kindName}"
    (some ⟨file, pos⟩)

end LeanTex.Core.Decl
