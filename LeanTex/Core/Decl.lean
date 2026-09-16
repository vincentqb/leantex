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
  deriving Repr, BEq

def Value.kindName : Value → String
  | .str _ => "string"
  | .dim _ => "dimension"
  | .int _ => "number"
  | .ident _ => "name"
  | .block _ => "block"

structure Entry where
  key : String
  value : Value
  deriving Repr, BEq

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.'

/-- Split on commas that are not inside braces, brackets, or quotes. -/
private def splitEntries (s : String) : List String := Id.run do
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
private def parseDecimal (s : String) : Option (Int × Nat) := Id.run do
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
private def unitScale : String → Option (Int × Nat)
  | "sp" => some (1, 1)
  | "pt" => some (spPerPt, 1)
  | "bp" => some (spPerPt, 1)
  | "in" => some (72 * spPerPt, 1)
  | "cm" => some (7200 * spPerPt, 254)
  | "mm" => some (7200 * spPerPt, 2540)
  | "pc" => some (12 * spPerPt, 1)
  | _ => none

def parseValue (raw : String) : Option Value :=
  let s := raw.trimAscii.toString
  if s.startsWith "\"" && s.endsWith "\"" && s.length ≥ 2 then
    some (.str (String.ofList (s.toList.drop 1).dropLast))
  else if s.startsWith "{" && s.endsWith "}" && s.length ≥ 2 then
    -- Nested blocks stay opaque; the declaration decides whether it takes one.
    some (.block (String.ofList (s.toList.drop 1).dropLast |>.trimAscii.toString))
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
def parseBlock (file : String) (src : String) (pos : Pos) (what : String) :
    Array Entry × Array Diag := Id.run do
  let mut entries : Array Entry := #[]
  let mut diags : Array Diag := #[]
  for entry in splitEntries src do
    match entry.splitOn "=" with
    | key :: rest =>
      let key := key.trimAscii.toString
      let valueSrc := String.intercalate "=" rest |>.trimAscii.toString
      if key.isEmpty || !key.toList.all isIdentChar then
        diags := diags.push {
          severity := .error
          code := "E0320"
          message := s!"invalid key in \\{what}: {entry.quote}"
          span := some ⟨file, pos⟩
          help := some "entries look like: key = value"
        }
      else if valueSrc.isEmpty then
        diags := diags.push {
          severity := .error
          code := "E0320"
          message := s!"'{key}' in \\{what} has no value"
          span := some ⟨file, pos⟩
          help := some "entries look like: key = value"
        }
      else
        match parseValue valueSrc with
        | some v => entries := entries.push ⟨key, v⟩
        | none =>
          diags := diags.push {
            severity := .error
            code := "E0321"
            message := s!"cannot read value for '{key}' in \\{what}: {valueSrc.quote}"
            span := some ⟨file, pos⟩
            help := some "values are \"strings\", dimensions (10pt, 0.5in), numbers, or names"
          }
    | [] => pure ()
  return (entries, diags)

/-- Reject keys the declaration does not define, naming the ones it does. -/
def unknownKey (file : String) (what key : String) (known : List String)
    (pos : Pos) : Diag :=
  { severity := .error
    code := "E0322"
    message := s!"\\{what} has no key '{key}'"
    span := some ⟨file, pos⟩
    help := some s!"known keys: {String.intercalate ", " known}" }

def wrongType (file : String) (what key expected : String) (got : Value)
    (pos : Pos) : Diag :=
  { severity := .error
    code := "E0323"
    message := s!"'{key}' in \\{what} expects {expected}, got a {got.kindName}"
    span := some ⟨file, pos⟩ }

end LeanTex.Core.Decl
