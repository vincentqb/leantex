module

public import LeanTex.Core.CssColorData
public import LeanTex.Core.Color
import LeanTex.Core.PathData

/-! CSS colour values an SVG paint may spell (CSS Color 4 §4–§6), and the named-colour table's contract. -/

namespace LeanTex.Core.CssColor

open LeanTex.Core

/-- A colour value: its sRGB channels, and its alpha in thousandths. -/
public structure Value where
  color : Ir.Color
  alpha : Nat
  deriving Repr, Inhabited

/-- The table's keywords, in order. -/
@[expose] public def keywords : List String := CssColorData.table.toList.map (·.1)

public theorem keywords_contract : keywords.Pairwise (· < ·) := by
  decide +kernel

public theorem channels_contract :
    CssColorData.table.toList.all (fun (_, r, g, b) => r < 256 && g < 256 && b < 256) = true := by
  decide +kernel

/-- A named colour, its keyword read without regard to ASCII case. -/
public def named? (s : String) : Option (Nat × Nat × Nat) :=
  let k := s.toLower
  (CssColorData.table.find? (·.1 == k)).map (·.2)

public theorem named?_mem (s : String) (v : Nat × Nat × Nat) (h : named? s = some v) :
    ∃ n, (n, v) ∈ CssColorData.table := by
  unfold named? at h
  cases hf : CssColorData.table.find? (·.1 == s.toLower) with
  | none => simp [hf] at h
  | some row =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    exact ⟨row.1, by rw [← h]; exact Array.mem_of_find?_eq_some hf⟩

private def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

private def byte (n : Nat) : UInt8 := (min n 255).toUInt8

/-- An alpha byte in thousandths, rounded. -/
@[expose] public def alphaOfByte (a : Nat) : Nat := (min a 255 * 1000 + 127) / 255

/-- `#rgb`, `#rgba`, `#rrggbb`, `#rrggbbaa`. -/
public def hex? (s : String) : Option Value := do
  let cs := s.toList
  let ds ← (cs.drop 1).mapM hexDigit
  if cs.head? != some '#' then none
  match ds with
  | [r, g, b] => some { color := { r := byte (r * 17), g := byte (g * 17), b := byte (b * 17) }, alpha := 1000 }
  | [r, g, b, a] =>
    some { color := { r := byte (r * 17), g := byte (g * 17), b := byte (b * 17) }, alpha := alphaOfByte (a * 17) }
  | [r1, r2, g1, g2, b1, b2] =>
    some { color := { r := byte (r1 * 16 + r2), g := byte (g1 * 16 + g2), b := byte (b1 * 16 + b2) }, alpha := 1000 }
  | [r1, r2, g1, g2, b1, b2, a1, a2] =>
    some { color := { r := byte (r1 * 16 + r2), g := byte (g1 * 16 + g2), b := byte (b1 * 16 + b2) }
           alpha := alphaOfByte (a1 * 16 + a2) }
  | _ => none

/-- A decimal number in thousandths, rounded half away from zero, read as path data reads one. -/
public def milli? (s : String) : Option Int := do
  let (d, rest) ← PathData.number s.toList
  unless rest.isEmpty do none
  let q : Nat := 10 ^ d.e
  let v : Nat := (d.m.natAbs * 1000 * 2 + q) / (2 * q)
  return if d.m < 0 then -(v : Int) else v

private def channel? (s : String) : Option UInt8 := do
  if s.endsWith "%" then
    let m ← milli? (s.dropEnd 1).toString
    let v := (m * 255 + 50000) / 100000
    some (byte (max 0 v).toNat)
  else
    let m ← milli? s
    let v := (m + 500) / 1000
    some (byte (max 0 v).toNat)

private def alpha? (s : String) : Option Nat := do
  if s.endsWith "%" then
    let m ← milli? (s.dropEnd 1).toString
    some (min 1000 (max 0 ((m + 50) / 100)).toNat)
  else
    let m ← milli? s
    some (min 1000 (max 0 m).toNat)

/-- `rgb(…)` or `rgba(…)`: three channels and an optional alpha, separated
by commas or spaces, the alpha after `/` in the space form. -/
public def rgb? (s : String) : Option Value := do
  let l := s.toLower
  let body ← if l.startsWith "rgba(" then some (l.drop 5).toString
    else if l.startsWith "rgb(" then some (l.drop 4).toString else none
  unless body.endsWith ")" do none
  let body := (body.dropEnd 1).toString
  let parts := ((body.replace "," " ").replace "/" " / ").splitOn " " |>.filter (!·.isEmpty)
  let parts := parts.filter (· != "/")
  match parts with
  | [r, g, b] =>
    some { color := { r := ← channel? r, g := ← channel? g, b := ← channel? b }, alpha := 1000 }
  | [r, g, b, a] =>
    some { color := { r := ← channel? r, g := ← channel? g, b := ← channel? b }, alpha := ← alpha? a }
  | _ => none

/-- A colour value, or `none` when the text is no colour this reader reads; `currentColor` is the caller's. -/
public def parse (s : String) : Option Value :=
  let t := s.trimAscii.toString
  if t.startsWith "#" then hex? t
  else if t.toLower.startsWith "rgb" then rgb? t
  else if t.toLower == "transparent" then some { color := { r := 0, g := 0, b := 0 }, alpha := 0 }
  else (named? t).map fun (r, g, b) =>
    { color := { r := r.toUInt8, g := g.toUInt8, b := b.toUInt8 }, alpha := 1000 }

end LeanTex.Core.CssColor
