module

import Std.Data.HashMap
import LeanTex.Core.CaseFoldData
import LeanTex.Core.CaseUpperData
import LeanTex.Core.Hex

/-! Unicode full case folding, CaseFolding.txt's common and full mappings, from the generated
`CaseFoldData`, and the full uppercase mapping from the generated `CaseUpperData`. -/

namespace LeanTex.Core.CaseFold

open Std

private def load (table : String) : HashMap UInt32 (Array Char) := Id.run do
  let bs := table.toUTF8
  let mut out : HashMap UInt32 (Array Char) := {}
  let mut p := 0
  for _ in [0:bs.size + 1] do
    if p + 7 > bs.size then break
    let k := Hex.field bs (p + 6) 1
    let mut parts : Array Char := Array.mkEmpty k
    for j in [0:k] do
      parts := parts.push (Char.ofNat (Hex.field bs (p + 7 + j * 6) 6))
    out := out.insert (UInt32.ofNat (Hex.field bs p 6)) parts
    p := p + 7 + k * 6
  return out

/-- The folding table, built once per process on first use. -/
private def table : Thunk (HashMap UInt32 (Array Char)) :=
  Thunk.mk fun _ => load CaseFoldData.fold

/-- The uppercase table, built once per process on first use. -/
private def upperTable : Thunk (HashMap UInt32 (Array Char)) :=
  Thunk.mk fun _ => load CaseUpperData.upper

/-- The characters `c` folds to. -/
public def foldChar (c : Char) : Array Char :=
  if c.toNat < 0x80 then #[c.toLower] else (table.get.get? c.val).getD #[c]

/-- A text folded character by character. -/
public def fold (s : String) : String :=
  s.foldl (fun acc c => (foldChar c).foldl String.push acc) ""

/-- The characters `c` maps to in upper case, untailored to a language. -/
public def upperChar (c : Char) : Array Char :=
  if c.toNat < 0x80 then #[c.toUpper] else (upperTable.get.get? c.val).getD #[c]

/-- A text in upper case, character by character. -/
public def upper (s : String) : String :=
  s.foldl (fun acc c => (upperChar c).foldl String.push acc) ""

end LeanTex.Core.CaseFold
