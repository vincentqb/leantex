module

import Std.Data.HashMap
import LeanTex.Core.CaseFoldData
import LeanTex.Core.Hex

/-! Unicode full case folding, CaseFolding.txt's common and full mappings, from the generated
`CaseFoldData`. -/

namespace LeanTex.Core.CaseFold

open Std

private def load (_ : Unit) : HashMap UInt32 (Array Char) := Id.run do
  let bs := CaseFoldData.fold.toUTF8
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

/-- The table, built once per process on first use; `load` takes `Unit` to defer the cost. -/
private def table : Thunk (HashMap UInt32 (Array Char)) := Thunk.mk load

/-- The characters `c` folds to. -/
public def foldChar (c : Char) : Array Char :=
  if c.toNat < 0x80 then #[c.toLower] else (table.get.get? c.val).getD #[c]

/-- A text folded character by character. -/
public def fold (s : String) : String :=
  s.foldl (fun acc c => (foldChar c).foldl String.push acc) ""

end LeanTex.Core.CaseFold
