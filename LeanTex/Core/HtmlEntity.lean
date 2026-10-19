module

import Std.Data.HashMap
import LeanTex.Core.HtmlEntityData
import LeanTex.Core.Hex

/-! The HTML Standard's named character references (§13.5) that end in `;`, over the generated
`HtmlEntityData`. -/

namespace LeanTex.Core.HtmlEntity

open Std

/-- One table line's name and characters, or `none` for a line of another shape. -/
private def row (line : String) : Option (String × String) := do
  let [name, cps] := line.splitOn " " | none
  let mut out := ""
  for cp in cps.splitOn "+" do
    if cp.isEmpty then none
    let v := cp.foldl (fun acc c => acc * 16 + (Hex.val? c.toNat).getD 0) 0
    out := out.push (Char.ofNat v)
  return (name, out)

private def load (_ : Unit) : HashMap String String := Id.run do
  let mut out : HashMap String String := {}
  for line in HtmlEntityData.table.splitOn "\n" do
    if let some (n, v) := row line then out := out.insert n v
  return out

/-- The table, built once per process on first use; `load` takes `Unit` to defer the cost. -/
private def table : Thunk (HashMap String String) := Thunk.mk load

/-- The characters `&name;` names, `name` without `&` and `;`, read case-sensitively. -/
public def lookup (name : String) : Option String := table.get[name]?

/-- How many names the table holds. -/
public def size (_ : Unit) : Nat := table.get.size

end LeanTex.Core.HtmlEntity
