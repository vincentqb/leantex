module

import LeanTex.Core.FaData
public import Std.Data.HashMap

namespace LeanTex.Core.FaIcons

/-- One Font Awesome icon: its fontawesome5 command (empty when none), name, Private Use Area
scalar, and accessible name as its default text alternative. -/
public structure Entry where
  macroName : String
  name : String
  scalar : Char
  label : String
  deriving Repr, BEq, Inhabited

private def parseHex (s : String) : Nat :=
  s.foldl (fun n c =>
    let d :=
      if c.isDigit then c.toNat - '0'.toNat
      else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
      else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else 0
    n * 16 + d) 0

private def parseLine (line : String) : Option Entry :=
  match line.splitOn "|" with
  | [m, name, hex, label] =>
    let n := parseHex hex
    if h : Nat.isValidChar n then
      some { macroName := m, name, scalar := Char.ofNatAux n h, label }
    else
      none
  | _ => none

/-- The generated table, parsed on first use; a line that does not parse is skipped. -/
private def entries : Thunk (Array Entry) := Thunk.mk fun _ =>
  FaData.table.splitOn "\n" |>.toArray |>.filterMap parseLine

private def index (key : Entry → String) : Std.HashMap String Entry :=
  entries.get.foldl (fun m e =>
    let k := key e
    if k.isEmpty || m.contains k then m else m.insert k e) {}

/-- `\faGithub` → its entry: lookup by the fontawesome5 command name. -/
public def byMacro : Thunk (Std.HashMap String Entry) := Thunk.mk fun _ =>
  index (·.macroName)

/-- `\faIcon{github}` → its entry: lookup by the icon's own name. -/
public def byName : Thunk (Std.HashMap String Entry) := Thunk.mk fun _ =>
  index (·.name)

end LeanTex.Core.FaIcons
