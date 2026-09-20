import LeanTex.Core.FaData
import Std.Data.HashMap

namespace LeanTex.Core.FaIcons

/-- One Font Awesome icon: the fontawesome5 LaTeX command (without its
backslash; empty when the package defines no single-command spelling), the
icon's own name (`\faIcon{name}`), its scalar in the Private Use Area, and
Font Awesome's accessible name for it — the icon's default text
alternative (WCAG 2.2 SC 1.1.1 wants one, and PUA scalars carry no meaning
of their own for assistive technology). -/
structure Entry where
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

/-- The table, parsed on first use (`Thunk` is call-by-need: a top-level
constant is computed at process start, and parsing the 58 KB generated
table there taxed every run whether or not it set an icon — the same trap
the Hyphen/Nfc tables already close). Generated data (`FaData.table`), so
a line that does not parse is a generator bug; it is skipped rather than
trusted. -/
def entries : Thunk (Array Entry) := Thunk.mk fun _ =>
  FaData.table.splitOn "\n" |>.toArray |>.filterMap parseLine

private def index (key : Entry → String) : Std.HashMap String Entry :=
  entries.get.foldl (fun m e =>
    let k := key e
    if k.isEmpty || m.contains k then m else m.insert k e) {}

/-- `\faGithub` → its entry: lookup by the fontawesome5 command name. -/
def byMacro : Thunk (Std.HashMap String Entry) := Thunk.mk fun _ =>
  index (·.macroName)

/-- `\faIcon{github}` → its entry: lookup by the icon's own name. -/
def byName : Thunk (Std.HashMap String Entry) := Thunk.mk fun _ =>
  index (·.name)

end LeanTex.Core.FaIcons
