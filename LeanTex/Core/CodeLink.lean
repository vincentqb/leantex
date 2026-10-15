module

import LeanTex.Core.Hex

/-! A link template's parts, filled as a URL carries them: shared by a Lean file's statements and a
blueprint's declaration names. -/

namespace LeanTex.Core.Code

/-- A link part as a URL carries it: each character but an unreserved one, and `/` in a path, as
its UTF-8 bytes in percent escapes. -/
public def urlPart (path : Bool) (s : String) : String :=
  s.foldl (fun acc c =>
    if (c.isAlphanum && c.toNat < 128) || c == '-' || c == '.' || c == '_' || c == '~' ||
        (path && c == '/') then acc.push c
    else (String.singleton c).toUTF8.foldl (fun out b =>
      let pair := Hex.byte true b
      out.push '%' ++ pair) acc) ""

/-- A template with each part it names filled, none where a part it names has no value. -/
public def expandParts (template : String) (parts : List (String × Option String)) :
    Option String :=
  parts.foldlM (fun (acc : String) (key, value) =>
    if (acc.splitOn key).length > 1 then value.map (acc.replace key ·) else some acc) template

end LeanTex.Core.Code
