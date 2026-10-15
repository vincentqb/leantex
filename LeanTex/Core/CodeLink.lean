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

/-- The parts a link template may name, in the order a declaration fills them: its name, module,
file path, first and last lines, and the file's commit. -/
public def templateParts : List String :=
  ["{name}", "{module}", "{path}", "{line}", "{endline}", "{commit}"]

/-- A link written as a GitHub repository's root, `https://github.com/OWNER/REPO` with or without
`.git` or a last `/`, reaches each declaration's lines at the commit the file stands at; any other
link is a template. -/
public def linkTemplate (link : String) : String :=
  let plain (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '.'
  let body := if link.startsWith "https://github.com/" then some (link.drop 19).toString
    else if link.startsWith "http://github.com/" then some (link.drop 18).toString else none
  match body.map fun b => (if b.endsWith "/" then (b.dropEnd 1).toString else b).splitOn "/" with
  | some [owner, repo] =>
    let repo := if repo.endsWith ".git" then (repo.dropEnd 4).toString else repo
    if !owner.isEmpty && !repo.isEmpty && owner.all plain && repo.all plain then
      s!"https://github.com/{owner}/{repo}/blob/\{commit}/\{path}#L\{line}-L\{endline}"
    else link
  | _ => link

/-- A link for a declaration known by its name alone: the template's `{name}` filled, none where
the template names a part only a Lean file's facts or its repository give. -/
public def expandName (link name : String) : Option String :=
  expandParts (linkTemplate link)
    (templateParts.map fun p => (p, if p == "{name}" then some (urlPart false name) else none))

end LeanTex.Core.Code
