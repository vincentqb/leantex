module

public import LeanTex.Core.Diag
import LeanTex.Core.Elab

namespace LeanTex.Core.ThemeImport

open LeanTex.Core.Ir

/-- A theme file both engines read: one `\palette` of hexadecimal colours under its source's name. -/
public def themeFile (source : String) (entries : Array (String × String)) : String :=
  s!"% A leantex theme imported from {source}.\n\\palette\{\n" ++
    ",\n".intercalate (entries.toList.map fun (k, v) => s!"  {k} = {v}") ++ "\n}\n"

/-- A beamer document around a colour theme's source. -/
private def beamerDoc (src : String) : String :=
  "\\documentclass{beamer}\n\\makeatletter\n" ++ src ++
    "\n\\makeatother\n\\begin{document}\n\\end{document}\n"

/-- A beamer colour theme's palette, its `\setbeamercolor`s read as a beamer document's are: each
role key the source sets, past beamer's own, and what the reading reported. -/
public def ofBeamer (file src : String) : Array (String × String) × Array Diag :=
  let (base, _) := Elab.run file (beamerDoc "")
  let (d, ds) := Elab.run file (beamerDoc src)
  let set := d.palette.entries.filter fun (k, c) =>
    (Role.ofKey? k.key).isSome && !base.palette.entries.contains (k, c)
  (set.map fun (k, c) => (k.key, c.hex), ds)

/-- A hexadecimal colour as both engines read it, six digits upper case; `none` for another value. -/
public def hexColor? (v : String) : Option String :=
  let digits := (v.drop 1).toString.toUpper
  if !v.startsWith "#" || !digits.all Char.isHexDigit then none
  else if digits.length == 6 then some ("#" ++ digits)
  else if digits.length == 3 then some ("#" ++ String.ofList (digits.toList.flatMap fun c => [c, c]))
  else none

/-- Why a custom property gave no palette colour. -/
public inductive Skip where
  | unmapped (name : String)
  | notHex (name value : String)
  | outside (name selector : String)
  deriving Repr, BEq

/-- A stylesheet with its comments taken out. -/
private def uncommented (src : String) : String := Id.run do
  let mut out : Array Char := #[]
  let mut inComment := false
  let mut prev := ' '
  for c in src.toList do
    if inComment then
      if prev == '*' && c == '/' then
        inComment := false
        prev := ' '
      else prev := c
    else if prev == '/' && c == '*' then
      out := out.pop
      inComment := true
      prev := ' '
    else
      out := out.push c
      prev := c
  return String.ofList out.toList

/-- A stylesheet's custom properties as palette keys: `--ltx-<key>` directly, another through its
`--map name=key`, each a hexadecimal colour of a top-level `:root` rule; with each one skipped. -/
public def ofCss (src : String) (maps : List (String × String)) : Array (String × String) × Array Skip :=
  Id.run do
  let mut out : Array (String × String) := #[]
  let mut skipped : Array Skip := #[]
  -- The open rules' selectors, innermost last, and the text since the last delimiter.
  let mut open_ : Array String := #[]
  let mut text := ""
  for c in (uncommented src).toList do
    if c == '{' then
      open_ := open_.push text.trimAscii.toString
      text := ""
    else if c == ';' || c == '}' then
      let decl := text.trimAscii.toString
      text := ""
      if decl.startsWith "--" then
        match decl.splitOn ":" with
        | name :: rest =>
          let name := (name.drop 2).trimAscii.toString
          let value := (":".intercalate rest).trimAscii.toString
          let selector := open_.back?.getD ""
          let key := if name.startsWith "ltx-" then some (name.drop 4).toString else maps.lookup name
          match key with
          | none => skipped := skipped.push (.unmapped name)
          | some k =>
            if open_.size != 1 || selector != ":root" then
              skipped := skipped.push (.outside name (" ".intercalate open_.toList))
            else
              match hexColor? value with
              | some v => out := (out.filter (·.1 != k)).push (k, v)
              | none => skipped := skipped.push (.notHex name value)
        | [] => pure ()
      if c == '}' then open_ := open_.pop
    else text := text.push c
  return (out, skipped)

/-- A skipped property as the command line names it. -/
public def Skip.describe : Skip → String
  | .unmapped n => s!"--{n} names no palette key; add --map {n}=<key>"
  | .notHex n v => s!"--{n}: '{v}' is not a hexadecimal colour"
  | .outside n s => s!"--{n} stands in '{s}', not a top-level :root rule"

end LeanTex.Core.ThemeImport
