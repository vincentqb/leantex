/-
Regenerate LeanTex/Core/FaData.lean from the fontawesome5 LaTeX package's
mapping table and Font Awesome's own icon metadata. Run with:

  lake env lean --run scripts/gen-fa-data.lean <fontawesome5-mapping.def> <icons.json>

Sources (both fetched, never vendored):
- fontawesome5-mapping.def from CTAN (fonts/fontawesome5/tex/, v5.15.4,
  LPPL 1.3c): each `\__fontawesome_def_icon:nnnnn{\faMacro}{name}{font}{slot}{"HEX}`
  line is the package's own LaTeX-command-to-codepoint mapping — the
  authority for what `\faGithub` means.
- metadata/icons.json from the FortAwesome/Font-Awesome repository
  (5.x branch, CC BY 4.0 for metadata): the `label` field is Font Awesome's
  curated human name per icon, used as the icon's default text alternative.
-/
import Lean.Data.Json

open Lean

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

def notice : String := "/-
Generated from fontawesome5-mapping.def (CTAN, fontawesome5 5.15.4, LPPL
1.3c; the Font Awesome 5 Free fonts it maps are SIL OFL 1.1) and
metadata/icons.json (FortAwesome/Font-Awesome, 5.x branch, CC BY 4.0);
do not edit by hand. Regenerate with:
  lake env lean --run scripts/gen-fa-data.lean <mapping.def> <icons.json>

One entry per line: macro|name|hex-codepoint|label. `macro` is the LaTeX
command without its backslash (empty when fontawesome5 defines no
single-command spelling and the icon is reachable only as \\faIcon{name});
`label` is Font Awesome's own accessible name for the icon.
-/
"

/-- One `\__fontawesome_def_icon:nnnnn{\faMacro}{name}{font}{slot}{"HEX}` line's
five brace groups, or none for any other line. -/
def defIconArgs (line : String) : Option (List String) := Id.run do
  unless line.startsWith "\\__fontawesome_def_icon:nnnnn" do return none
  let mut groups : List String := []
  let mut cur := ""
  let mut depth := 0
  for c in line.toList do
    if c == '{' then
      if depth == 0 then cur := "" else cur := cur.push c
      depth := depth + 1
    else if c == '}' then
      depth := depth - 1
      if depth == 0 then groups := groups ++ [cur] else cur := cur.push c
    else if depth > 0 then
      cur := cur.push c
  if groups.length == 5 then return some groups else return none

def main (args : List String) : IO UInt32 := do
  let [mappingPath, jsonPath] := args
    | die "usage: gen-fa-data.lean <fontawesome5-mapping.def> <icons.json>"
  let mapping ← IO.FS.readFile mappingPath
  let jsonText ← IO.FS.readFile jsonPath
  let json ← match Json.parse jsonText with
    | .ok j => pure j
    | .error e => die s!"icons.json: {e}"
  let labelOf (name : String) : Option String := do
    let entry ← (json.getObjVal? name).toOption
    (entry.getObjValAs? String "label").toOption
  let mut lines : Array String := #[]
  let mut seen : Array String := #[]
  for line in mapping.splitOn "\n" do
    let some [macroArg, name, _font, _slot, hex] := defIconArgs line.trimAscii.toString
      | continue
    let macroName := if macroArg.startsWith "\\" then (macroArg.drop 1).toString else macroArg
    let hex := if hex.startsWith "\"" then (hex.drop 1).toString else hex
    if seen.contains name then continue
    seen := seen.push name
    let label := (labelOf name).getD name
    if label.contains '|' || label.contains '\n' then
      die s!"label for {name} carries a delimiter: {label.quote}"
    lines := lines.push s!"{macroName}|{name}|{hex}|{label}"
  let body := String.intercalate "\n" lines.toList
  let content := "module\n\n" ++ notice
    ++ "namespace LeanTex.Core.FaData\n\n"
    ++ "public def table : String :=\n  \""
    ++ ((body.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" "\\n"
    ++ "\"\n\nend LeanTex.Core.FaData\n"
  IO.FS.writeFile "LeanTex/Core/FaData.lean" content
  IO.println s!"wrote LeanTex/Core/FaData.lean: {lines.size} icons"
  return 0
